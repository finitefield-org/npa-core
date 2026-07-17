//! Implementation of `npa package validate-l2-namespace-transport`.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{verify_module_cert_hashes, DeclPayload, GlobalRef, ModuleCert, Name};
use npa_package::{
    format_package_hash, l2_transport_derived_mapping_hash, l2_transport_module_declaration_names,
    l2_transport_module_projection, l2_transport_module_projection_subset,
    l2_transport_normalized_closure_hash, package_file_hash, parse_l2_acceptance_policy_json,
    parse_l2_acceptance_v2_json, parse_l2_namespace_transport_policy_json,
    parse_l2_namespace_transport_request_json, parse_package_axiom_report_json,
    parse_package_theorem_index_json, L2NamespaceTransportAttestation,
    L2TransportAttestationChangedPath, L2TransportAttestationModulePair,
    L2TransportAttestationTheoremPair, L2TransportModuleRole, PackageHash, PackagePath,
    PackageTheoremIndex,
};

use crate::{
    args::PackageL2NamespaceTransportOptions,
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_path,
    governance_writer::{
        confined_governance_path, write_governance_artifact, GovernanceOutputPolicy,
    },
    package::load_package_root,
    package_artifacts::{
        load_package_audit_snapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
        PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH,
    },
    package_l2_acceptance_aggregate::validate_l2_acceptance_v2_current,
};

const COMMAND: &str = "package validate-l2-namespace-transport";

struct TransportAuditSnapshot {
    theorem_index: PackageTheoremIndex,
    lock_file_hash: PackageHash,
    axiom_report_file_hash: PackageHash,
    theorem_index_file_hash: PackageHash,
    checker_identities: Vec<String>,
    files: BTreeMap<PackagePath, Option<Vec<u8>>>,
}

impl TransportAuditSnapshot {
    fn capture_missing(
        &mut self,
        root: &std::path::Path,
        paths: &BTreeSet<PackagePath>,
        reason: &str,
    ) -> Result<(), Box<CommandDiagnostic>> {
        for path in paths {
            if self.files.contains_key(path) {
                continue;
            }
            let full = confined_governance_path(root, path, path.as_str(), reason)?;
            let bytes = match fs::read(full) {
                Ok(bytes) => Some(bytes),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
                Err(_) => return Err(diagnostic(reason, path.as_str())),
            };
            self.files.insert(path.clone(), bytes);
        }
        Ok(())
    }

    fn bytes(&self, path: &PackagePath, reason: &str) -> Result<&[u8], Box<CommandDiagnostic>> {
        self.files
            .get(path)
            .and_then(Option::as_deref)
            .ok_or_else(|| diagnostic(reason, path.as_str()))
    }

    fn optional_bytes(&self, path: &PackagePath) -> Option<&[u8]> {
        self.files.get(path).and_then(Option::as_deref)
    }
}

struct LoadedTransportCertificate {
    cert: ModuleCert,
    file_hash: PackageHash,
}

struct TransportValidationPackages<'a> {
    source_root: &'a crate::package::LoadedPackageRoot,
    baseline_root: &'a crate::package::LoadedPackageRoot,
    target_root: &'a crate::package::LoadedPackageRoot,
    source_snapshot: &'a TransportAuditSnapshot,
    baseline_snapshot: &'a TransportAuditSnapshot,
    target_snapshot: &'a TransportAuditSnapshot,
}

#[derive(Default)]
struct DeclarationClosure {
    declarations: BTreeMap<Name, BTreeSet<usize>>,
    required_imports: BTreeMap<Name, BTreeSet<Name>>,
}

impl DeclarationClosure {
    fn modules(&self) -> BTreeSet<Name> {
        self.declarations.keys().cloned().collect()
    }
}

/// Validate a source-free, canonical-certificate namespace-only transport.
pub fn run_package_validate_l2_namespace_transport(
    options: PackageL2NamespaceTransportOptions,
) -> CommandResult {
    let source = match load_package_root(&options.common.root, COMMAND) {
        Ok(value) => value,
        Err(result) => return result,
    };
    let root_display = source.root_display.clone();
    let result = validate_transport(&source, &options);
    let (attestation, hash) = match result {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    if let Some(out) = &options.out {
        let path = PackagePath::new(out.to_string_lossy());
        let full = match confined_governance_path(
            &source.root,
            &path,
            "--out",
            "l2_transport_output_not_package_relative",
        ) {
            Ok(path) => path,
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        };
        if options.check {
            if fs::read(full).ok().as_deref() != Some(attestation.as_bytes()) {
                return CommandResult::failed(
                    COMMAND,
                    root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::GeneratedArtifact,
                        "l2_transport_output_stale",
                    )
                    .with_path(render_package_path(&path))],
                );
            }
        } else if let Err(diagnostic) = write_governance_artifact(
            &source.root,
            &path,
            attestation.as_bytes(),
            GovernanceOutputPolicy::CreateOrIdentical,
            "l2_transport",
        ) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    if let Some(out) = options.out {
        result.artifacts.push(CommandArtifact {
            kind: "l2_namespace_transport_attestation".to_owned(),
            path: out.to_string_lossy().into_owned(),
        });
    }
    result.diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::PackagePolicy,
            "l2_namespace_transport_validated",
        )
        .with_actual_value(format_package_hash(&hash)),
    );
    result
}

fn validate_transport(
    source: &crate::package::LoadedPackageRoot,
    options: &PackageL2NamespaceTransportOptions,
) -> Result<(String, npa_package::PackageHash), Box<CommandDiagnostic>> {
    let baseline = load_package_root(&options.target_baseline_root, COMMAND)
        .map_err(|_| diagnostic("l2_transport_baseline_invalid", "--target-baseline-root"))?;
    let target = load_package_root(&options.target_root, COMMAND)
        .map_err(|_| diagnostic("l2_transport_target_invalid", "--target-root"))?;
    let baseline_real = fs::canonicalize(&baseline.root)
        .map_err(|_| diagnostic("l2_transport_baseline_invalid", "--target-baseline-root"))?;
    let target_real = fs::canonicalize(&target.root)
        .map_err(|_| diagnostic("l2_transport_target_invalid", "--target-root"))?;
    if baseline_real == target_real {
        return Err(diagnostic("l2_transport_target_alias", "--target-root"));
    }
    let acceptance_policy_bytes = fs::read(&options.acceptance_policy)
        .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--acceptance-policy"))?;
    let acceptance_policy = parse_l2_acceptance_policy_json(
        std::str::from_utf8(&acceptance_policy_bytes)
            .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--acceptance-policy"))?,
    )
    .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--acceptance-policy"))?;
    if acceptance_policy.policy_version != 2 {
        return Err(diagnostic(
            "l2_transport_policy_mismatch",
            "--acceptance-policy",
        ));
    }
    let transport_policy_bytes = fs::read(&options.transport_policy)
        .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--transport-policy"))?;
    let transport_policy = parse_l2_namespace_transport_policy_json(
        std::str::from_utf8(&transport_policy_bytes)
            .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--transport-policy"))?,
    )
    .map_err(|_| diagnostic("l2_transport_policy_mismatch", "--transport-policy"))?;
    if transport_policy.source_acceptance_policy_id != acceptance_policy.policy_id
        || transport_policy.source_acceptance_policy_version != acceptance_policy.policy_version
        || transport_policy.source_acceptance_policy_file_hash
            != package_file_hash(&acceptance_policy_bytes)
        || transport_policy.target_package != target.validated.manifest().package
    {
        return Err(diagnostic(
            "l2_transport_policy_mismatch",
            "--transport-policy",
        ));
    }
    let mapping_path = PackagePath::new(options.mapping.to_string_lossy());
    let mapping_bytes = read_package(
        &source.root,
        &mapping_path,
        "l2_transport_mapping_noncanonical",
    )?;
    let request = parse_l2_namespace_transport_request_json(
        std::str::from_utf8(&mapping_bytes)
            .map_err(|_| diagnostic("l2_transport_mapping_noncanonical", mapping_path.as_str()))?,
    )
    .map_err(|_| diagnostic("l2_transport_mapping_noncanonical", mapping_path.as_str()))?;
    let source_manifest = source.validated.manifest();
    let baseline_manifest = baseline.validated.manifest();
    let target_manifest = target.validated.manifest();
    if request.source.package != source_manifest.package
        || request.source.version != source_manifest.version
        || request.target.package != target_manifest.package
        || request.target.version != target_manifest.version
        || baseline_manifest.package != target_manifest.package
    {
        return Err(diagnostic(
            "l2_transport_mapping_incomplete",
            mapping_path.as_str(),
        ));
    }
    for mapping in &request.module_mappings {
        if !transport_policy
            .allowed_source_prefixes
            .iter()
            .any(|prefix| mapping.source.module.as_dotted().starts_with(prefix))
        {
            return Err(diagnostic(
                "l2_transport_source_prefix_denied",
                &mapping.source.module.as_dotted(),
            ));
        }
        if !transport_policy
            .allowed_target_prefixes
            .iter()
            .any(|prefix| mapping.target.module.as_dotted().starts_with(prefix))
        {
            return Err(diagnostic(
                "l2_transport_target_prefix_denied",
                &mapping.target.module.as_dotted(),
            ));
        }
    }

    let acceptance_path = PackagePath::new(options.source_acceptance.to_string_lossy());
    let acceptance_bytes = read_package(
        &source.root,
        &acceptance_path,
        "l2_transport_source_acceptance_failed",
    )?;
    let acceptance =
        parse_l2_acceptance_v2_json(std::str::from_utf8(&acceptance_bytes).map_err(|_| {
            diagnostic(
                "l2_transport_source_acceptance_failed",
                acceptance_path.as_str(),
            )
        })?)
        .map_err(|_| {
            diagnostic(
                "l2_transport_source_acceptance_failed",
                acceptance_path.as_str(),
            )
        })?;
    validate_l2_acceptance_v2_current(
        source,
        &acceptance,
        &acceptance_policy,
        package_file_hash(&acceptance_policy_bytes),
    )
    .map_err(|_| {
        diagnostic(
            "l2_transport_source_acceptance_failed",
            acceptance_path.as_str(),
        )
    })?;

    let source_audit = load_transport_audit_snapshot(source)?;
    let source_index = &source_audit.theorem_index;
    for entry in &acceptance.entries {
        let current = source_index.entries.iter().find(|current| {
            current.global_ref.module == entry.module
                && current.global_ref.name == entry.theorem
                && current.kind == npa_package::PackageTheoremIndexKind::Theorem
                && current.artifact.origin == npa_package::PackageArtifactOrigin::Local
        });
        if current.is_none_or(|current| {
            current.statement.core_hash != entry.statement_hash
                || current.global_ref.certificate_hash != entry.certificate_hash
        }) {
            return Err(diagnostic(
                "l2_transport_source_acceptance_failed",
                &entry.module.as_dotted(),
            ));
        }
    }
    for mapping in request
        .module_mappings
        .iter()
        .filter(|mapping| mapping.role == L2TransportModuleRole::Selected)
    {
        for theorem in source_index.entries.iter().filter(|entry| {
            entry.global_ref.module == mapping.source.module
                && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
                && entry.artifact.origin == npa_package::PackageArtifactOrigin::Local
        }) {
            if !acceptance.entries.iter().any(|entry| {
                entry.module == mapping.source.module && entry.theorem == theorem.global_ref.name
            }) {
                return Err(diagnostic(
                    "l2_transport_source_acceptance_failed",
                    &mapping.source.module.as_dotted(),
                ));
            }
        }
    }

    let mut baseline_audit = load_transport_audit_snapshot(&baseline)?;
    let mut target_audit = load_transport_audit_snapshot(&target)?;
    let mut target_inventory = package_snapshot_inventory(baseline_manifest);
    target_inventory.extend(package_snapshot_inventory(target_manifest));
    baseline_audit.capture_missing(
        &baseline.root,
        &target_inventory,
        "l2_transport_baseline_invalid",
    )?;
    target_audit.capture_missing(
        &target.root,
        &target_inventory,
        "l2_transport_target_verification_failed",
    )?;
    let source_certificates = package_certificates(
        source,
        &source_audit,
        "l2_transport_source_verification_failed",
    )?;
    let target_certificates = package_certificates(
        &target,
        &target_audit,
        "l2_transport_target_verification_failed",
    )?;
    let source_roots = request
        .module_mappings
        .iter()
        .filter(|mapping| mapping.role == L2TransportModuleRole::Selected)
        .map(|mapping| mapping.source.module.clone());
    let target_roots = request
        .module_mappings
        .iter()
        .filter(|mapping| mapping.role == L2TransportModuleRole::Selected)
        .map(|mapping| mapping.target.module.clone());
    let source_closure = declaration_closure(&source_certificates, source_roots)?;
    let target_closure = declaration_closure(&target_certificates, target_roots)?;
    let source_reachable = source_closure.modules();
    let target_reachable = target_closure.modules();
    let changed_paths = validate_target_baseline(
        &request,
        &transport_policy,
        &TransportValidationPackages {
            source_root: source,
            baseline_root: &baseline,
            target_root: &target,
            source_snapshot: &source_audit,
            baseline_snapshot: &baseline_audit,
            target_snapshot: &target_audit,
        },
        &source_reachable,
        &target_reachable,
    )?;

    let mut closure_rows = Vec::new();
    let mut module_rows = Vec::new();
    for mapping in &request.module_mappings {
        let source_certificate_hash = match mapping.source.origin {
            npa_package::PackageArtifactOrigin::Local => {
                let module = source_manifest
                    .modules
                    .iter()
                    .find(|module| module.module == mapping.source.module)
                    .ok_or_else(|| {
                        diagnostic(
                            "l2_transport_declaration_missing",
                            &mapping.source.module.as_dotted(),
                        )
                    })?;
                module.expected_certificate_hash
            }
            npa_package::PackageArtifactOrigin::External => {
                let import = source_manifest
                    .imports
                    .as_deref()
                    .unwrap_or_default()
                    .iter()
                    .find(|import| {
                        import.module == mapping.source.module
                            && import.package == mapping.source.package
                            && import.version == mapping.source.version
                    })
                    .ok_or_else(|| {
                        diagnostic(
                            "l2_transport_declaration_missing",
                            &mapping.source.module.as_dotted(),
                        )
                    })?;
                import.certificate_hash
            }
        };
        let target_module = target_manifest
            .modules
            .iter()
            .find(|module| module.module == mapping.target.module)
            .ok_or_else(|| {
                diagnostic(
                    "l2_transport_declaration_missing",
                    &mapping.target.module.as_dotted(),
                )
            })?;
        let source_loaded = source_certificates
            .get(&mapping.source.module)
            .ok_or_else(|| {
                diagnostic(
                    "l2_transport_declaration_missing",
                    &mapping.source.module.as_dotted(),
                )
            })?;
        let target_loaded = target_certificates
            .get(&mapping.target.module)
            .ok_or_else(|| {
                diagnostic(
                    "l2_transport_declaration_missing",
                    &mapping.target.module.as_dotted(),
                )
            })?;
        let source_cert = &source_loaded.cert;
        let target_cert = &target_loaded.cert;
        for target_import in &target_cert.imports {
            let target_name = target_import.module.as_dotted();
            if transport_policy
                .allowed_source_prefixes
                .iter()
                .any(|prefix| target_name.starts_with(prefix))
            {
                return Err(diagnostic(
                    "l2_transport_source_namespace_leak",
                    &target_name,
                ));
            }
        }
        for source_import in &source_cert.imports {
            if !source_closure
                .required_imports
                .get(&mapping.source.module)
                .is_some_and(|imports| imports.contains(&source_import.module))
            {
                continue;
            }
            let mapped = request
                .module_mappings
                .iter()
                .any(|candidate| candidate.source.module == source_import.module);
            let source_name = source_import.module.as_dotted();
            if !mapped
                && transport_policy
                    .allowed_source_prefixes
                    .iter()
                    .any(|prefix| source_name.starts_with(prefix))
            {
                return Err(diagnostic(
                    "l2_transport_source_namespace_leak",
                    &source_name,
                ));
            }
            if !mapped
                && !target_cert
                    .imports
                    .iter()
                    .any(|target_import| target_import == source_import)
            {
                return Err(diagnostic(
                    "l2_transport_import_mismatch",
                    &source_import.module.as_dotted(),
                ));
            }
        }
        let mapped_names = l2_transport_module_declaration_names(source_cert, &request, true)
            .map_err(|_| {
                diagnostic(
                    "l2_transport_mapping_incomplete",
                    &mapping.source.module.as_dotted(),
                )
            })?;
        let target_names = l2_transport_module_declaration_names(target_cert, &request, false)
            .map_err(|_| {
                diagnostic(
                    "l2_transport_mapping_incomplete",
                    &mapping.target.module.as_dotted(),
                )
            })?;
        let required_names = required_projection_names(
            source_cert,
            &request,
            &mapping.source.module,
            &source_closure,
        )?;
        let source_owners = declaration_owner_indices(source_cert)?;
        let required_indices = source_closure
            .declarations
            .get(&mapping.source.module)
            .ok_or_else(|| {
                diagnostic(
                    "l2_transport_mapping_incomplete",
                    &mapping.source.module.as_dotted(),
                )
            })?;
        if (mapping.role == L2TransportModuleRole::Selected
            && !mapped_names.is_subset(&target_names))
            || !required_names.is_subset(&target_names)
            || has_invalid_explicit_rename(
                &mapping.renames,
                &source_owners,
                required_indices,
                &target_names,
            )
        {
            return Err(diagnostic(
                "l2_transport_mapping_incomplete",
                &mapping.source.module.as_dotted(),
            ));
        }
        let (left, right) = if mapping.role == L2TransportModuleRole::Selected {
            (
                l2_transport_module_projection(source_cert, &request, true),
                l2_transport_module_projection(target_cert, &request, false),
            )
        } else {
            (
                l2_transport_module_projection_subset(source_cert, &request, true, &required_names),
                l2_transport_module_projection_subset(
                    target_cert,
                    &request,
                    false,
                    &required_names,
                ),
            )
        };
        let left = left.map_err(|_| {
            diagnostic(
                "l2_transport_type_mismatch",
                &mapping.source.module.as_dotted(),
            )
        })?;
        let right = right.map_err(|_| {
            diagnostic(
                "l2_transport_type_mismatch",
                &mapping.target.module.as_dotted(),
            )
        })?;
        if left != right {
            return Err(diagnostic(
                "l2_transport_body_mismatch",
                &mapping.source.module.as_dotted(),
            ));
        }
        closure_rows.push((mapping.target.module.clone(), left));
        let source_source_file_hash =
            if mapping.source.origin == npa_package::PackageArtifactOrigin::Local {
                let source_module = source_manifest
                    .modules
                    .iter()
                    .find(|module| module.module == mapping.source.module)
                    .ok_or_else(|| {
                        diagnostic(
                            "l2_transport_declaration_missing",
                            &mapping.source.module.as_dotted(),
                        )
                    })?;
                let source_bytes = source_audit.bytes(
                    &source_module.source,
                    "l2_transport_source_verification_failed",
                )?;
                let source_hash = package_file_hash(source_bytes);
                if source_hash != source_module.expected_source_hash {
                    return Err(diagnostic(
                        "l2_transport_source_verification_failed",
                        source_module.source.as_str(),
                    ));
                }
                Some(source_hash)
            } else {
                None
            };
        let target_source_bytes = target_audit.bytes(
            &target_module.source,
            "l2_transport_target_verification_failed",
        )?;
        let target_source_file_hash = package_file_hash(target_source_bytes);
        if target_source_file_hash != target_module.expected_source_hash {
            return Err(diagnostic(
                "l2_transport_target_verification_failed",
                target_module.source.as_str(),
            ));
        }
        module_rows.push(L2TransportAttestationModulePair {
            role: mapping.role,
            source_module: mapping.source.module.clone(),
            target_module: mapping.target.module.clone(),
            source_source_file_hash,
            target_source_file_hash,
            source_certificate_file_hash: source_loaded.file_hash,
            target_certificate_file_hash: target_loaded.file_hash,
            source_certificate_hash,
            target_certificate_hash: target_module.expected_certificate_hash,
            source_export_hash: npa_package::PackageHash::from(source_cert.hashes.export_hash),
            target_export_hash: npa_package::PackageHash::from(target_cert.hashes.export_hash),
            source_axiom_report_hash: npa_package::PackageHash::from(
                source_cert.hashes.axiom_report_hash,
            ),
            target_axiom_report_hash: npa_package::PackageHash::from(
                target_cert.hashes.axiom_report_hash,
            ),
        });
    }
    module_rows.sort_by(|left, right| {
        (&left.source_module, &left.target_module)
            .cmp(&(&right.source_module, &right.target_module))
    });
    let mut theorem_pairs = Vec::new();
    for mapping in request
        .module_mappings
        .iter()
        .filter(|mapping| mapping.role == L2TransportModuleRole::Selected)
    {
        for source_theorem in source_audit.theorem_index.entries.iter().filter(|entry| {
            entry.global_ref.module == mapping.source.module
                && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
                && entry.artifact.origin == npa_package::PackageArtifactOrigin::Local
        }) {
            let (target_module, target_name) = request
                .map_global(&mapping.source.module, &source_theorem.global_ref.name)
                .ok_or_else(|| {
                    diagnostic(
                        "l2_transport_mapping_incomplete",
                        &mapping.source.module.as_dotted(),
                    )
                })?;
            let target_theorem = target_audit
                .theorem_index
                .entries
                .iter()
                .find(|entry| {
                    entry.global_ref.module == target_module
                        && entry.global_ref.name == target_name
                        && entry.kind == npa_package::PackageTheoremIndexKind::Theorem
                        && entry.artifact.origin == npa_package::PackageArtifactOrigin::Local
                })
                .ok_or_else(|| {
                    diagnostic(
                        "l2_transport_declaration_missing",
                        &target_module.as_dotted(),
                    )
                })?;
            theorem_pairs.push(L2TransportAttestationTheoremPair {
                source_module: mapping.source.module.clone(),
                source_theorem: source_theorem.global_ref.name.clone(),
                source_statement_hash: source_theorem.statement.core_hash,
                target_module,
                target_theorem: target_name,
                target_statement_hash: target_theorem.statement.core_hash,
            });
        }
    }
    theorem_pairs.sort_by(|left, right| {
        (
            &left.source_module,
            &left.source_theorem,
            &left.target_module,
            &left.target_theorem,
        )
            .cmp(&(
                &right.source_module,
                &right.source_theorem,
                &right.target_module,
                &right.target_theorem,
            ))
    });
    closure_rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut closure = Vec::new();
    for (_, projection) in closure_rows {
        closure.extend_from_slice(&(projection.len() as u64).to_le_bytes());
        closure.extend_from_slice(&projection);
    }
    let closure_hash = l2_transport_normalized_closure_hash(&closure);
    let mapping_certificates = source_certificates
        .iter()
        .map(|(module, loaded)| (module.clone(), loaded.cert.clone()))
        .collect::<BTreeMap<_, _>>();
    let derived_mapping_hash =
        l2_transport_derived_mapping_hash(&request, &mapping_certificates)
            .map_err(|_| diagnostic("l2_transport_mapping_incomplete", mapping_path.as_str()))?;
    let attestation = L2NamespaceTransportAttestation {
        schema: "npa.l2_namespace_transport_attestation.v2".to_owned(),
        transport_policy_id: transport_policy.policy_id,
        transport_policy_version: transport_policy.policy_version,
        transport_policy_file_hash: package_file_hash(&transport_policy_bytes),
        acceptance_policy_id: acceptance_policy.policy_id,
        acceptance_policy_version: acceptance_policy.policy_version,
        acceptance_policy_file_hash: package_file_hash(&acceptance_policy_bytes),
        mapping_request_file_hash: package_file_hash(&mapping_bytes),
        source_acceptance_file_hash: package_file_hash(&acceptance_bytes),
        source_package: source_manifest.package.clone(),
        source_version: source_manifest.version.clone(),
        target_baseline_version: baseline_manifest.version.clone(),
        target_package: target_manifest.package.clone(),
        target_version: target_manifest.version.clone(),
        source_manifest_hash: package_file_hash(source.manifest_source.as_bytes()),
        target_baseline_manifest_hash: package_file_hash(baseline.manifest_source.as_bytes()),
        target_manifest_hash: package_file_hash(target.manifest_source.as_bytes()),
        source_lock_hash: source_audit.lock_file_hash,
        target_baseline_lock_hash: baseline_audit.lock_file_hash,
        target_lock_hash: target_audit.lock_file_hash,
        source_axiom_report_hash: source_audit.axiom_report_file_hash,
        target_baseline_axiom_report_hash: baseline_audit.axiom_report_file_hash,
        target_axiom_report_hash: target_audit.axiom_report_file_hash,
        source_theorem_index_hash: source_audit.theorem_index_file_hash,
        target_baseline_theorem_index_hash: baseline_audit.theorem_index_file_hash,
        target_theorem_index_hash: target_audit.theorem_index_file_hash,
        source_checker_identities: source_audit.checker_identities,
        target_baseline_checker_identities: baseline_audit.checker_identities,
        target_checker_identities: target_audit.checker_identities,
        changed_paths,
        module_pairs: module_rows,
        theorem_pairs,
        derived_mapping_hash,
        normalized_closure_hash: closure_hash,
        status: "accepted_namespace_transport".to_owned(),
        proof_evidence: false,
    }
    .canonical_json()
    .map_err(|_| diagnostic("l2_transport_output_write_failed", "--out"))?;
    let hash = package_file_hash(attestation.as_bytes());
    Ok((attestation, hash))
}

fn validate_target_baseline(
    request: &npa_package::L2NamespaceTransportRequest,
    transport_policy: &npa_package::L2NamespaceTransportPolicy,
    packages: &TransportValidationPackages<'_>,
    source_reachable: &BTreeSet<Name>,
    target_reachable: &BTreeSet<Name>,
) -> Result<Vec<L2TransportAttestationChangedPath>, Box<CommandDiagnostic>> {
    let TransportValidationPackages {
        source_root,
        baseline_root,
        target_root,
        source_snapshot,
        baseline_snapshot,
        target_snapshot,
    } = packages;
    let source = source_root.validated.manifest();
    let baseline = baseline_root.validated.manifest();
    let target = target_root.validated.manifest();
    let selected = request
        .module_mappings
        .iter()
        .filter(|mapping| mapping.role == L2TransportModuleRole::Selected)
        .map(|mapping| mapping.target.module.clone())
        .collect::<BTreeSet<_>>();
    for mapping in &request.module_mappings {
        let before = baseline
            .modules
            .iter()
            .find(|module| module.module == mapping.target.module);
        let after = target
            .modules
            .iter()
            .find(|module| module.module == mapping.target.module);
        match mapping.role {
            L2TransportModuleRole::Selected if before.is_some() => {
                return Err(diagnostic(
                    "l2_transport_selected_already_in_baseline",
                    &mapping.target.module.as_dotted(),
                ))
            }
            L2TransportModuleRole::Selected if after.is_none() => {
                return Err(diagnostic(
                    "l2_transport_declaration_missing",
                    &mapping.target.module.as_dotted(),
                ))
            }
            L2TransportModuleRole::Dependency if before.is_none() || before != after => {
                return Err(diagnostic(
                    "l2_transport_dependency_not_in_baseline",
                    &mapping.target.module.as_dotted(),
                ))
            }
            _ => {}
        }
    }
    for before in &baseline.modules {
        if target
            .modules
            .iter()
            .find(|module| module.module == before.module)
            != Some(before)
        {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                &before.module.as_dotted(),
            ));
        }
        let paths = [
            Some(&before.source),
            Some(&before.certificate),
            before.meta.as_ref(),
            before.replay.as_ref(),
        ];
        for path in paths.into_iter().flatten() {
            let baseline_bytes = baseline_snapshot.bytes(path, "l2_transport_baseline_invalid")?;
            let target_bytes =
                target_snapshot.bytes(path, "l2_transport_unscoped_target_change")?;
            if baseline_bytes != target_bytes {
                return Err(diagnostic(
                    "l2_transport_unscoped_target_change",
                    path.as_str(),
                ));
            }
        }
    }
    if let Some(imports) = &baseline.imports {
        for import in imports {
            let baseline_bytes =
                baseline_snapshot.bytes(&import.certificate, "l2_transport_baseline_invalid")?;
            let target_bytes = target_snapshot
                .bytes(&import.certificate, "l2_transport_unscoped_target_change")?;
            if baseline_bytes != target_bytes {
                return Err(diagnostic(
                    "l2_transport_unscoped_target_change",
                    import.certificate.as_str(),
                ));
            }
        }
    }
    let mapped_modules = request
        .module_mappings
        .iter()
        .map(|mapping| mapping.source.module.clone())
        .collect::<BTreeSet<_>>();
    let source_external_modules = source
        .imports
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|external| external.module.clone())
        .collect::<BTreeSet<_>>();
    let target_external_modules = target
        .imports
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|external| external.module.clone())
        .collect::<BTreeSet<_>>();
    let mapped_target_modules = request
        .module_mappings
        .iter()
        .map(|mapping| mapping.target.module.clone())
        .collect::<BTreeSet<_>>();
    if !mapped_modules.is_subset(source_reachable)
        || !mapped_target_modules.is_subset(target_reachable)
    {
        return Err(diagnostic(
            "l2_transport_mapping_incomplete",
            "module_mappings",
        ));
    }
    if let Some(module) = first_unmapped_source_namespace(
        source_reachable,
        &mapped_modules,
        &transport_policy.allowed_source_prefixes,
    ) {
        return Err(diagnostic(
            "l2_transport_source_namespace_leak",
            &module.as_dotted(),
        ));
    }
    if let Some(module) = first_unmapped_source_namespace(
        target_reachable,
        &BTreeSet::new(),
        &transport_policy.allowed_source_prefixes,
    ) {
        return Err(diagnostic(
            "l2_transport_source_namespace_leak",
            &module.as_dotted(),
        ));
    }
    let required_source_external_modules = required_unmapped_external_modules(
        source_reachable,
        &source_external_modules,
        &mapped_modules,
    );
    let required_target_external_modules = required_unmapped_external_modules(
        target_reachable,
        &target_external_modules,
        &BTreeSet::new(),
    );
    for module in &required_source_external_modules {
        if !required_target_external_modules.contains(module) {
            return Err(diagnostic(
                "l2_transport_import_mismatch",
                &module.as_dotted(),
            ));
        }
        let source_import = source
            .imports
            .as_deref()
            .unwrap_or_default()
            .iter()
            .find(|candidate| candidate.module == *module)
            .ok_or_else(|| diagnostic("l2_transport_import_mismatch", &module.as_dotted()))?;
        let target_import = target
            .imports
            .as_deref()
            .unwrap_or_default()
            .iter()
            .find(|candidate| candidate.module == *module)
            .ok_or_else(|| diagnostic("l2_transport_import_mismatch", &module.as_dotted()))?;
        if !same_external_import_identity(source_import, target_import) {
            return Err(diagnostic(
                "l2_transport_import_mismatch",
                &module.as_dotted(),
            ));
        }
    }
    let baseline_imports = baseline.imports.as_deref().unwrap_or_default();
    let target_imports = target.imports.as_deref().unwrap_or_default();
    for before in baseline_imports {
        if !target_imports.iter().any(|after| after == before) {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                &before.module.as_dotted(),
            ));
        }
    }
    for after in target_imports {
        if baseline_imports.iter().any(|before| before == after) {
            continue;
        }
        let Some(source_import) =
            source
                .imports
                .as_deref()
                .unwrap_or_default()
                .iter()
                .find(|candidate| {
                    candidate.module == after.module
                        && candidate.package == after.package
                        && candidate.version == after.version
                        && candidate.export_hash == after.export_hash
                        && candidate.certificate_hash == after.certificate_hash
                })
        else {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                &after.module.as_dotted(),
            ));
        };
        if !required_target_external_modules.contains(&after.module)
            || !required_source_external_modules.contains(&after.module)
        {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                &after.module.as_dotted(),
            ));
        }
        let source_bytes = source_snapshot.bytes(
            &source_import.certificate,
            "l2_transport_source_verification_failed",
        )?;
        let target_bytes =
            target_snapshot.bytes(&after.certificate, "l2_transport_unscoped_target_change")?;
        if source_bytes != target_bytes {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                after.certificate.as_str(),
            ));
        }
    }
    for after in &target.modules {
        if !baseline
            .modules
            .iter()
            .any(|module| module.module == after.module)
            && !selected.contains(&after.module)
        {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                &after.module.as_dotted(),
            ));
        }
    }
    if baseline.schema != target.schema
        || baseline.package != target.package
        || baseline.core_spec != target.core_spec
        || baseline.kernel_profile != target.kernel_profile
        || baseline.certificate_format != target.certificate_format
        || baseline.checker_profile != target.checker_profile
        || baseline.policy != target.policy
        || baseline.license != target.license
        || baseline.repository != target.repository
        || baseline.description != target.description
    {
        return Err(diagnostic(
            "l2_transport_unscoped_target_change",
            "npa-package.toml",
        ));
    }
    let mut inventory = BTreeSet::from([
        PackagePath::new("npa-package.toml"),
        PackagePath::new(PACKAGE_LOCK_PATH),
        PackagePath::new(PACKAGE_AXIOM_REPORT_PATH),
        PackagePath::new(PACKAGE_THEOREM_INDEX_PATH),
    ]);
    for manifest in [baseline, target] {
        for module in &manifest.modules {
            inventory.insert(module.source.clone());
            inventory.insert(module.certificate.clone());
            inventory.extend(module.meta.iter().cloned());
            inventory.extend(module.replay.iter().cloned());
        }
        for import in manifest.imports.as_deref().unwrap_or_default() {
            inventory.insert(import.certificate.clone());
        }
    }
    let allowed_added_paths = target
        .modules
        .iter()
        .filter(|module| selected.contains(&module.module))
        .flat_map(|module| {
            [
                Some(module.source.clone()),
                Some(module.certificate.clone()),
                module.meta.clone(),
                module.replay.clone(),
            ]
            .into_iter()
            .flatten()
        })
        .chain(
            target_imports
                .iter()
                .filter(|import| !baseline_imports.iter().any(|before| before == *import))
                .map(|import| import.certificate.clone()),
        )
        .collect::<BTreeSet<_>>();
    let always_changeable = BTreeSet::from([
        PackagePath::new("npa-package.toml"),
        PackagePath::new(PACKAGE_LOCK_PATH),
        PackagePath::new(PACKAGE_AXIOM_REPORT_PATH),
        PackagePath::new(PACKAGE_THEOREM_INDEX_PATH),
    ]);
    let mut changed = Vec::new();
    for path in inventory {
        let baseline_bytes = baseline_snapshot.optional_bytes(&path);
        let target_bytes = target_snapshot.optional_bytes(&path);
        if baseline_bytes == target_bytes {
            continue;
        }
        let target_bytes = target_bytes
            .ok_or_else(|| diagnostic("l2_transport_unscoped_target_change", path.as_str()))?;
        if !always_changeable.contains(&path) && !allowed_added_paths.contains(&path) {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                path.as_str(),
            ));
        }
        if baseline_bytes.is_some() && allowed_added_paths.contains(&path) {
            return Err(diagnostic(
                "l2_transport_unscoped_target_change",
                path.as_str(),
            ));
        }
        changed.push(L2TransportAttestationChangedPath {
            path,
            baseline_file_hash: baseline_bytes.map(package_file_hash),
            target_file_hash: package_file_hash(target_bytes),
        });
    }
    Ok(changed)
}

fn package_certificates(
    loaded: &crate::package::LoadedPackageRoot,
    snapshot: &TransportAuditSnapshot,
    reason: &str,
) -> Result<BTreeMap<Name, LoadedTransportCertificate>, Box<CommandDiagnostic>> {
    let manifest = loaded.validated.manifest();
    let artifacts = manifest
        .modules
        .iter()
        .map(|module| {
            (
                &module.module,
                &module.certificate,
                Some(module.expected_certificate_file_hash),
                module.expected_certificate_hash,
                module.expected_export_hash,
                Some(module.expected_axiom_report_hash),
            )
        })
        .chain(
            manifest
                .imports
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(|import| {
                    (
                        &import.module,
                        &import.certificate,
                        None,
                        import.certificate_hash,
                        import.export_hash,
                        None,
                    )
                }),
        );
    let mut certificates = BTreeMap::new();
    for (
        module,
        certificate,
        expected_file_hash,
        expected_certificate_hash,
        expected_export_hash,
        expected_axiom_report_hash,
    ) in artifacts
    {
        let bytes = snapshot.bytes(certificate, reason)?;
        let cert = verify_module_cert_hashes(bytes)
            .map_err(|_| diagnostic(reason, certificate.as_str()))?;
        let file_hash = package_file_hash(bytes);
        if cert.header.module != *module
            || expected_file_hash.is_some_and(|expected| expected != file_hash)
            || PackageHash::from(cert.hashes.certificate_hash) != expected_certificate_hash
            || PackageHash::from(cert.hashes.export_hash) != expected_export_hash
            || expected_axiom_report_hash.is_some_and(|expected| {
                expected != PackageHash::from(cert.hashes.axiom_report_hash)
            })
        {
            return Err(diagnostic(reason, certificate.as_str()));
        }
        certificates.insert(
            module.clone(),
            LoadedTransportCertificate { cert, file_hash },
        );
    }
    Ok(certificates)
}

fn declaration_closure(
    certificates: &BTreeMap<Name, LoadedTransportCertificate>,
    roots: impl IntoIterator<Item = Name>,
) -> Result<DeclarationClosure, Box<CommandDiagnostic>> {
    let owners = certificates
        .iter()
        .map(|(module, loaded)| {
            declaration_owner_indices(&loaded.cert).map(|owners| (module.clone(), owners))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let mut closure = DeclarationClosure::default();
    let mut pending = roots.into_iter().collect::<VecDeque<_>>();
    let mut declarations = VecDeque::new();
    while let Some(module) = pending.pop_front() {
        let cert = certificates
            .get(&module)
            .ok_or_else(|| diagnostic("l2_transport_declaration_missing", &module.as_dotted()))?;
        closure.declarations.entry(module.clone()).or_default();
        for import in &cert.cert.imports {
            closure
                .required_imports
                .entry(module.clone())
                .or_default()
                .insert(import.module.clone());
            closure
                .declarations
                .entry(import.module.clone())
                .or_default();
        }
        for index in 0..cert.cert.declarations.len() {
            declarations.push_back((module.clone(), index));
        }
    }
    while let Some((module, index)) = declarations.pop_front() {
        if !closure
            .declarations
            .entry(module.clone())
            .or_default()
            .insert(index)
        {
            continue;
        }
        let cert = &certificates
            .get(&module)
            .ok_or_else(|| diagnostic("l2_transport_declaration_missing", &module.as_dotted()))?
            .cert;
        let declaration = cert
            .declarations
            .get(index)
            .ok_or_else(|| diagnostic("l2_transport_declaration_missing", &module.as_dotted()))?;
        for global in declaration
            .dependencies
            .iter()
            .map(|dependency| &dependency.global_ref)
            .chain(
                declaration
                    .axiom_dependencies
                    .iter()
                    .map(|axiom| &axiom.global_ref),
            )
        {
            match global {
                GlobalRef::Builtin { .. } => {}
                GlobalRef::Local { decl_index } | GlobalRef::LocalGenerated { decl_index, .. } => {
                    declarations.push_back((module.clone(), *decl_index));
                }
                GlobalRef::Imported {
                    import_index, name, ..
                } => {
                    let imported_module = cert
                        .imports
                        .get(*import_index)
                        .ok_or_else(|| {
                            diagnostic("l2_transport_declaration_missing", &module.as_dotted())
                        })?
                        .module
                        .clone();
                    let imported_name = cert.name_table.get(*name).ok_or_else(|| {
                        diagnostic("l2_transport_declaration_missing", &module.as_dotted())
                    })?;
                    closure
                        .required_imports
                        .entry(module.clone())
                        .or_default()
                        .insert(imported_module.clone());
                    let imported_index = owners
                        .get(&imported_module)
                        .and_then(|entries| entries.get(imported_name))
                        .copied()
                        .ok_or_else(|| {
                            diagnostic(
                                "l2_transport_declaration_missing",
                                &imported_module.as_dotted(),
                            )
                        })?;
                    declarations.push_back((imported_module, imported_index));
                }
            }
        }
    }
    Ok(closure)
}

fn declaration_owner_indices(
    cert: &ModuleCert,
) -> Result<BTreeMap<Name, usize>, Box<CommandDiagnostic>> {
    let mut owners = BTreeMap::new();
    for (index, declaration) in cert.declarations.iter().enumerate() {
        let mut names = vec![decl_name_id(&declaration.decl)];
        match &declaration.decl {
            DeclPayload::Inductive {
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                constructors,
                recursor,
                ..
            } => {
                names.extend(constructors.iter().map(|constructor| constructor.name));
                names.extend(recursor.iter().map(|recursor| recursor.name));
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    names.push(inductive.name);
                    names.extend(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.name),
                    );
                    names.extend(inductive.recursor.iter().map(|recursor| recursor.name));
                }
            }
            _ => {}
        }
        for name in names {
            let name = cert.name_table.get(name).cloned().ok_or_else(|| {
                diagnostic(
                    "l2_transport_declaration_missing",
                    &cert.header.module.as_dotted(),
                )
            })?;
            owners.insert(name, index);
        }
    }
    Ok(owners)
}

fn required_projection_names(
    cert: &ModuleCert,
    request: &npa_package::L2NamespaceTransportRequest,
    module: &Name,
    closure: &DeclarationClosure,
) -> Result<BTreeSet<Name>, Box<CommandDiagnostic>> {
    closure
        .declarations
        .get(module)
        .into_iter()
        .flatten()
        .map(|index| {
            let declaration = cert.declarations.get(*index).ok_or_else(|| {
                diagnostic("l2_transport_declaration_missing", &module.as_dotted())
            })?;
            let source_name = cert
                .name_table
                .get(decl_name_id(&declaration.decl))
                .ok_or_else(|| {
                    diagnostic("l2_transport_declaration_missing", &module.as_dotted())
                })?;
            request
                .map_global(module, source_name)
                .map(|(_, target_name)| target_name)
                .ok_or_else(|| diagnostic("l2_transport_mapping_incomplete", &module.as_dotted()))
        })
        .collect()
}

fn has_invalid_explicit_rename(
    renames: &[npa_package::L2TransportDeclarationRename],
    source_owners: &BTreeMap<Name, usize>,
    required_indices: &BTreeSet<usize>,
    target_names: &BTreeSet<Name>,
) -> bool {
    renames.iter().any(|rename| {
        !target_names.contains(&rename.target)
            || source_owners
                .get(&rename.source)
                .is_none_or(|owner| !required_indices.contains(owner))
    })
}

const fn decl_name_id(declaration: &DeclPayload) -> usize {
    match declaration {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn required_unmapped_external_modules(
    reachable: &BTreeSet<npa_cert::Name>,
    external: &BTreeSet<npa_cert::Name>,
    mapped: &BTreeSet<npa_cert::Name>,
) -> BTreeSet<npa_cert::Name> {
    reachable
        .intersection(external)
        .filter(|module| !mapped.contains(*module))
        .cloned()
        .collect()
}

fn first_unmapped_source_namespace(
    reachable: &BTreeSet<npa_cert::Name>,
    mapped: &BTreeSet<npa_cert::Name>,
    prefixes: &[String],
) -> Option<npa_cert::Name> {
    reachable
        .iter()
        .find(|module| {
            !mapped.contains(*module)
                && prefixes
                    .iter()
                    .any(|prefix| module.as_dotted().starts_with(prefix))
        })
        .cloned()
}

fn same_external_import_identity(
    source: &npa_package::PackageExternalImport,
    target: &npa_package::PackageExternalImport,
) -> bool {
    source.module == target.module
        && source.package == target.package
        && source.version == target.version
        && source.export_hash == target.export_hash
        && source.certificate_hash == target.certificate_hash
}

fn package_snapshot_inventory(manifest: &npa_package::PackageManifest) -> BTreeSet<PackagePath> {
    let mut inventory = BTreeSet::from([
        PackagePath::new("npa-package.toml"),
        PackagePath::new(PACKAGE_LOCK_PATH),
        PackagePath::new(PACKAGE_AXIOM_REPORT_PATH),
        PackagePath::new(PACKAGE_THEOREM_INDEX_PATH),
    ]);
    for module in &manifest.modules {
        inventory.insert(module.source.clone());
        inventory.insert(module.certificate.clone());
        inventory.extend(module.meta.iter().cloned());
        inventory.extend(module.replay.iter().cloned());
    }
    for import in manifest.imports.as_deref().unwrap_or_default() {
        inventory.insert(import.certificate.clone());
    }
    inventory
}

fn load_transport_audit_snapshot(
    loaded: &crate::package::LoadedPackageRoot,
) -> Result<TransportAuditSnapshot, Box<CommandDiagnostic>> {
    let audit = load_package_audit_snapshot(
        &loaded.root,
        COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    )
    .map_err(|_| diagnostic("l2_transport_verification_failed", "generated"))?;
    if audit.snapshot.validated != loaded.validated
        || audit.snapshot.projection_input_hashes.manifest_file_hash
            != package_file_hash(loaded.manifest_source.as_bytes())
    {
        return Err(diagnostic(
            "l2_transport_verification_failed",
            "npa-package.toml",
        ));
    }
    let axiom_source = audit
        .checked_generated
        .axiom_report_json
        .as_deref()
        .ok_or_else(|| {
            diagnostic(
                "l2_transport_verification_failed",
                PACKAGE_AXIOM_REPORT_PATH,
            )
        })?;
    let theorem_index_source = audit
        .checked_generated
        .theorem_index_json
        .as_deref()
        .ok_or_else(|| {
            diagnostic(
                "l2_transport_verification_failed",
                PACKAGE_THEOREM_INDEX_PATH,
            )
        })?;
    let axiom_report = parse_package_axiom_report_json(axiom_source).map_err(|_| {
        diagnostic(
            "l2_transport_verification_failed",
            PACKAGE_AXIOM_REPORT_PATH,
        )
    })?;
    let theorem_index = parse_package_theorem_index_json(theorem_index_source).map_err(|_| {
        diagnostic(
            "l2_transport_verification_failed",
            PACKAGE_THEOREM_INDEX_PATH,
        )
    })?;
    if axiom_report
        != audit.snapshot.project_axiom_report().map_err(|_| {
            diagnostic(
                "l2_transport_verification_failed",
                PACKAGE_AXIOM_REPORT_PATH,
            )
        })?
        || theorem_index
            != audit.snapshot.project_theorem_index().map_err(|_| {
                diagnostic(
                    "l2_transport_verification_failed",
                    PACKAGE_THEOREM_INDEX_PATH,
                )
            })?
    {
        return Err(diagnostic("l2_transport_verification_failed", "generated"));
    }
    let mut checker_identities = audit
        .snapshot
        .checker_summaries
        .iter()
        .map(|summary| {
            format!(
                "{}:{}:{}",
                summary.checker,
                summary.profile,
                summary.mode.as_str()
            )
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    checker_identities.sort();
    let mut files = BTreeMap::from([
        (
            PackagePath::new("npa-package.toml"),
            Some(loaded.manifest_source.as_bytes().to_vec()),
        ),
        (
            PackagePath::new(PACKAGE_LOCK_PATH),
            Some(audit.package_lock_json.as_bytes().to_vec()),
        ),
        (
            PackagePath::new(PACKAGE_AXIOM_REPORT_PATH),
            Some(axiom_source.as_bytes().to_vec()),
        ),
        (
            PackagePath::new(PACKAGE_THEOREM_INDEX_PATH),
            Some(theorem_index_source.as_bytes().to_vec()),
        ),
    ]);
    for artifact in &audit.snapshot.certificate_artifacts {
        files.insert(artifact.path.clone(), Some(artifact.bytes.clone()));
    }
    let mut snapshot = TransportAuditSnapshot {
        theorem_index,
        lock_file_hash: package_file_hash(audit.package_lock_json.as_bytes()),
        axiom_report_file_hash: package_file_hash(axiom_source.as_bytes()),
        theorem_index_file_hash: package_file_hash(theorem_index_source.as_bytes()),
        checker_identities,
        files,
    };
    let inventory = package_snapshot_inventory(loaded.validated.manifest());
    snapshot.capture_missing(&loaded.root, &inventory, "l2_transport_verification_failed")?;
    if let Some(missing) = inventory
        .iter()
        .find(|path| snapshot.optional_bytes(path).is_none())
    {
        return Err(diagnostic(
            "l2_transport_verification_failed",
            missing.as_str(),
        ));
    }
    Ok(snapshot)
}
fn read_package(
    root: &std::path::Path,
    path: &PackagePath,
    reason: &str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let full = confined_governance_path(root, path, path.as_str(), reason)?;
    fs::read(full).map_err(|_| diagnostic(reason, path.as_str()))
}
fn diagnostic(reason: &str, path: &str) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path))
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_package::{
        L2TransportDeclarationRename, PackageExternalImport, PackageId, PackageVersion,
    };

    #[test]
    fn explicit_dependency_rename_requires_its_owner_in_the_closure() {
        let source = Name::from_dotted("source_name");
        let target = Name::from_dotted("target_name");
        let renames = vec![L2TransportDeclarationRename {
            source: source.clone(),
            target: target.clone(),
        }];
        let owners = BTreeMap::from([(source, 3)]);
        let target_names = BTreeSet::from([target]);
        assert!(has_invalid_explicit_rename(
            &renames,
            &owners,
            &BTreeSet::new(),
            &target_names,
        ));
        assert!(!has_invalid_explicit_rename(
            &renames,
            &owners,
            &BTreeSet::from([3]),
            &target_names,
        ));
    }

    #[test]
    fn declaration_closure_excludes_unreferenced_dependency_declarations() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../testdata/package/npa-mathlib");
        let loaded = load_package_root(&root, "test").expect("fixture package must load");
        let snapshot = load_transport_audit_snapshot(&loaded).unwrap();
        let mut certificates = package_certificates(&loaded, &snapshot, "test").unwrap();
        let dependency = Name::from_dotted("Std.Nat.Basic");
        let mut unrelated = certificates[&Name::from_dotted("Mathlib.Core.Reduction")]
            .cert
            .declarations[0]
            .clone();
        unrelated.dependencies.clear();
        unrelated.axiom_dependencies.clear();
        let dependency_cert = &mut certificates.get_mut(&dependency).unwrap().cert;
        let unrelated_name = dependency_cert.name_table.len();
        dependency_cert
            .name_table
            .push(Name::from_dotted("transport_test_unrelated"));
        match &mut unrelated.decl {
            DeclPayload::Axiom { name, .. }
            | DeclPayload::AxiomConstrained { name, .. }
            | DeclPayload::Def { name, .. }
            | DeclPayload::DefConstrained { name, .. }
            | DeclPayload::Theorem { name, .. }
            | DeclPayload::TheoremConstrained { name, .. }
            | DeclPayload::Inductive { name, .. }
            | DeclPayload::InductiveConstrained { name, .. }
            | DeclPayload::MutualInductiveBlock { name, .. } => *name = unrelated_name,
        }
        dependency_cert.declarations.push(unrelated);
        let closure =
            declaration_closure(&certificates, [Name::from_dotted("Mathlib.Core.Reduction")])
                .unwrap();
        let required = closure.declarations.get(&dependency).unwrap();
        let available = certificates[&dependency].cert.declarations.len();
        assert!(!required.is_empty());
        assert!(required.len() < available);
    }

    #[test]
    fn external_identity_comparison_includes_package_and_version() {
        let import = |package: &str, version: &str| PackageExternalImport {
            module: npa_cert::Name::from_dotted("Std.External"),
            package: PackageId::new(package),
            version: PackageVersion::new(version),
            certificate: PackagePath::new("vendor/Std/External/certificate.npcert"),
            export_hash: package_file_hash(b"export"),
            certificate_hash: package_file_hash(b"certificate"),
        };
        assert!(same_external_import_identity(
            &import("npa-std", "0.1.0"),
            &import("npa-std", "0.1.0"),
        ));
        assert!(!same_external_import_identity(
            &import("npa-std", "0.1.0"),
            &import("other-package", "0.1.0"),
        ));
        assert!(!same_external_import_identity(
            &import("npa-std", "0.1.0"),
            &import("npa-std", "0.2.0"),
        ));
    }
}
