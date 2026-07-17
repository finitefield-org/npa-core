//! Promotion-origin registry validation and equivalent-source registration.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_package::{
    package_file_hash, parse_package_hash, parse_promotion_origin_registry_json,
    validate_promotion_origin_registry_transition, PromotionLifecycle, PromotionOriginRegistry,
    PromotionSourceModule, PromotionSourceOrigin, MATHLIB_PROMOTION_REGISTRY_PATH,
};

use crate::{
    args::{
        PackageRegisterEquivalentPromotionOriginOptions,
        PackageValidatePromotionOriginRegistryOptions,
    },
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_root,
    governance_writer::{confined_governance_path, lock_governance_artifact},
    package_artifacts::{
        load_package_audit_snapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
        PACKAGE_THEOREM_INDEX_PATH,
    },
    package_promotion_transaction::TargetLock,
};

const VALIDATE_COMMAND: &str = "package validate-promotion-origin-registry";
const REGISTER_COMMAND: &str = "package register-equivalent-promotion-origin";

/// Validate the canonical registry against target and optional source packages.
pub fn run_package_validate_promotion_origin_registry(
    options: PackageValidatePromotionOriginRegistryOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let registry = match load_registry(&options.common.root, VALIDATE_COMMAND) {
        Ok(registry) => registry,
        Err(diagnostic) => {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
    };
    if let Some(path) = &options.previous_registry {
        let previous = match fs::read_to_string(path)
            .map_err(|_| {
                diagnostic(
                    DiagnosticKind::ArtifactIo,
                    "promotion_registry_noncanonical",
                    path.display().to_string(),
                )
            })
            .and_then(|source| {
                parse_promotion_origin_registry_json(&source).map_err(|_| {
                    diagnostic(
                        DiagnosticKind::GeneratedArtifact,
                        "promotion_registry_noncanonical",
                        path.display().to_string(),
                    )
                })
            }) {
            Ok(previous) => previous,
            Err(diagnostic) => {
                return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic])
            }
        };
        if validate_promotion_origin_registry_transition(&previous, &registry).is_err() {
            return CommandResult::failed(
                VALIDATE_COMMAND,
                root_display,
                vec![*diagnostic(
                    DiagnosticKind::PackagePolicy,
                    "promotion_registry_transition_not_append_only",
                    MATHLIB_PROMOTION_REGISTRY_PATH,
                )],
            );
        }
    }
    let target = match load_package_audit_snapshot(
        &options.common.root,
        VALIDATE_COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(target) => target,
        Err(result) => return result,
    };
    if target.snapshot.validated.manifest().package != registry.target_package {
        return mismatch_result(
            VALIDATE_COMMAND,
            root_display,
            "promotion_registry_target_identity_mismatch",
            "$.target_package",
        );
    }
    if let Err(diagnostic) = validate_checked_generated(&target) {
        return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
    }
    if let Err(diagnostic) = validate_target_registry(&options.common.root, &target, &registry) {
        return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
    }

    let mut sources = BTreeMap::new();
    for source_root in &options.source_roots {
        let loaded = match load_package_audit_snapshot(
            source_root,
            VALIDATE_COMMAND,
            PackageGeneratedArtifactReadMode::all(),
            PackageArtifactReferenceSummaryMode::Include,
        ) {
            Ok(loaded) => loaded,
            Err(result) => return result,
        };
        if let Err(diagnostic) = validate_checked_generated(&loaded) {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        sources.insert(
            (
                loaded.snapshot.validated.manifest().package.clone(),
                loaded.snapshot.validated.manifest().version.clone(),
            ),
            (source_root.as_path(), loaded),
        );
    }
    let mut unavailable = 0usize;
    for entry in &registry.entries {
        for origin in std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources) {
            if let Some((root, loaded)) =
                sources.get(&(origin.package.clone(), origin.version.clone()))
            {
                if let Err(diagnostic) = validate_source_origin(root, loaded, origin, entry) {
                    return CommandResult::failed(
                        VALIDATE_COMMAND,
                        root_display,
                        vec![*diagnostic],
                    );
                }
            } else {
                unavailable += 1;
            }
        }
    }
    let mut result = CommandResult::passed(VALIDATE_COMMAND, root_display);
    if unavailable != 0 {
        result.diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "source_unavailable")
                .with_actual_value(unavailable.to_string()),
        );
    }
    result.artifacts.push(CommandArtifact {
        kind: "promotion_origin_registry".to_owned(),
        path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
    });
    result
}

/// Validate and optionally append one artifact-identical source origin.
pub fn run_package_register_equivalent_promotion_origin(
    options: PackageRegisterEquivalentPromotionOriginOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let mut target_lock = if options.apply {
        match TargetLock::acquire(&options.target_root) {
            Ok(lock) => Some(lock),
            Err(_) => {
                return mismatch_result(
                    REGISTER_COMMAND,
                    root_display,
                    "promotion_concurrent_update",
                    MATHLIB_PROMOTION_REGISTRY_PATH,
                )
            }
        }
    } else {
        None
    };
    let mut registry = match load_registry(&options.target_root, REGISTER_COMMAND) {
        Ok(registry) => registry,
        Err(diagnostic) => {
            return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic])
        }
    };
    let target = match load_package_audit_snapshot(
        &options.target_root,
        REGISTER_COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(target) => target,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&target) {
        return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
    }
    if let Err(diagnostic) = validate_target_registry(&options.target_root, &target, &registry) {
        return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
    }
    let promotion_id = match parse_package_hash(&options.promotion_id, "--promotion-id") {
        Ok(hash) => hash,
        Err(_) => {
            return mismatch_result(
                REGISTER_COMMAND,
                root_display,
                "promotion_registry_duplicate_origin",
                "--promotion-id",
            )
        }
    };
    if target_lock.as_mut().is_some_and(|lock| {
        lock.record(Some(promotion_id), "register-equivalent", None)
            .is_err()
    }) {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_concurrent_update",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let Some(position) = registry
        .entries
        .iter()
        .position(|entry| entry.promotion_id == promotion_id)
    else {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_duplicate_origin",
            "--promotion-id",
        );
    };
    let source = match load_package_audit_snapshot(
        &options.common.root,
        REGISTER_COMMAND,
        PackageGeneratedArtifactReadMode::all(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(source) => source,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&source) {
        return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
    }
    let canonical = &registry.entries[position].canonical_source;
    let candidate = match project_equivalent_origin(&options.common.root, &source, canonical) {
        Ok(origin) => origin,
        Err(diagnostic) => {
            return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic])
        }
    };
    if registry.entries.iter().any(|entry| {
        entry.canonical_source.package == candidate.package
            && entry.canonical_source.version == candidate.version
            || entry.equivalent_sources.iter().any(|source| {
                source.package == candidate.package && source.version == candidate.version
            })
    }) {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_duplicate_origin",
            "$.entries",
        );
    }
    let previous = registry.clone();
    registry.entries[position]
        .equivalent_sources
        .push(candidate);
    registry.entries[position]
        .equivalent_sources
        .sort_by(|left, right| {
            (&left.package, &left.version).cmp(&(&right.package, &right.version))
        });
    registry.generation += 1;
    if registry.refresh_hash().is_err() {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_noncanonical",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    if validate_promotion_origin_registry_transition(&previous, &registry).is_err() {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_transition_not_append_only",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let json = match registry.canonical_json() {
        Ok(json) => json,
        Err(_) => {
            return mismatch_result(
                REGISTER_COMMAND,
                root_display,
                "promotion_registry_noncanonical",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    };
    if options.apply {
        let path = npa_package::PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH);
        let lock = match lock_governance_artifact(&options.target_root, &path, "promotion_registry")
        {
            Ok(lock) => lock,
            Err(diagnostic) => {
                return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
            }
        };
        let expected = previous
            .canonical_json()
            .expect("validated registry serializes")
            .into_bytes();
        if let Err(diagnostic) = lock.replace_if_unchanged(json.as_bytes(), &expected) {
            return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
        }
    }
    let mut result = CommandResult::passed(REGISTER_COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: if options.apply {
            "promotion_origin_registry"
        } else {
            "promotion_origin_registry_dry_run"
        }
        .to_owned(),
        path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
    });
    result
}

pub(crate) fn load_registry(
    root: &Path,
    command: &str,
) -> Result<PromotionOriginRegistry, Box<CommandDiagnostic>> {
    load_registry_with_source(root, command).map(|(registry, _)| registry)
}

pub(crate) fn load_registry_with_source(
    root: &Path,
    _command: &str,
) -> Result<(PromotionOriginRegistry, String), Box<CommandDiagnostic>> {
    let path = npa_package::PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH);
    let full = confined_governance_path(
        root,
        &path,
        path.as_str(),
        "promotion_registry_noncanonical",
    )?;
    let source = fs::read_to_string(full).map_err(|_| {
        diagnostic(
            DiagnosticKind::ArtifactIo,
            "promotion_registry_noncanonical",
            path.as_str(),
        )
    })?;
    let registry = parse_promotion_origin_registry_json(&source).map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_noncanonical",
            path.as_str(),
        )
    })?;
    Ok((registry, source))
}

pub(crate) fn validate_checked_generated(
    loaded: &crate::package_artifacts::LoadedPackageAuditSnapshot,
) -> Result<(), Box<CommandDiagnostic>> {
    let axiom = loaded.snapshot.project_axiom_report().map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_AXIOM_REPORT_PATH,
        )
    })?;
    let index = loaded.snapshot.project_theorem_index().map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_THEOREM_INDEX_PATH,
        )
    })?;
    if loaded.checked_generated.axiom_report_json.as_deref()
        != Some(
            axiom
                .canonical_json()
                .map_err(|_| {
                    diagnostic(
                        DiagnosticKind::GeneratedArtifact,
                        "promotion_registry_target_identity_mismatch",
                        PACKAGE_AXIOM_REPORT_PATH,
                    )
                })?
                .as_str(),
        )
    {
        return Err(diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_AXIOM_REPORT_PATH,
        ));
    }
    if loaded.checked_generated.theorem_index_json.as_deref()
        != Some(
            index
                .canonical_json()
                .map_err(|_| {
                    diagnostic(
                        DiagnosticKind::GeneratedArtifact,
                        "promotion_registry_target_identity_mismatch",
                        PACKAGE_THEOREM_INDEX_PATH,
                    )
                })?
                .as_str(),
        )
    {
        return Err(diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_THEOREM_INDEX_PATH,
        ));
    }
    Ok(())
}

fn validate_target_registry(
    root: &Path,
    target: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    registry: &PromotionOriginRegistry,
) -> Result<(), Box<CommandDiagnostic>> {
    let manifest = target.snapshot.validated.manifest();
    let axiom = target.snapshot.project_axiom_report().map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_AXIOM_REPORT_PATH,
        )
    })?;
    let index = target.snapshot.project_theorem_index().map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_target_identity_mismatch",
            PACKAGE_THEOREM_INDEX_PATH,
        )
    })?;
    for entry in &registry.entries {
        validate_registry_evidence(root, &entry.evidence)?;
        validate_registry_lifecycle(root, &entry.lifecycle)?;
        for route in &entry.module_routes {
            validate_target_route_base(
                root,
                manifest,
                &axiom,
                &index,
                &entry.lifecycle,
                &route.target_module,
                route
                    .target_revisions
                    .last()
                    .expect("registry validation requires revision"),
            )?;
            if matches!(entry.lifecycle, PromotionLifecycle::Active) {
                let revision = route.target_revisions.last().expect("validated revision");
                let actual = index
                    .entries
                    .iter()
                    .filter(|row| row.global_ref.module == route.target_module)
                    .filter(|row| row.kind == npa_package::PackageTheoremIndexKind::Theorem)
                    .map(|row| (row.global_ref.name.clone(), row.statement.core_hash))
                    .collect::<BTreeSet<_>>();
                let expected = revision
                    .theorems
                    .iter()
                    .map(|row| (row.target_name.clone(), row.target_statement_hash))
                    .collect::<BTreeSet<_>>();
                if actual != expected {
                    return Err(identity_mismatch(&route.target_module));
                }
            }
        }
    }
    for reservation in &registry.unresolved_legacy_targets {
        validate_registry_evidence(root, &reservation.evidence)?;
        validate_registry_lifecycle(root, &reservation.lifecycle)?;
        validate_target_route_base(
            root,
            manifest,
            &axiom,
            &index,
            &reservation.lifecycle,
            &reservation.target_module,
            reservation
                .target_revisions
                .last()
                .expect("registry validation requires revision"),
        )?;
        if matches!(reservation.lifecycle, PromotionLifecycle::Active) {
            let revision = reservation
                .target_revisions
                .last()
                .expect("validated revision");
            let actual = index
                .entries
                .iter()
                .filter(|row| row.global_ref.module == reservation.target_module)
                .filter(|row| row.kind == npa_package::PackageTheoremIndexKind::Theorem)
                .map(|row| (row.global_ref.name.clone(), row.statement.core_hash))
                .collect::<BTreeSet<_>>();
            let expected = revision
                .theorems
                .iter()
                .map(|row| (row.target_name.clone(), row.target_statement_hash))
                .collect::<BTreeSet<_>>();
            if actual != expected {
                return Err(identity_mismatch(&reservation.target_module));
            }
        }
    }
    let active = registry
        .entries
        .iter()
        .flat_map(|entry| {
            entry
                .module_routes
                .iter()
                .filter(move |_| matches!(entry.lifecycle, PromotionLifecycle::Active))
                .map(|route| route.target_module.clone())
        })
        .chain(
            registry
                .unresolved_legacy_targets
                .iter()
                .filter(|row| matches!(row.lifecycle, PromotionLifecycle::Active))
                .map(|row| row.target_module.clone()),
        )
        .collect::<BTreeSet<_>>();
    let current = manifest
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    if active != current {
        return Err(diagnostic(
            DiagnosticKind::PackagePolicy,
            "promotion_registry_target_identity_mismatch",
            "$.unresolved_legacy_targets",
        ));
    }
    Ok(())
}

fn validate_target_route_base<T>(
    root: &Path,
    manifest: &npa_package::PackageManifest,
    axiom: &npa_package::PackageAxiomReport,
    index: &npa_package::PackageTheoremIndex,
    lifecycle: &PromotionLifecycle,
    module_name: &npa_cert::Name,
    revision: &npa_package::PromotionTargetRevision<T>,
) -> Result<(), Box<CommandDiagnostic>> {
    let module = manifest
        .modules
        .iter()
        .find(|module| &module.module == module_name);
    if matches!(lifecycle, PromotionLifecycle::Retired { .. }) {
        return if module.is_none() {
            Ok(())
        } else {
            Err(identity_mismatch(module_name))
        };
    }
    let module = module.ok_or_else(|| identity_mismatch(module_name))?;
    if version_tuple(&revision.target_version) > version_tuple(&manifest.version) {
        return Err(identity_mismatch(module_name));
    }
    let source = confined_governance_path(
        root,
        &module.source,
        module.source.as_str(),
        "promotion_registry_target_identity_mismatch",
    )?;
    let source_hash =
        package_file_hash(&fs::read(source).map_err(|_| identity_mismatch(module_name))?);
    if source_hash != revision.target_source_file_hash
        || module.expected_certificate_file_hash != revision.target_certificate_file_hash
        || module.expected_certificate_hash != revision.target_certificate_hash
        || module.expected_export_hash != revision.target_export_hash
        || module.expected_axiom_report_hash != revision.target_axiom_report_hash
    {
        return Err(identity_mismatch(module_name));
    }
    let axiom_row = axiom
        .modules
        .iter()
        .find(|row| &row.module == module_name)
        .ok_or_else(|| identity_mismatch(module_name))?;
    if axiom_row.certificate_file_hash != revision.target_certificate_file_hash
        || axiom_row.certificate_hash != revision.target_certificate_hash
        || axiom_row.export_hash != revision.target_export_hash
        || axiom_row.axiom_report_hash != revision.target_axiom_report_hash
    {
        return Err(identity_mismatch(module_name));
    }
    if index
        .entries
        .iter()
        .filter(|row| &row.global_ref.module == module_name)
        .any(|row| {
            row.global_ref.certificate_hash != revision.target_certificate_hash
                || row.global_ref.export_hash != revision.target_export_hash
                || row.module_axiom_report_hash != revision.target_axiom_report_hash
        })
    {
        return Err(identity_mismatch(module_name));
    }
    Ok(())
}

fn validate_source_origin(
    root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    origin: &PromotionSourceOrigin,
    entry: &npa_package::PromotionOriginEntry,
) -> Result<(), Box<CommandDiagnostic>> {
    if source.snapshot.validated.manifest().package != origin.package
        || source.snapshot.validated.manifest().version != origin.version
    {
        return Err(diagnostic(
            DiagnosticKind::HashMismatch,
            "promotion_registry_source_identity_mismatch",
            "$.canonical_source",
        ));
    }
    for expected in &origin.modules {
        let module = source
            .snapshot
            .validated
            .manifest()
            .modules
            .iter()
            .find(|module| module.module == expected.module)
            .ok_or_else(|| source_mismatch(&expected.module))?;
        let source_path = confined_governance_path(
            root,
            &module.source,
            module.source.as_str(),
            "promotion_registry_source_identity_mismatch",
        )?;
        let source_hash = package_file_hash(
            &fs::read(source_path).map_err(|_| source_mismatch(&expected.module))?,
        );
        if source_hash != expected.source_file_hash
            || module.expected_certificate_file_hash != expected.certificate_file_hash
            || module.expected_certificate_hash != expected.certificate_hash
            || module.expected_export_hash != expected.export_hash
        {
            return Err(source_mismatch(&expected.module));
        }
    }
    let index = source
        .snapshot
        .project_theorem_index()
        .map_err(|_| source_mismatch(&origin.modules[0].module))?;
    for route in &entry.module_routes {
        let revision = route.target_revisions.first().expect("validated revision");
        let actual = index
            .entries
            .iter()
            .filter(|row| row.global_ref.module == route.source_module)
            .filter(|row| row.kind == npa_package::PackageTheoremIndexKind::Theorem)
            .map(|row| (row.global_ref.name.clone(), row.statement.core_hash))
            .collect::<BTreeSet<_>>();
        let expected = revision
            .theorems
            .iter()
            .map(|row| (row.source_name.clone(), row.source_statement_hash))
            .collect::<BTreeSet<_>>();
        if actual != expected {
            return Err(source_mismatch(&route.source_module));
        }
    }
    Ok(())
}

fn validate_registry_evidence(
    root: &Path,
    evidence: &npa_package::PromotionEvidence,
) -> Result<(), Box<CommandDiagnostic>> {
    if let npa_package::PromotionEvidence::LegacyAudit {
        audit_location,
        audit_file_hash,
    } = evidence
    {
        if audit_location.repository == "npa-mathlib" {
            let full = confined_governance_path(
                root,
                &audit_location.path,
                audit_location.path.as_str(),
                "promotion_registry_target_identity_mismatch",
            )?;
            let bytes = fs::read(full).map_err(|_| {
                diagnostic(
                    DiagnosticKind::ArtifactIo,
                    "promotion_registry_target_identity_mismatch",
                    audit_location.path.as_str(),
                )
            })?;
            if package_file_hash(&bytes) != *audit_file_hash {
                return Err(diagnostic(
                    DiagnosticKind::HashMismatch,
                    "promotion_registry_target_identity_mismatch",
                    audit_location.path.as_str(),
                ));
            }
        }
    }
    Ok(())
}

fn validate_registry_lifecycle(
    root: &Path,
    lifecycle: &PromotionLifecycle,
) -> Result<(), Box<CommandDiagnostic>> {
    if let PromotionLifecycle::Retired {
        audit_location,
        audit_file_hash,
        ..
    } = lifecycle
    {
        if audit_location.repository == "npa-mathlib" {
            let full = confined_governance_path(
                root,
                &audit_location.path,
                audit_location.path.as_str(),
                "promotion_registry_target_identity_mismatch",
            )?;
            let bytes = fs::read(full).map_err(|_| {
                diagnostic(
                    DiagnosticKind::ArtifactIo,
                    "promotion_registry_target_identity_mismatch",
                    audit_location.path.as_str(),
                )
            })?;
            if package_file_hash(&bytes) != *audit_file_hash {
                return Err(diagnostic(
                    DiagnosticKind::HashMismatch,
                    "promotion_registry_target_identity_mismatch",
                    audit_location.path.as_str(),
                ));
            }
        }
    }
    Ok(())
}

fn version_tuple(version: &npa_package::PackageVersion) -> (u64, u64, u64) {
    let mut parts = version
        .as_str()
        .split('.')
        .map(|part| part.parse::<u64>().unwrap_or(0));
    (
        parts.next().unwrap_or(0),
        parts.next().unwrap_or(0),
        parts.next().unwrap_or(0),
    )
}

fn project_equivalent_origin(
    root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    canonical: &PromotionSourceOrigin,
) -> Result<PromotionSourceOrigin, Box<CommandDiagnostic>> {
    let manifest = source.snapshot.validated.manifest();
    let mut modules = Vec::new();
    for canonical_module in &canonical.modules {
        let module = manifest
            .modules
            .iter()
            .find(|module| module.module == canonical_module.module)
            .ok_or_else(|| source_mismatch(&canonical_module.module))?;
        let path = confined_governance_path(
            root,
            &module.source,
            module.source.as_str(),
            "promotion_registry_source_identity_mismatch",
        )?;
        let projected = PromotionSourceModule {
            module: module.module.clone(),
            source_file_hash: package_file_hash(
                &fs::read(path).map_err(|_| source_mismatch(&module.module))?,
            ),
            certificate_file_hash: module.expected_certificate_file_hash,
            certificate_hash: module.expected_certificate_hash,
            export_hash: module.expected_export_hash,
        };
        if projected.source_file_hash != canonical_module.source_file_hash
            || projected.certificate_file_hash != canonical_module.certificate_file_hash
            || projected.certificate_hash != canonical_module.certificate_hash
            || projected.export_hash != canonical_module.export_hash
        {
            return Err(source_mismatch(&module.module));
        }
        modules.push(projected);
    }
    Ok(PromotionSourceOrigin {
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        modules,
    })
}

fn identity_mismatch(module: &npa_cert::Name) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(
            DiagnosticKind::HashMismatch,
            "promotion_registry_target_identity_mismatch",
        )
        .with_module(module.as_dotted()),
    )
}

fn source_mismatch(module: &npa_cert::Name) -> Box<CommandDiagnostic> {
    Box::new(
        CommandDiagnostic::error(
            DiagnosticKind::HashMismatch,
            "promotion_registry_source_identity_mismatch",
        )
        .with_module(module.as_dotted()),
    )
}

fn diagnostic(
    kind: DiagnosticKind,
    reason: &str,
    path: impl Into<String>,
) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::error(kind, reason).with_path(path))
}

fn mismatch_result(command: &str, root: String, reason: &str, path: &str) -> CommandResult {
    CommandResult::failed(
        command,
        root,
        vec![*diagnostic(DiagnosticKind::PackagePolicy, reason, path)],
    )
}
