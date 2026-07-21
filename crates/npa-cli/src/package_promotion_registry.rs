//! Promotion-origin registry validation and equivalent-source registration.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{resolve_verified_declaration_export, GlobalDeclarationIdentity};
use npa_package::{
    lookup_promotion_origin, lookup_promotion_origin_v2,
    migrate_promotion_origin_registry_v1_to_v2, package_file_hash,
    parse_declaration_promotion_request_json, parse_mathlib_promotion_plan_v2_json,
    parse_package_hash, parse_promotion_origin_registry_json,
    parse_promotion_origin_registry_v2_json, parse_verified_materialization_attestation_json,
    validate_declaration_registry_entry_admission, validate_promotion_origin_registry_transition,
    validate_promotion_origin_registry_v1_to_v2_transition,
    validate_promotion_origin_registry_v2_transition, MathlibPromotionPlanV2,
    PackageArtifactOrigin, PackageLockEntryOrigin, PromotionLifecycle, PromotionOriginEntryV2,
    PromotionOriginLookup, PromotionOriginRegistry, PromotionOriginRegistryV2,
    PromotionPlanEndpoint, PromotionSourceModule, PromotionSourceOrigin,
    MATHLIB_PROMOTION_REGISTRY_PATH,
};

use crate::{
    args::{
        PackageCommonOptions, PackageRegisterEquivalentPromotionOriginOptions,
        PackageValidatePromotionOriginRegistryOptions,
    },
    diagnostic::{
        CommandArtifact, CommandDiagnostic, CommandResult, CommandStatus, DiagnosticKind,
    },
    fs::render_package_root,
    governance_writer::{confined_governance_path, lock_governance_artifact},
    package_artifacts::{
        load_package_audit_snapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
        PACKAGE_THEOREM_INDEX_PATH,
    },
    package_promotion_materialization_validate::normalized_closure_identity,
    package_promotion_materialize::{
        declaration_plan_selection_current, filtered_declaration_replay,
    },
    package_promotion_prepare_declaration::endpoint_record,
    package_promotion_transaction::TargetLock,
};

const VALIDATE_COMMAND: &str = "package validate-promotion-origin-registry";
const REGISTER_COMMAND: &str = "package register-equivalent-promotion-origin";

pub(crate) const fn promotion_plan_generated_read_mode() -> PackageGeneratedArtifactReadMode {
    PackageGeneratedArtifactReadMode {
        axiom_report: true,
        theorem_index: true,
        theorem_premise_report: false,
    }
}

pub(crate) enum ParsedPromotionOriginRegistry {
    V1(PromotionOriginRegistry),
    V2(PromotionOriginRegistryV2),
}

pub(crate) fn parse_promotion_origin_registry_versioned(
    source: &str,
) -> Result<ParsedPromotionOriginRegistry, ()> {
    if let Ok(registry) = parse_promotion_origin_registry_v2_json(source) {
        return Ok(ParsedPromotionOriginRegistry::V2(registry));
    }
    parse_promotion_origin_registry_json(source)
        .map(ParsedPromotionOriginRegistry::V1)
        .map_err(|_| ())
}

pub(crate) fn lookup_promotion_origin_versioned(
    registry: &ParsedPromotionOriginRegistry,
    source: &PromotionSourceOrigin,
    target_modules: &[npa_cert::Name],
    target_artifacts: &[(npa_package::PackageHash, npa_package::PackageHash)],
) -> PromotionOriginLookup {
    match registry {
        ParsedPromotionOriginRegistry::V1(registry) => {
            lookup_promotion_origin(registry, source, target_modules, target_artifacts)
        }
        ParsedPromotionOriginRegistry::V2(registry) => {
            lookup_promotion_origin_v2(registry, source, target_modules, target_artifacts)
        }
    }
}

/// Validate the canonical registry against target and optional source packages.
pub fn run_package_validate_promotion_origin_registry(
    options: PackageValidatePromotionOriginRegistryOptions,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let registry_source = match load_registry_source(&options.common.root) {
        Ok(source) => source,
        Err(diagnostic) => {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
    };
    let registry = match parse_promotion_origin_registry_versioned(&registry_source) {
        Ok(ParsedPromotionOriginRegistry::V2(registry)) => {
            return run_validate_registry_v2(options, registry)
        }
        Ok(ParsedPromotionOriginRegistry::V1(registry)) => registry,
        Err(()) => {
            return mismatch_result(
                VALIDATE_COMMAND,
                root_display,
                "promotion_registry_noncanonical",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
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
        promotion_plan_generated_read_mode(),
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
            promotion_plan_generated_read_mode(),
            PackageArtifactReferenceSummaryMode::Include,
        ) {
            Ok(loaded) => loaded,
            Err(result) => return result,
        };
        if let Err(diagnostic) = validate_checked_generated(&loaded) {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        sources
            .entry((
                loaded.snapshot.validated.manifest().package.clone(),
                loaded.snapshot.validated.manifest().version.clone(),
            ))
            .or_insert_with(Vec::new)
            .push((source_root.as_path(), loaded));
    }
    let mut unavailable = 0usize;
    for entry in &registry.entries {
        for origin in std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources) {
            if let Some(loaded_sources) =
                sources.get(&(origin.package.clone(), origin.version.clone()))
            {
                for (root, loaded) in loaded_sources {
                    if let Err(diagnostic) = validate_source_origin(root, loaded, origin, entry) {
                        return CommandResult::failed(
                            VALIDATE_COMMAND,
                            root_display,
                            vec![*diagnostic],
                        );
                    }
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
    let root_display = render_package_root(&options.target_root);
    let source = match load_registry_source(&options.target_root) {
        Ok(source) => source,
        Err(diagnostic) => {
            return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
        }
    };
    match parse_promotion_origin_registry_versioned(&source) {
        Ok(ParsedPromotionOriginRegistry::V2(registry)) => {
            run_register_equivalent_v2(options, RegistryPrevious::V2(registry), source)
        }
        Ok(ParsedPromotionOriginRegistry::V1(registry)) => {
            run_register_equivalent_v2(options, RegistryPrevious::V1(registry), source)
        }
        Err(()) => mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_noncanonical",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        ),
    }
}

enum RegistryPrevious {
    V1(PromotionOriginRegistry),
    V2(PromotionOriginRegistryV2),
}

fn run_register_equivalent_v2(
    options: PackageRegisterEquivalentPromotionOriginOptions,
    previous: RegistryPrevious,
    previous_source: String,
) -> CommandResult {
    let root_display = render_package_root(&options.target_root);
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
    let target_validation = run_package_validate_promotion_origin_registry(
        PackageValidatePromotionOriginRegistryOptions {
            common: PackageCommonOptions {
                root: options.target_root.clone(),
                json: false,
            },
            source_roots: Vec::new(),
            previous_registry: None,
        },
    );
    if target_validation.status != CommandStatus::Passed {
        return CommandResult::failed(
            REGISTER_COMMAND,
            root_display,
            target_validation.diagnostics,
        );
    }
    let mut registry = match &previous {
        RegistryPrevious::V1(previous) => {
            match migrate_promotion_origin_registry_v1_to_v2(previous) {
                Ok(registry) => registry,
                Err(_) => {
                    return mismatch_result(
                        REGISTER_COMMAND,
                        root_display,
                        "promotion_registry_upgrade_invalid",
                        MATHLIB_PROMOTION_REGISTRY_PATH,
                    )
                }
            }
        }
        RegistryPrevious::V2(previous) => previous.clone(),
    };
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
        .position(|entry| entry.promotion_id() == promotion_id)
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
        promotion_plan_generated_read_mode(),
        PackageArtifactReferenceSummaryMode::Include,
    ) {
        Ok(source) => source,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&source) {
        return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
    }
    let candidate_identity = (
        source.snapshot.validated.manifest().package.clone(),
        source.snapshot.validated.manifest().version.clone(),
    );
    let duplicate = match &registry.entries[position] {
        PromotionOriginEntryV2::WholeModuleV1(entry) => {
            (
                entry.canonical_source.package.clone(),
                entry.canonical_source.version.clone(),
            ) == candidate_identity
                || entry
                    .equivalent_sources
                    .iter()
                    .any(|row| (row.package.clone(), row.version.clone()) == candidate_identity)
        }
        PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
            (
                entry.canonical_source.package.clone(),
                entry.canonical_source.version.clone(),
            ) == candidate_identity
                || entry
                    .equivalent_sources
                    .iter()
                    .any(|row| (row.package.clone(), row.version.clone()) == candidate_identity)
        }
    };
    if duplicate {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_duplicate_origin",
            "$.entries",
        );
    }
    match &mut registry.entries[position] {
        PromotionOriginEntryV2::WholeModuleV1(entry) => {
            let candidate = match project_equivalent_origin(
                &options.common.root,
                &source,
                &entry.canonical_source,
            ) {
                Ok(candidate) => candidate,
                Err(diagnostic) => {
                    return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic])
                }
            };
            entry.equivalent_sources.push(candidate);
            entry.equivalent_sources.sort_by(|left, right| {
                (&left.package, &left.version).cmp(&(&right.package, &right.version))
            });
        }
        PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
            let manifest = source.snapshot.validated.manifest();
            let Some(module) = manifest
                .modules
                .iter()
                .find(|module| module.module == entry.source_module)
            else {
                return mismatch_result(
                    REGISTER_COMMAND,
                    root_display,
                    "promotion_registry_source_identity_mismatch",
                    "$.entries",
                );
            };
            let source_path = match confined_governance_path(
                &options.common.root,
                &module.source,
                module.source.as_str(),
                "promotion_registry_source_identity_mismatch",
            ) {
                Ok(path) => path,
                Err(diagnostic) => {
                    return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic])
                }
            };
            let bytes = match fs::read(source_path) {
                Ok(bytes) => bytes,
                Err(_) => {
                    return mismatch_result(
                        REGISTER_COMMAND,
                        root_display,
                        "promotion_registry_source_identity_mismatch",
                        module.source.as_str(),
                    )
                }
            };
            let canonical = &entry.canonical_source;
            if package_file_hash(&bytes) != canonical.source_file_hash
                || module.expected_certificate_file_hash != canonical.certificate_file_hash
                || module.expected_certificate_hash != canonical.certificate_hash
                || module.expected_export_hash != canonical.export_hash
            {
                return mismatch_result(
                    REGISTER_COMMAND,
                    root_display,
                    "promotion_registry_source_identity_mismatch",
                    module.source.as_str(),
                );
            }
            entry
                .equivalent_sources
                .push(npa_package::PromotionPlanV2EquivalentSource {
                    package: manifest.package.clone(),
                    version: manifest.version.clone(),
                    source_module: entry.source_module.clone(),
                    source_file_hash: canonical.source_file_hash,
                    certificate_file_hash: canonical.certificate_file_hash,
                    certificate_hash: canonical.certificate_hash,
                    export_hash: canonical.export_hash,
                    declaration_closure_hash: canonical.declaration_closure_hash,
                    dependency_edge_hash: canonical.dependency_edge_hash,
                });
            entry.equivalent_sources.sort();
        }
    }
    let Some(next_generation) = registry.generation.checked_add(1) else {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_transition_not_append_only",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    };
    registry.generation = next_generation;
    if registry.refresh_hash().is_err() {
        return mismatch_result(
            REGISTER_COMMAND,
            root_display,
            "promotion_registry_noncanonical",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let valid = match &previous {
        RegistryPrevious::V1(previous) => migrate_promotion_origin_registry_v1_to_v2(previous)
            .ok()
            .is_some_and(|migrated| {
                validate_promotion_origin_registry_v2_transition(&migrated, &registry).is_ok()
            }),
        RegistryPrevious::V2(previous) => {
            validate_promotion_origin_registry_v2_transition(previous, &registry).is_ok()
        }
    };
    if !valid {
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
                return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic])
            }
        };
        if let Err(diagnostic) =
            lock.replace_if_unchanged(json.as_bytes(), previous_source.as_bytes())
        {
            return CommandResult::failed(REGISTER_COMMAND, root_display, vec![*diagnostic]);
        }
    }
    let mut result = CommandResult::passed(REGISTER_COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: if options.apply {
            "promotion_origin_registry_v2"
        } else {
            "promotion_origin_registry_v2_dry_run"
        }
        .to_owned(),
        path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
    });
    result
}

fn load_registry_source(root: &Path) -> Result<String, Box<CommandDiagnostic>> {
    let path = npa_package::PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH);
    let full = confined_governance_path(
        root,
        &path,
        path.as_str(),
        "promotion_registry_noncanonical",
    )?;
    fs::read_to_string(full).map_err(|_| {
        diagnostic(
            DiagnosticKind::ArtifactIo,
            "promotion_registry_noncanonical",
            path.as_str(),
        )
    })
}

pub(crate) fn load_registry_versioned_with_source(
    root: &Path,
    _command: &str,
) -> Result<(ParsedPromotionOriginRegistry, String), Box<CommandDiagnostic>> {
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
    let registry = parse_promotion_origin_registry_versioned(&source).map_err(|_| {
        diagnostic(
            DiagnosticKind::GeneratedArtifact,
            "promotion_registry_noncanonical",
            path.as_str(),
        )
    })?;
    Ok((registry, source))
}

fn run_validate_registry_v2(
    options: PackageValidatePromotionOriginRegistryOptions,
    registry: PromotionOriginRegistryV2,
) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    if let Some(path) = &options.previous_registry {
        let previous = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(_) => {
                return mismatch_result(
                    VALIDATE_COMMAND,
                    root_display,
                    "promotion_registry_noncanonical",
                    &path.display().to_string(),
                )
            }
        };
        let valid = match parse_promotion_origin_registry_versioned(&previous) {
            Ok(ParsedPromotionOriginRegistry::V2(previous)) => {
                validate_promotion_origin_registry_v2_transition(&previous, &registry).is_ok()
            }
            Ok(ParsedPromotionOriginRegistry::V1(previous)) => {
                validate_promotion_origin_registry_v1_to_v2_transition(&previous, &registry).is_ok()
            }
            Err(()) => false,
        };
        if !valid {
            return mismatch_result(
                VALIDATE_COMMAND,
                root_display,
                "promotion_registry_transition_not_append_only",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            );
        }
    }
    let target = match load_package_audit_snapshot(
        &options.common.root,
        VALIDATE_COMMAND,
        promotion_plan_generated_read_mode(),
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
    let target_axiom = match target.snapshot.project_axiom_report() {
        Ok(value) => value,
        Err(_) => {
            return mismatch_result(
                VALIDATE_COMMAND,
                root_display,
                "promotion_registry_target_identity_mismatch",
                PACKAGE_AXIOM_REPORT_PATH,
            )
        }
    };
    let target_index = match target.snapshot.project_theorem_index() {
        Ok(value) => value,
        Err(_) => {
            return mismatch_result(
                VALIDATE_COMMAND,
                root_display,
                "promotion_registry_target_identity_mismatch",
                PACKAGE_THEOREM_INDEX_PATH,
            )
        }
    };
    let mut source_snapshots = BTreeMap::new();
    for root in &options.source_roots {
        let snapshot = match load_package_audit_snapshot(
            root,
            VALIDATE_COMMAND,
            promotion_plan_generated_read_mode(),
            PackageArtifactReferenceSummaryMode::Include,
        ) {
            Ok(snapshot) => snapshot,
            Err(result) => return result,
        };
        if let Err(diagnostic) = validate_checked_generated(&snapshot) {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        source_snapshots
            .entry((
                snapshot.snapshot.validated.manifest().package.clone(),
                snapshot.snapshot.validated.manifest().version.clone(),
            ))
            .or_insert_with(Vec::new)
            .push((root.as_path(), snapshot));
    }
    let mut active = BTreeSet::new();
    let mut unavailable = 0usize;
    for entry in &registry.entries {
        match entry {
            PromotionOriginEntryV2::WholeModuleV1(entry) => {
                if let Err(diagnostic) =
                    validate_registry_evidence(&options.common.root, &entry.evidence)
                {
                    return CommandResult::failed(
                        VALIDATE_COMMAND,
                        root_display,
                        vec![*diagnostic],
                    );
                }
                if let Err(diagnostic) =
                    validate_registry_lifecycle(&options.common.root, &entry.lifecycle)
                {
                    return CommandResult::failed(
                        VALIDATE_COMMAND,
                        root_display,
                        vec![*diagnostic],
                    );
                }
                for route in &entry.module_routes {
                    if matches!(entry.lifecycle, PromotionLifecycle::Active) {
                        active.insert(route.target_module.clone());
                    }
                    if let Err(diagnostic) = validate_target_route_base(
                        &options.common.root,
                        target.snapshot.validated.manifest(),
                        &target_axiom,
                        &target_index,
                        &entry.lifecycle,
                        &route.target_module,
                        route.target_revisions.last().expect("validated registry"),
                    ) {
                        return CommandResult::failed(
                            VALIDATE_COMMAND,
                            root_display,
                            vec![*diagnostic],
                        );
                    }
                }
                for origin in
                    std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources)
                {
                    if let Some(snapshots) =
                        source_snapshots.get(&(origin.package.clone(), origin.version.clone()))
                    {
                        for (root, snapshot) in snapshots {
                            if let Err(diagnostic) =
                                validate_source_origin(root, snapshot, origin, entry)
                            {
                                return CommandResult::failed(
                                    VALIDATE_COMMAND,
                                    root_display,
                                    vec![*diagnostic],
                                );
                            }
                        }
                    } else {
                        unavailable += 1;
                    }
                }
            }
            PromotionOriginEntryV2::DeclarationClosureV1(entry) => {
                active.insert(entry.target_module.clone());
                if let Err(diagnostic) =
                    validate_declaration_target_v2(&options.common.root, &target, entry)
                {
                    return CommandResult::failed(
                        VALIDATE_COMMAND,
                        root_display,
                        vec![*diagnostic],
                    );
                }
                for origin in
                    std::iter::once(&entry.canonical_source).chain(&entry.equivalent_sources)
                {
                    if let Some(snapshots) =
                        source_snapshots.get(&(origin.package.clone(), origin.version.clone()))
                    {
                        for (root, snapshot) in snapshots {
                            if let Err(diagnostic) = validate_declaration_source_v2(
                                root,
                                snapshot,
                                &options.common.root,
                                &target,
                                origin,
                                entry,
                            ) {
                                return CommandResult::failed(
                                    VALIDATE_COMMAND,
                                    root_display,
                                    vec![*diagnostic],
                                );
                            }
                        }
                    } else {
                        unavailable += 1;
                    }
                }
            }
        }
    }
    for reservation in &registry.unresolved_legacy_targets {
        if let Err(diagnostic) =
            validate_registry_evidence(&options.common.root, &reservation.evidence)
        {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        if let Err(diagnostic) =
            validate_registry_lifecycle(&options.common.root, &reservation.lifecycle)
        {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        if let Err(diagnostic) = validate_target_route_base(
            &options.common.root,
            target.snapshot.validated.manifest(),
            &target_axiom,
            &target_index,
            &reservation.lifecycle,
            &reservation.target_module,
            reservation
                .target_revisions
                .last()
                .expect("validated registry"),
        ) {
            return CommandResult::failed(VALIDATE_COMMAND, root_display, vec![*diagnostic]);
        }
        if matches!(reservation.lifecycle, PromotionLifecycle::Active) {
            active.insert(reservation.target_module.clone());
        }
    }
    let current = target
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<BTreeSet<_>>();
    if active != current {
        return mismatch_result(
            VALIDATE_COMMAND,
            root_display,
            "promotion_registry_target_identity_mismatch",
            "$.entries",
        );
    }
    let mut result = CommandResult::passed(VALIDATE_COMMAND, root_display);
    if unavailable != 0 {
        result.diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "source_unavailable")
                .with_actual_value(unavailable.to_string()),
        );
    }
    result.artifacts.push(CommandArtifact {
        kind: "promotion_origin_registry_v2".to_owned(),
        path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
    });
    result
}

fn validate_declaration_target_v2(
    root: &Path,
    target: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    entry: &npa_package::DeclarationClosureRegistryEntry,
) -> Result<(), Box<CommandDiagnostic>> {
    let revision = entry
        .target_revisions
        .last()
        .ok_or_else(|| identity_mismatch(&entry.target_module))?;
    let module = target
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .find(|module| module.module == entry.target_module)
        .ok_or_else(|| identity_mismatch(&entry.target_module))?;
    if version_tuple(&revision.target_version)
        > version_tuple(&target.snapshot.validated.manifest().version)
    {
        return Err(identity_mismatch(&entry.target_module));
    }
    let source = fs::read(confined_governance_path(
        root,
        &module.source,
        module.source.as_str(),
        "promotion_registry_target_identity_mismatch",
    )?)
    .map_err(|_| identity_mismatch(&entry.target_module))?;
    let meta_path = module
        .meta
        .as_ref()
        .ok_or_else(|| identity_mismatch(&entry.target_module))?;
    let replay_path = module
        .replay
        .as_ref()
        .ok_or_else(|| identity_mismatch(&entry.target_module))?;
    let meta = fs::read(confined_governance_path(
        root,
        meta_path,
        meta_path.as_str(),
        "promotion_registry_target_identity_mismatch",
    )?)
    .map_err(|_| identity_mismatch(&entry.target_module))?;
    let replay = fs::read(confined_governance_path(
        root,
        replay_path,
        replay_path.as_str(),
        "promotion_registry_target_identity_mismatch",
    )?)
    .map_err(|_| identity_mismatch(&entry.target_module))?;
    if package_file_hash(&source) != revision.target_source_file_hash
        || package_file_hash(&meta) != revision.target_meta_file_hash
        || package_file_hash(&replay) != revision.target_replay_file_hash
        || module.expected_certificate_file_hash != revision.target_certificate_file_hash
        || module.expected_certificate_hash != revision.target_certificate_hash
        || module.expected_export_hash != revision.target_export_hash
        || module.expected_axiom_report_hash != revision.target_axiom_report_hash
    {
        return Err(identity_mismatch(&entry.target_module));
    }
    let index = target
        .snapshot
        .project_theorem_index()
        .map_err(|_| identity_mismatch(&entry.target_module))?;
    let actual = index
        .entries
        .iter()
        .filter(|row| {
            row.global_ref.module == entry.target_module
                && row.kind == npa_package::PackageTheoremIndexKind::Theorem
        })
        .map(|row| (row.global_ref.name.clone(), row.statement.core_hash))
        .collect::<BTreeSet<_>>();
    let expected = revision
        .theorems
        .iter()
        .map(|row| (row.target_name.clone(), row.statement_hash))
        .collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(identity_mismatch(&entry.target_module));
    }
    Ok(())
}

fn validate_declaration_source_v2(
    root: &Path,
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    target_root: &Path,
    target: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    origin: &npa_package::PromotionPlanV2EquivalentSource,
    entry: &npa_package::DeclarationClosureRegistryEntry,
) -> Result<(), Box<CommandDiagnostic>> {
    let manifest = source.snapshot.validated.manifest();
    let module = manifest
        .modules
        .iter()
        .find(|module| module.module == origin.source_module)
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let bytes = fs::read(confined_governance_path(
        root,
        &module.source,
        module.source.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    if manifest.package != origin.package
        || manifest.version != origin.version
        || package_file_hash(&bytes) != origin.source_file_hash
        || module.expected_certificate_file_hash != origin.certificate_file_hash
        || module.expected_certificate_hash != origin.certificate_hash
        || module.expected_export_hash != origin.export_hash
        || origin.declaration_closure_hash != entry.evidence.declaration_closure_hash
    {
        return Err(source_mismatch(&origin.source_module));
    }
    if origin.package != entry.canonical_source.package
        || origin.version != entry.canonical_source.version
    {
        return Ok(());
    }
    let plan_bytes = fs::read(confined_governance_path(
        root,
        &entry.evidence.plan_path,
        entry.evidence.plan_path.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    let attestation_bytes = fs::read(confined_governance_path(
        root,
        &entry.evidence.attestation_path,
        entry.evidence.attestation_path.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    let plan = std::str::from_utf8(&plan_bytes)
        .ok()
        .and_then(|source| parse_mathlib_promotion_plan_v2_json(source).ok())
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let attestation = std::str::from_utf8(&attestation_bytes)
        .ok()
        .and_then(|source| parse_verified_materialization_attestation_json(source).ok())
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let request_bytes = fs::read(confined_governance_path(
        root,
        &plan.governance.request_path,
        plan.governance.request_path.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    let request = std::str::from_utf8(&request_bytes)
        .ok()
        .and_then(|source| parse_declaration_promotion_request_json(source).ok())
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let source_external = declaration_registry_mapping_identities(source, target, &plan)
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let normalized_closure_hash =
        normalized_closure_identity(root, target_root, source, target, target, &plan)
            .map_err(|_| source_mismatch(&origin.source_module))?;
    let meta_path = module
        .meta
        .as_ref()
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let replay_path = module
        .replay
        .as_ref()
        .ok_or_else(|| source_mismatch(&origin.source_module))?;
    let meta_bytes = fs::read(confined_governance_path(
        root,
        meta_path,
        meta_path.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    let replay_bytes = fs::read(confined_governance_path(
        root,
        replay_path,
        replay_path.as_str(),
        "promotion_registry_source_identity_mismatch",
    )?)
    .map_err(|_| source_mismatch(&origin.source_module))?;
    let replay_source =
        std::str::from_utf8(&replay_bytes).map_err(|_| source_mismatch(&origin.source_module))?;
    let (expected_target_replay, expected_omissions) =
        filtered_declaration_replay(replay_source, &plan)
            .map_err(|_| source_mismatch(&origin.source_module))?;
    if package_file_hash(&plan_bytes) != entry.evidence.plan_file_hash
        || package_file_hash(&attestation_bytes) != entry.evidence.attestation_file_hash
        || validate_declaration_registry_entry_admission(entry, &plan, &attestation).is_err()
        || source.snapshot.manifest.file_hash != plan.source.manifest_file_hash
        || package_file_hash(source.package_lock_json.as_bytes()) != plan.source.lock_file_hash
        || source
            .checked_generated
            .axiom_report_json
            .as_deref()
            .is_none_or(|value| {
                package_file_hash(value.as_bytes()) != plan.source.axiom_report_file_hash
            })
        || source
            .checked_generated
            .theorem_index_json
            .as_deref()
            .is_none_or(|value| {
                package_file_hash(value.as_bytes()) != plan.source.theorem_index_file_hash
            })
        || module.source != plan.selection.source_path
        || module.certificate != plan.selection.certificate_path
        || meta_path != &plan.selection.meta_path
        || replay_path != &plan.selection.replay_path
        || package_file_hash(&request_bytes) != plan.governance.request_file_hash
        || package_file_hash(&meta_bytes) != plan.selection.meta_file_hash
        || package_file_hash(&replay_bytes) != plan.selection.replay_file_hash
        || package_file_hash(expected_target_replay.as_bytes())
            != attestation.target.replay_file_hash
        || expected_omissions != attestation.replay_omissions
        || !declaration_plan_selection_current(root, source, &request, &plan, &source_external)
        || normalized_closure_hash != entry.evidence.normalized_closure_hash
        || plan.promotion_id != entry.promotion_id
        || attestation.promotion_id != entry.promotion_id
        || plan.selection.declaration_closure_hash != entry.evidence.declaration_closure_hash
        || attestation.normalized_closure_hash != entry.evidence.normalized_closure_hash
        || plan.governance.catalog_policy_file_hash != entry.evidence.catalog_policy_file_hash
        || plan.governance.namespace_policy_file_hash != entry.evidence.namespace_policy_file_hash
    {
        return Err(source_mismatch(&origin.source_module));
    }
    Ok(())
}

fn declaration_registry_mapping_identities(
    source: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    target: &crate::package_artifacts::LoadedPackageAuditSnapshot,
    plan: &MathlibPromotionPlanV2,
) -> Option<BTreeMap<GlobalDeclarationIdentity, GlobalDeclarationIdentity>> {
    let mut mappings = BTreeMap::new();
    for mapping in &plan.dependency_mappings {
        let source_record = endpoint_record(source, &mapping.source)?;
        let target_record = registry_target_endpoint_record(target, &mapping.target)?;
        let source_identity = resolve_verified_declaration_export(
            &source_record.verified_module,
            &mapping.declaration_name,
        )
        .ok()?
        .identity;
        let target_identity = resolve_verified_declaration_export(
            &target_record.verified_module,
            &mapping.declaration_name,
        )
        .ok()?
        .identity;
        if source_identity.kind != target_identity.kind
            || npa_package::PackageHash::from(source_identity.decl_interface_hash)
                != mapping.source_decl_interface_hash
            || npa_package::PackageHash::from(target_identity.decl_interface_hash)
                != mapping.target_decl_interface_hash
            || target_record.certificate.file_hash != mapping.target_certificate_file_hash
            || target_record.key.certificate_hash != mapping.target_certificate_hash
            || target_record.key.export_hash != mapping.target_export_hash
            || mappings.insert(source_identity, target_identity).is_some()
        {
            return None;
        }
    }
    Some(mappings)
}

fn registry_target_endpoint_record<'a>(
    target: &'a crate::package_artifacts::LoadedPackageAuditSnapshot,
    endpoint: &PromotionPlanEndpoint,
) -> Option<&'a npa_api::PackageArtifactVerifiedModule> {
    if endpoint.origin == PackageArtifactOrigin::External {
        return endpoint_record(target, endpoint);
    }
    let manifest = target.snapshot.validated.manifest();
    let lock = target
        .snapshot
        .package_lock_manifest
        .entries
        .iter()
        .find(|entry| entry.module == endpoint.module)?;
    (lock.origin == PackageLockEntryOrigin::Local
        && endpoint.package == manifest.package
        && version_tuple(&endpoint.version) <= version_tuple(&manifest.version))
    .then(|| {
        target
            .snapshot
            .decoded_module_records
            .values()
            .find(|record| record.key.module == endpoint.module)
    })
    .flatten()
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

#[cfg(test)]
mod tests {
    use super::*;
    use npa_package::{
        promotion_legacy_target_reservation_id, PackageHash, PackagePath, PackageVersion,
        PromotionAuditLocation, PromotionEvidence, PromotionLegacyTargetReservation,
        PromotionReservedTheorem, PromotionTargetRevision,
        MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA,
    };

    #[test]
    fn version_dispatch_uses_the_top_level_schema_not_embedded_evidence_text() {
        let mut registry = parse_promotion_origin_registry_json(include_str!(
            "../../../testdata/package/npa-mathlib-declaration-baseline/promotion-origins.json"
        ))
        .unwrap();
        let zero = PackageHash::new([0; 32]);
        let target_module = npa_cert::Name::from_dotted("Mathlib.DispatchFixture");
        let revision = PromotionTargetRevision::<PromotionReservedTheorem> {
            target_version: PackageVersion::new("0.1.0"),
            target_source_file_hash: zero,
            target_certificate_file_hash: zero,
            target_certificate_hash: zero,
            target_export_hash: zero,
            target_axiom_report_hash: zero,
            theorems: Vec::new(),
        };
        registry
            .unresolved_legacy_targets
            .push(PromotionLegacyTargetReservation {
                reservation_id: promotion_legacy_target_reservation_id(&target_module, &revision)
                    .unwrap(),
                lifecycle: PromotionLifecycle::Active,
                target_module,
                target_revisions: vec![revision],
                evidence: PromotionEvidence::LegacyAudit {
                    audit_location: PromotionAuditLocation {
                        repository: MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
                        path: PackagePath::new("docs/dispatch-fixture.md"),
                    },
                    audit_file_hash: zero,
                },
            });
        registry.refresh_hash().unwrap();
        let source = registry.canonical_json().unwrap();
        assert!(source.contains(MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA));
        assert!(matches!(
            parse_promotion_origin_registry_versioned(&source),
            Ok(ParsedPromotionOriginRegistry::V1(_))
        ));

        let migrated = migrate_promotion_origin_registry_v1_to_v2(&registry).unwrap();
        assert!(matches!(
            parse_promotion_origin_registry_versioned(&migrated.canonical_json().unwrap()),
            Ok(ParsedPromotionOriginRegistry::V2(_))
        ));
    }
}
