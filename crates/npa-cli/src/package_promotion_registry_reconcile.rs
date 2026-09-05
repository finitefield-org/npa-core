//! Recurring promotion-origin registry reconciliation.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_package::{
    active_catalog_routes, catalog_change_event_id, catalog_change_set_hash, catalog_target_id,
    catalog_target_revision_hash, migrate_promotion_origin_registry_v1_to_v3,
    migrate_promotion_origin_registry_v2_to_v3, package_file_hash,
    parse_catalog_registry_sync_attestation_json,
    validate_catalog_registry_sync_attestation_against_transition, CatalogAddedTarget,
    CatalogAttestationRef, CatalogChangeEvent, CatalogChangeRequestRef, CatalogGovernanceFileRef,
    CatalogLifecycleChange, CatalogRegistryComparison, CatalogRegistryInputIdentity,
    CatalogRegistrySyncAttestation, CatalogRevisedRoute, CatalogTargetEntry, CatalogTargetEvidence,
    CatalogTargetProjection, PackageHash, PackageManifest, PackagePath,
    PromotionDeclarationTargetRevision, PromotionDeclarationTargetTheorem, PromotionOriginEntryV3,
    MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA, MATHLIB_PROMOTION_REGISTRY_PATH,
    PACKAGE_PUBLISH_PLAN_PATH, PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH,
};

use crate::{
    args::{
        PackageAuditCacheMode, PackageChecker, PackageCommonOptions, PackageExportSummaryOptions,
        PackageLockInputMode, PackagePublishPlanOptions,
        PackageReconcilePromotionOriginRegistryOptions, PackageTimingMode,
        PackageValidatePromotionOriginRegistryOptions, PackageVerifierMemoMode,
        PackageVerifyCertsOptions,
    },
    diagnostic::{
        CommandArtifact, CommandDiagnostic, CommandResult, CommandStatus, DiagnosticKind,
    },
    fs::{no_follow_directory::open_absolute_directory, render_package_root},
    generated_artifact_writer::{
        open_package_parent_no_follow, read_package_regular_file_no_follow,
    },
    governance_writer::{
        confined_governance_path, read_governance_artifact,
        replace_governance_artifact_if_unchanged, write_governance_artifact,
        GovernanceOutputPolicy,
    },
    package_api::v1::build_certs_check,
    package_artifacts::{
        load_package_audit_snapshot, PackageGeneratedArtifactReadMode, PACKAGE_AXIOM_REPORT_PATH,
        PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH,
    },
    package_build::run_package_build_certs,
    package_check::run_package_check,
    package_export_summary::run_package_export_summary,
    package_hashes::run_package_check_hashes,
    package_promotion_registry::{
        parse_promotion_origin_registry_versioned, run_package_validate_promotion_origin_registry,
        validate_checked_generated, validate_registry_v3_target, ParsedPromotionOriginRegistry,
    },
    package_promotion_transaction::TargetLock,
    package_publish::run_package_publish_plan,
    package_verify::run_package_verify_certs,
};

const COMMAND: &str = "package reconcile-promotion-origin-registry";
const REASON: &str = "promotion_registry_reconciliation";
const MANIFEST_PATH: &str = "npa-package.toml";

struct PreviousPackageState {
    manifest: PackageManifest,
    projection: CatalogTargetProjection,
    revisions: BTreeMap<String, PromotionDeclarationTargetRevision>,
}

/// Validate and optionally apply one arbitrary older-to-newer catalog transition.
pub fn run_package_reconcile_promotion_origin_registry(
    options: PackageReconcilePromotionOriginRegistryOptions,
) -> CommandResult {
    if let Some(path) = &options.recover {
        return recover(&options.common.root, path);
    }
    let root_display = render_package_root(&options.common.root);
    let Some(previous_root) = options.previous_target_root.as_deref() else {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_missing_input",
            "--previous-target-root",
        );
    };
    let Some(audit_option) = options.audit.as_deref() else {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_missing_input",
            "--audit",
        );
    };
    let Some(out_option) = options.out.as_deref() else {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_missing_input",
            "--out",
        );
    };
    let audit = match governance_path(&options.common.root, audit_option, "--audit", false) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let out = match governance_path(&options.common.root, out_option, "--out", true) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    if audit == out {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_path_invalid",
            "--out",
        );
    }
    let request_path = match options.request.as_deref() {
        Some(path) => match governance_path(&options.common.root, path, "--request", true) {
            Ok(value) => Some(value),
            Err(diagnostic) => {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
            }
        },
        None => None,
    };
    let current_canonical = match fs::canonicalize(&options.common.root) {
        Ok(value) => value,
        Err(_) => return failed(&options.common.root, "package_root_unavailable", "--root"),
    };
    let previous_canonical = match fs::canonicalize(previous_root) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_previous_target_invalid",
                "--previous-target-root",
            )
        }
    };
    if current_canonical == previous_canonical {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_same_root",
            "--previous-target-root",
        );
    }
    let target_lock = match if options.apply {
        TargetLock::acquire(&options.common.root)
    } else {
        TargetLock::acquire_shared(&options.common.root)
    } {
        Ok(lock) => lock,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_concurrent_update",
                "--root",
            )
        }
    };
    if pending_recovery_journal(&options.common.root).is_some() {
        return failed(
            &options.common.root,
            "promotion_recovery_required",
            "target/registry-reconciliation",
        );
    }
    let registry_path = PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH);
    let registry_bytes = match read_governance_artifact(
        &options.common.root,
        &registry_path,
        MATHLIB_PROMOTION_REGISTRY_PATH,
        "promotion_registry_noncanonical",
    ) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let registry_source = match std::str::from_utf8(&registry_bytes) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_noncanonical",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    };
    let parsed = match parse_promotion_origin_registry_versioned(registry_source) {
        Ok(value) => value,
        Err(()) => {
            return failed(
                &options.common.root,
                "promotion_registry_noncanonical",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    };
    let transition_base = parsed.clone();
    let input_schema = registry_schema(&parsed).to_owned();
    let input_registry_hash = registry_self_hash(&parsed);
    let input_file_hash = package_file_hash(&registry_bytes);
    let mut proposed = match parsed {
        ParsedPromotionOriginRegistry::V1(value) => {
            match migrate_promotion_origin_registry_v1_to_v3(&value) {
                Ok(value) => value,
                Err(_) => {
                    return failed(
                        &options.common.root,
                        "promotion_registry_noncanonical",
                        MATHLIB_PROMOTION_REGISTRY_PATH,
                    )
                }
            }
        }
        ParsedPromotionOriginRegistry::V2(value) => {
            match migrate_promotion_origin_registry_v2_to_v3(&value) {
                Ok(value) => value,
                Err(_) => {
                    return failed(
                        &options.common.root,
                        "promotion_registry_noncanonical",
                        MATHLIB_PROMOTION_REGISTRY_PATH,
                    )
                }
            }
        }
        ParsedPromotionOriginRegistry::V3(value) => value,
    };
    let mut old_routes = match active_catalog_routes(&proposed) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_noncanonical",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    };
    let mut gates = immutable_previous_root_gates(previous_root);
    gates.append(&mut root_gates(&options.common.root));
    for gate in gates {
        if gate.status != CommandStatus::Passed {
            return CommandResult::failed(COMMAND, root_display, gate.diagnostics);
        }
    }
    let loaded = match load_snapshot(previous_root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&loaded) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let previous_projection_value = match projection(previous_root, &loaded) {
        Ok(value) => value,
        Err(path) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_projection_invalid",
                path,
            )
        }
    };
    let revisions = match package_revisions(previous_root, &loaded) {
        Ok(value) => value,
        Err(path) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_previous_target_mismatch",
                path,
            )
        }
    };
    let previous = PreviousPackageState {
        manifest: loaded.snapshot.validated.manifest().clone(),
        projection: previous_projection_value,
        revisions,
    };
    let current = match load_snapshot(&options.common.root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&current) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let current_common = PackageCommonOptions {
        root: options.common.root.clone(),
        json: false,
    };
    for gate in [
        run_package_export_summary(PackageExportSummaryOptions {
            common: current_common.clone(),
            out: None,
            check: true,
            timings: PackageTimingMode::Off,
        }),
        run_package_publish_plan(PackagePublishPlanOptions {
            common: current_common,
            check: true,
            timings: PackageTimingMode::Off,
        }),
    ] {
        if gate.status != CommandStatus::Passed {
            return CommandResult::failed(COMMAND, root_display, gate.diagnostics);
        }
    }
    let previous_manifest = &previous.manifest;
    let current_manifest = current.snapshot.validated.manifest();
    if previous_manifest.package != proposed.target_package
        || current_manifest.package != proposed.target_package
        || !version_greater(
            current_manifest.version.as_str(),
            previous_manifest.version.as_str(),
        )
    {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_version_invalid",
            "--previous-target-root",
        );
    }
    let previous_projection = previous.projection.clone();
    let current_projection = match projection(&options.common.root, &current) {
        Ok(value) => value,
        Err(path) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_projection_invalid",
                path,
            )
        }
    };
    let audit_bytes = match read_governance_artifact(
        &options.common.root,
        &audit,
        "--audit",
        "promotion_registry_reconciliation_audit_invalid",
    ) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    if std::str::from_utf8(&audit_bytes).is_err() {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_audit_invalid",
            "--audit",
        );
    }
    let audit_ref = CatalogGovernanceFileRef {
        path: audit,
        file_hash: package_file_hash(&audit_bytes),
    };
    let request = match request_path {
        Some(path) => {
            let bytes = match read_governance_artifact(
                &options.common.root,
                &path,
                "--request",
                "promotion_registry_reconciliation_request_invalid",
            ) {
                Ok(value) => value,
                Err(diagnostic) => {
                    return CommandResult::failed(COMMAND, root_display, vec![*diagnostic])
                }
            };
            let source = match std::str::from_utf8(&bytes) {
                Ok(value) => value,
                Err(_) => {
                    return failed(
                        &options.common.root,
                        "promotion_registry_reconciliation_request_invalid",
                        "--request",
                    )
                }
            };
            let parsed = match npa_package::parse_catalog_registry_change_request_json(source) {
                Ok(value) => value,
                Err(_) => {
                    return failed(
                        &options.common.root,
                        "promotion_registry_reconciliation_request_invalid",
                        "--request",
                    )
                }
            };
            if parsed.previous_version != previous_manifest.version
                || parsed.target_version != current_manifest.version
                || parsed.audit_path != audit_ref.path
                || parsed.audit_file_hash != audit_ref.file_hash
            {
                return failed(
                    &options.common.root,
                    "promotion_registry_reconciliation_request_invalid",
                    "--request",
                );
            }
            let request_hash = parsed.request_hash;
            Some((
                parsed,
                CatalogChangeRequestRef {
                    path,
                    file_hash: package_file_hash(&bytes),
                    request_hash,
                },
            ))
        }
        None => None,
    };
    if let Some(last) = proposed.catalog_change_events.last() {
        if last.previous_target == previous_projection
            && last.target == current_projection
            && last.audit == audit_ref
            && last.request == request.as_ref().map(|(_, reference)| reference.clone())
            && last.attestation.path == out
        {
            let existing_attestation = read_governance_artifact(
                &options.common.root,
                &out,
                "--out",
                "promotion_registry_reconciliation_attestation_invalid",
            )
            .ok();
            if existing_attestation.as_deref().is_some_and(|bytes| {
                parse_catalog_registry_sync_attestation_json(
                    std::str::from_utf8(bytes).unwrap_or_default(),
                )
                .is_ok_and(|attestation| {
                    comparison_rows_for_revisions(
                        &proposed,
                        last,
                        &attestation.input_registry.schema,
                        &previous.revisions,
                        &options.common.root,
                        &current,
                    )
                    .is_some_and(|expected_comparisons| {
                        previous_registry_self_hash(&proposed, &attestation.input_registry.schema)
                            .is_some_and(|expected_registry_hash| {
                                validate_catalog_registry_sync_attestation_against_transition(
                                    &attestation,
                                    last,
                                    expected_registry_hash,
                                    &expected_comparisons,
                                )
                                .is_ok()
                            })
                    })
                })
            }) && validate_registry_v3_target(&options.common.root, &current, &proposed).is_ok()
            {
                let mut result = CommandResult::passed(COMMAND, root_display);
                result.diagnostics.push(CommandDiagnostic::info(
                    DiagnosticKind::PackagePolicy,
                    "already_applied",
                ));
                result.artifacts.push(CommandArtifact {
                    kind: "promotion_origin_registry_v3".to_owned(),
                    path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
                });
                return result;
            }
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_partial_apply",
                out.as_str(),
            );
        }
    }
    let previous_revisions = previous.revisions;
    if old_routes.len() != previous_revisions.len()
        || old_routes.iter().any(|(module, (_, stored))| {
            previous_revisions
                .get(module)
                .is_none_or(|actual| !same_artifacts(stored, actual))
        })
    {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_previous_target_mismatch",
            "$.entries",
        );
    }
    let legacy_incomplete = old_routes
        .iter()
        .filter_map(|(module, (_, revision))| {
            legacy_revision_is_incomplete(revision).then_some(module.clone())
        })
        .collect::<BTreeSet<_>>();
    for (module, (_, revision)) in &mut old_routes {
        if let Some(actual) = previous_revisions.get(module) {
            complete_legacy_revision(revision, actual);
        }
    }
    let current_revisions = match package_revisions(&options.common.root, &current) {
        Ok(value) => value,
        Err(path) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_target_invalid",
                path,
            )
        }
    };
    let removed = old_routes
        .keys()
        .filter(|module| !current_revisions.contains_key(*module))
        .cloned()
        .collect::<Vec<_>>();
    if !removed.is_empty() && request.is_none() {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_request_required",
            &removed[0],
        );
    }
    if let Some((request, _)) = &request {
        let requested_old = request
            .changes
            .iter()
            .flat_map(|change| change.old_modules.iter().map(|name| name.as_dotted()))
            .collect::<Vec<_>>();
        let mut expected_old = removed.clone();
        expected_old.sort();
        let mut requested_old_sorted = requested_old;
        requested_old_sorted.sort();
        let mut requested_new = request
            .changes
            .iter()
            .flat_map(|change| change.new_modules.iter().map(|name| name.as_dotted()))
            .collect::<Vec<_>>();
        requested_new.sort();
        if requested_old_sorted != expected_old
            || requested_old_sorted
                .windows(2)
                .any(|pair| pair[0] == pair[1])
            || requested_new.windows(2).any(|pair| pair[0] == pair[1])
            || requested_new
                .iter()
                .any(|module| old_routes.contains_key(module))
            || request.changes.iter().any(|change| {
                change
                    .new_modules
                    .iter()
                    .any(|module| !current_revisions.contains_key(&module.as_dotted()))
            })
        {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_request_invalid",
                "--request",
            );
        }
    }
    let mut revised_routes = Vec::new();
    for (module, (route, old_revision)) in &old_routes {
        let Some(new_revision) = current_revisions.get(module) else {
            continue;
        };
        if legacy_incomplete.contains(module)
            || !same_complete_artifacts(old_revision, new_revision)
        {
            revised_routes.push(CatalogRevisedRoute {
                owner_kind: route.owner_kind.clone(),
                owner_id: route.owner_id,
                target_module: route.target_module.clone(),
                previous_revision_hash: match catalog_target_revision_hash(old_revision) {
                    Ok(value) => value,
                    Err(_) => {
                        return failed(
                            &options.common.root,
                            "promotion_registry_noncanonical",
                            module,
                        )
                    }
                },
                target_revision: new_revision.clone(),
            });
        }
    }
    revised_routes.sort();
    let zero = PackageHash::new([0; 32]);
    let mut added_targets = Vec::new();
    for (module, revision) in current_revisions
        .iter()
        .filter(|(module, _)| !old_routes.contains_key(*module))
    {
        let target_module = npa_cert::Name::from_dotted(module);
        let owner_id = match catalog_target_id(&target_module, revision) {
            Ok(value) => value,
            Err(_) => {
                return failed(
                    &options.common.root,
                    "promotion_registry_reconciliation_target_invalid",
                    module,
                )
            }
        };
        proposed
            .entries
            .push(PromotionOriginEntryV3::CatalogTargetV1(Box::new(
                CatalogTargetEntry {
                    catalog_target_id: owner_id,
                    lifecycle: "active".to_owned(),
                    introduced_version: current_manifest.version.clone(),
                    target_module: target_module.clone(),
                    first_revision: revision.clone(),
                    evidence: CatalogTargetEvidence {
                        kind: "catalog_registry_sync_v1".to_owned(),
                        audit_path: audit_ref.path.clone(),
                        audit_file_hash: audit_ref.file_hash,
                        change_set_hash: zero,
                    },
                },
            )));
        added_targets.push(CatalogAddedTarget {
            owner_kind: "catalog_target_v1".to_owned(),
            owner_id,
            target_module,
            first_revision_hash: match catalog_target_revision_hash(revision) {
                Ok(value) => value,
                Err(_) => {
                    return failed(
                        &options.common.root,
                        "promotion_registry_reconciliation_target_invalid",
                        module,
                    )
                }
            },
        });
    }
    proposed
        .entries
        .sort_by_key(PromotionOriginEntryV3::owner_id);
    added_targets.sort();
    let lifecycle_changes = request
        .as_ref()
        .map(|(request, _)| {
            request
                .changes
                .iter()
                .map(|change| {
                    let old_routes = change
                        .old_modules
                        .iter()
                        .map(|module| {
                            old_routes
                                .get(&module.as_dotted())
                                .map(|(route, _)| route.clone())
                                .ok_or(())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let new_routes = change
                        .new_modules
                        .iter()
                        .map(|module| {
                            added_targets
                                .iter()
                                .find(|row| row.target_module == *module)
                                .map(|row| npa_package::CatalogRouteRef {
                                    owner_kind: row.owner_kind.clone(),
                                    owner_id: row.owner_id,
                                    target_module: row.target_module.clone(),
                                })
                                .ok_or(())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(CatalogLifecycleChange {
                        kind: change.kind.clone(),
                        effective_version: current_manifest.version.clone(),
                        old_routes,
                        new_routes,
                    })
                })
                .collect::<Result<Vec<_>, ()>>()
        })
        .transpose();
    let mut lifecycle_changes = match lifecycle_changes {
        Ok(Some(value)) => value,
        Ok(None) => Vec::new(),
        Err(()) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_request_invalid",
                "--request",
            )
        }
    };
    lifecycle_changes.sort();
    if revised_routes.is_empty()
        && added_targets.is_empty()
        && lifecycle_changes.is_empty()
        && request.is_none()
    {
        if let Err(diagnostic) =
            validate_registry_v3_target(&options.common.root, &current, &proposed)
        {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
        let mut result = CommandResult::passed(COMMAND, root_display);
        result.diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::PackagePolicy,
                "promotion_registry_no_catalog_change",
            )
            .with_actual_value(format!(
                "previous_version={};target_version={};registry_unchanged=true",
                previous_manifest.version.as_str(),
                current_manifest.version.as_str()
            )),
        );
        result.artifacts.push(CommandArtifact {
            kind: "promotion_origin_registry_v3".to_owned(),
            path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
        });
        return result;
    }
    proposed.generation = match proposed.generation.checked_add(1) {
        Some(value) => value,
        None => {
            return failed(
                &options.common.root,
                "promotion_registry_noncanonical",
                "$.generation",
            )
        }
    };
    let mut event = CatalogChangeEvent {
        event_id: zero,
        kind: "catalog_registry_sync_v1".to_owned(),
        input_registry_hash: input_file_hash,
        change_set_hash: zero,
        previous_target: previous_projection.clone(),
        target: current_projection.clone(),
        audit: audit_ref.clone(),
        request: request.as_ref().map(|(_, reference)| reference.clone()),
        attestation: CatalogAttestationRef {
            path: out.clone(),
            payload_hash: zero,
        },
        revised_routes,
        added_targets,
        lifecycle_changes,
    };
    event.change_set_hash = match catalog_change_set_hash(&event) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_change_set_invalid",
                "$.change_set_hash",
            )
        }
    };
    for entry in &mut proposed.entries {
        if let PromotionOriginEntryV3::CatalogTargetV1(entry) = entry {
            if event
                .added_targets
                .iter()
                .any(|row| row.owner_id == entry.catalog_target_id)
            {
                entry.evidence.change_set_hash = event.change_set_hash;
            }
        }
    }
    let comparisons = comparison_rows(&old_routes, &current_revisions, &event);
    let expected_comparisons = comparisons.clone();
    let unchanged_count = old_routes
        .len()
        .saturating_sub(event.revised_routes.len())
        .saturating_sub(
            event
                .lifecycle_changes
                .iter()
                .map(|change| change.old_routes.len())
                .sum(),
        );
    let mut attestation_value = CatalogRegistrySyncAttestation {
        schema: MATHLIB_CATALOG_REGISTRY_SYNC_ATTESTATION_SCHEMA.to_owned(),
        command: COMMAND.to_owned(),
        input_registry: CatalogRegistryInputIdentity {
            schema: input_schema,
            file_hash: input_file_hash,
            registry_hash: input_registry_hash,
        },
        previous_target: event.previous_target.clone(),
        target: event.target.clone(),
        change_set_hash: event.change_set_hash,
        audit: event.audit.clone(),
        request: event.request.clone(),
        comparisons,
        unchanged_count: unchanged_count as u64,
        revised_count: event.revised_routes.len() as u64,
        added_count: event.added_targets.len() as u64,
        lifecycle_change_count: event.lifecycle_changes.len() as u64,
        gates: CatalogRegistrySyncAttestation::required_gates(),
        attestation_hash: zero,
        proof_evidence: false,
    };
    if attestation_value.refresh_hash().is_err() {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_attestation_invalid",
            out.as_str(),
        );
    }
    event.attestation.payload_hash = attestation_value.attestation_hash;
    event.event_id = match catalog_change_event_id(&event) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_event_invalid",
                "$.event_id",
            )
        }
    };
    proposed.catalog_change_events.push(event);
    if proposed.refresh_hash().is_err() {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_event_invalid",
            "$.registry_hash",
        );
    }
    if let Err(diagnostic) = validate_registry_v3_target(&options.common.root, &current, &proposed)
    {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let transition_valid = match &transition_base {
        ParsedPromotionOriginRegistry::V1(previous) => {
            npa_package::validate_promotion_origin_registry_v1_to_v3_reconciliation_with_previous_hashes(
                previous,
                &proposed,
                &previous_revision_hashes(&old_routes),
            )
            .is_ok()
        }
        ParsedPromotionOriginRegistry::V2(previous) => {
            npa_package::validate_promotion_origin_registry_v2_to_v3_reconciliation_with_previous_hashes(
                previous,
                &proposed,
                &previous_revision_hashes(&old_routes),
            )
            .is_ok()
        }
        ParsedPromotionOriginRegistry::V3(previous) => {
            npa_package::validate_promotion_origin_registry_v3_transition_with_previous_hashes(
                previous,
                &proposed,
                &previous_revision_hashes(&old_routes),
            )
            .is_ok()
        }
    };
    if !transition_valid {
        return failed(
            &options.common.root,
            "promotion_registry_transition_not_append_only",
            MATHLIB_PROMOTION_REGISTRY_PATH,
        );
    }
    let proposed_json = match proposed.canonical_json() {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_event_invalid",
                "$",
            )
        }
    };
    let attestation = match attestation_value.canonical_json() {
        Ok(value) => value,
        Err(_) => {
            return failed(
                &options.common.root,
                "promotion_registry_reconciliation_attestation_invalid",
                out.as_str(),
            )
        }
    };
    if proposed.catalog_change_events.last().is_none_or(|event| {
        validate_catalog_registry_sync_attestation_against_transition(
            &attestation_value,
            event,
            input_registry_hash,
            &expected_comparisons,
        )
        .is_err()
    }) {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_attestation_invalid",
            out.as_str(),
        );
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.extend([
        CommandArtifact {
            kind: "promotion_origin_registry_input".to_owned(),
            path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
        },
        CommandArtifact {
            kind: "catalog_registry_sync_attestation".to_owned(),
            path: out.as_str().to_owned(),
        },
        CommandArtifact {
            kind: "promotion_origin_registry_v3".to_owned(),
            path: MATHLIB_PROMOTION_REGISTRY_PATH.to_owned(),
        },
    ]);
    if !options.apply {
        result.diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "dry_run")
                .with_actual_value(npa_package::format_package_hash(&proposed.registry_hash)),
        );
        return result;
    }
    if !inputs_still_match(
        previous_root,
        &options.common.root,
        &previous_projection,
        &current_projection,
        &previous_revisions,
        &current_revisions,
        &audit_ref,
        &audit_bytes,
        request.as_ref(),
        &registry_path,
        &registry_bytes,
    ) {
        return failed(
            &options.common.root,
            "promotion_registry_concurrent_update",
            "--root",
        );
    }
    let Some(event_id) = proposed
        .catalog_change_events
        .last()
        .map(|event| event.event_id)
    else {
        return failed(
            &options.common.root,
            "promotion_registry_reconciliation_event_invalid",
            "$.catalog_change_events",
        );
    };
    let journal = PackagePath::new(format!(
        "target/registry-reconciliation/{}.json",
        npa_package::format_package_hash(&event_id).trim_start_matches("sha256:")
    ));
    let journal_bytes = recovery_journal_json(
        &options.common.root,
        &out,
        &registry_bytes,
        attestation.as_bytes(),
        proposed_json.as_bytes(),
    );
    if let Err(diagnostic) = write_governance_artifact(
        &options.common.root,
        &journal,
        journal_bytes.as_bytes(),
        GovernanceOutputPolicy::CreateOrIdentical,
        REASON,
    ) {
        return CommandResult::failed(
            COMMAND,
            render_package_root(&options.common.root),
            vec![*diagnostic],
        );
    }
    if let Err(diagnostic) = write_governance_artifact(
        &options.common.root,
        &out,
        attestation.as_bytes(),
        GovernanceOutputPolicy::CreateOrIdentical,
        REASON,
    ) {
        return recovery_required(&options.common.root, diagnostic, &journal);
    }
    if let Err(diagnostic) = replace_governance_artifact_if_unchanged(
        &options.common.root,
        &registry_path,
        proposed_json.as_bytes(),
        &registry_bytes,
        REASON,
    ) {
        return recovery_required(&options.common.root, diagnostic, &journal);
    }
    let validation = run_package_validate_promotion_origin_registry(
        PackageValidatePromotionOriginRegistryOptions {
            common: options.common.clone(),
            source_roots: Vec::new(),
            previous_registry: None,
        },
    );
    if validation.status != CommandStatus::Passed {
        let mut diagnostics = validation.diagnostics;
        diagnostics.push(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "promotion_recovery_required")
                .with_path(journal.as_str()),
        );
        return CommandResult::failed(
            COMMAND,
            render_package_root(&options.common.root),
            diagnostics,
        );
    }
    let _ = remove_recovery_journal_if_unchanged(
        &options.common.root,
        &journal,
        journal_bytes.as_bytes(),
        &target_lock,
    );
    result
}

fn root_gates(root: &Path) -> Vec<CommandResult> {
    let common = PackageCommonOptions {
        root: root.to_path_buf(),
        json: false,
    };
    vec![
        run_package_check(common.clone()),
        run_package_check_hashes(common.clone()),
        run_package_build_certs(build_certs_check(common.clone())),
        run_package_verify_certs(PackageVerifyCertsOptions {
            common,
            checker: PackageChecker::Reference,
            changed: false,
            modules: Vec::new(),
            base: None,
            modules_requested: false,
            audit_cache: PackageAuditCacheMode::Off,
            verifier_memo: PackageVerifierMemoMode::Off,
            jobs: 1,
            external: None,
            timings: PackageTimingMode::Off,
            package_lock_mode: PackageLockInputMode::CheckedFile,
        }),
    ]
}

/// Validate an immutable previous catalog snapshot without rebuilding its
/// historical authoring source. Exact source bytes still have to match their
/// manifest hashes, while package-lock imports, certificates, generated
/// identities, and reference verification remain authoritative.
fn immutable_previous_root_gates(root: &Path) -> Vec<CommandResult> {
    let common = PackageCommonOptions {
        root: root.to_path_buf(),
        json: false,
    };
    vec![
        run_package_check_hashes(common.clone()),
        run_package_verify_certs(PackageVerifyCertsOptions {
            common,
            checker: PackageChecker::Reference,
            changed: false,
            modules: Vec::new(),
            base: None,
            modules_requested: false,
            audit_cache: PackageAuditCacheMode::Off,
            verifier_memo: PackageVerifierMemoMode::Off,
            jobs: 1,
            external: None,
            timings: PackageTimingMode::Off,
            package_lock_mode: PackageLockInputMode::CheckedFile,
        }),
    ]
}

fn load_snapshot(
    root: &Path,
) -> Result<crate::package_artifacts::LoadedPackageAuditSnapshot, CommandResult> {
    load_package_audit_snapshot(
        root,
        COMMAND,
        PackageGeneratedArtifactReadMode {
            axiom_report: true,
            theorem_index: true,
            theorem_premise_report: false,
        },
        PackageArtifactReferenceSummaryMode::Include,
    )
}

fn projection(
    root: &Path,
    loaded: &crate::package_artifacts::LoadedPackageAuditSnapshot,
) -> Result<CatalogTargetProjection, String> {
    projection_for_manifest(root, loaded.snapshot.validated.manifest())
}

fn projection_for_manifest(
    root: &Path,
    manifest: &PackageManifest,
) -> Result<CatalogTargetProjection, String> {
    Ok(CatalogTargetProjection {
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        manifest_file_hash: hash_file(root, MANIFEST_PATH)?,
        package_lock_file_hash: hash_file(root, PACKAGE_LOCK_PATH)?,
        axiom_report_file_hash: hash_file(root, PACKAGE_AXIOM_REPORT_PATH)?,
        theorem_index_file_hash: hash_file(root, PACKAGE_THEOREM_INDEX_PATH)?,
        export_summary_file_hash: hash_file(root, PACKAGE_VERIFIED_EXPORT_SUMMARY_PATH)?,
        publish_plan_file_hash: hash_file(root, PACKAGE_PUBLISH_PLAN_PATH)?,
    })
}

fn package_revisions(
    root: &Path,
    loaded: &crate::package_artifacts::LoadedPackageAuditSnapshot,
) -> Result<BTreeMap<String, PromotionDeclarationTargetRevision>, String> {
    let index = loaded
        .snapshot
        .project_theorem_index()
        .map_err(|_| PACKAGE_THEOREM_INDEX_PATH)?;
    loaded
        .snapshot
        .validated
        .manifest()
        .modules
        .iter()
        .map(|module| {
            let meta = module
                .meta
                .as_ref()
                .map_or(Ok(PackageHash::new([0; 32])), |path| {
                    hash_file(root, path.as_str())
                })?;
            let replay = module
                .replay
                .as_ref()
                .map_or(Ok(PackageHash::new([0; 32])), |path| {
                    hash_file(root, path.as_str())
                })?;
            let theorems = index
                .entries
                .iter()
                .filter(|row| {
                    row.global_ref.module == module.module
                        && row.kind == npa_package::PackageTheoremIndexKind::Theorem
                })
                .map(|row| PromotionDeclarationTargetTheorem {
                    target_name: row.global_ref.name.clone(),
                    statement_hash: row.statement.core_hash,
                })
                .collect();
            let source_hash = hash_file(root, module.source.as_str())?;
            let certificate_file_hash = hash_file(root, module.certificate.as_str())?;
            if source_hash != module.expected_source_hash {
                return Err(module.source.as_str().to_owned());
            }
            if certificate_file_hash != module.expected_certificate_file_hash {
                return Err(module.certificate.as_str().to_owned());
            }
            Ok((
                module.module.as_dotted(),
                PromotionDeclarationTargetRevision {
                    target_version: loaded.snapshot.validated.manifest().version.clone(),
                    target_source_file_hash: source_hash,
                    target_meta_file_hash: meta,
                    target_replay_file_hash: replay,
                    target_certificate_file_hash: module.expected_certificate_file_hash,
                    target_certificate_hash: module.expected_certificate_hash,
                    target_export_hash: module.expected_export_hash,
                    target_axiom_report_hash: module.expected_axiom_report_hash,
                    theorems,
                },
            ))
        })
        .collect()
}

fn same_artifacts(
    left: &PromotionDeclarationTargetRevision,
    right: &PromotionDeclarationTargetRevision,
) -> bool {
    left.target_source_file_hash == right.target_source_file_hash
        && (left.target_meta_file_hash == right.target_meta_file_hash
            || left.target_meta_file_hash == PackageHash::new([0; 32]))
        && (left.target_replay_file_hash == right.target_replay_file_hash
            || left.target_replay_file_hash == PackageHash::new([0; 32]))
        && left.target_certificate_file_hash == right.target_certificate_file_hash
        && left.target_certificate_hash == right.target_certificate_hash
        && left.target_export_hash == right.target_export_hash
        && left.target_axiom_report_hash == right.target_axiom_report_hash
        && left.theorems == right.theorems
}

fn same_complete_artifacts(
    left: &PromotionDeclarationTargetRevision,
    right: &PromotionDeclarationTargetRevision,
) -> bool {
    left.target_source_file_hash == right.target_source_file_hash
        && left.target_meta_file_hash == right.target_meta_file_hash
        && left.target_replay_file_hash == right.target_replay_file_hash
        && left.target_certificate_file_hash == right.target_certificate_file_hash
        && left.target_certificate_hash == right.target_certificate_hash
        && left.target_export_hash == right.target_export_hash
        && left.target_axiom_report_hash == right.target_axiom_report_hash
        && left.theorems == right.theorems
}

fn legacy_revision_is_incomplete(revision: &PromotionDeclarationTargetRevision) -> bool {
    let zero = PackageHash::new([0; 32]);
    revision.target_meta_file_hash == zero || revision.target_replay_file_hash == zero
}

fn complete_legacy_revision(
    stored: &mut PromotionDeclarationTargetRevision,
    actual: &PromotionDeclarationTargetRevision,
) {
    let zero = PackageHash::new([0; 32]);
    if stored.target_meta_file_hash == zero {
        stored.target_meta_file_hash = actual.target_meta_file_hash;
    }
    if stored.target_replay_file_hash == zero {
        stored.target_replay_file_hash = actual.target_replay_file_hash;
    }
}

fn previous_revision_hashes(
    routes: &BTreeMap<
        String,
        (
            npa_package::CatalogRouteRef,
            PromotionDeclarationTargetRevision,
        ),
    >,
) -> BTreeMap<String, PackageHash> {
    routes
        .iter()
        .filter_map(|(module, (_, revision))| {
            catalog_target_revision_hash(revision)
                .ok()
                .map(|hash| (module.clone(), hash))
        })
        .collect()
}

fn comparison_rows_for_revisions(
    registry: &npa_package::PromotionOriginRegistryV3,
    event: &CatalogChangeEvent,
    input_schema: &str,
    previous_revisions: &BTreeMap<String, PromotionDeclarationTargetRevision>,
    current_root: &Path,
    current: &crate::package_artifacts::LoadedPackageAuditSnapshot,
) -> Option<Vec<CatalogRegistryComparison>> {
    let Ok(current) = package_revisions(current_root, current) else {
        return None;
    };
    let previous_registry = reconstruct_previous_registry(registry, input_schema)?;
    let Ok(previous_registry) = registry_as_v3(&previous_registry) else {
        return None;
    };
    let Ok(mut old) = active_catalog_routes(&previous_registry) else {
        return None;
    };
    if old.len() != previous_revisions.len()
        || old.iter().any(|(module, (_, stored))| {
            previous_revisions
                .get(module)
                .is_none_or(|actual| !same_artifacts(stored, actual))
        })
    {
        return None;
    }
    for (module, (_, revision)) in &mut old {
        complete_legacy_revision(revision, previous_revisions.get(module)?);
    }
    Some(comparison_rows(&old, &current, event))
}

fn hash_file(root: &Path, path: &str) -> Result<PackageHash, String> {
    let logical = PackagePath::new(path);
    read_package_regular_file_no_follow(root, &logical)
        .map(|bytes| package_file_hash(&bytes))
        .map_err(|_| path.to_owned())
}

fn governance_path(
    root: &Path,
    raw: &Path,
    field: &str,
    json: bool,
) -> Result<PackagePath, Box<CommandDiagnostic>> {
    let raw = raw.to_str().ok_or_else(|| {
        Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                format!("{REASON}_path_invalid"),
            )
            .with_path(field),
        )
    })?;
    let path = PackagePath::new(raw);
    if !raw.starts_with("docs/promotion/")
        || (json && !raw.ends_with(".json"))
        || raw == MATHLIB_PROMOTION_REGISTRY_PATH
    {
        return Err(Box::new(
            CommandDiagnostic::error(
                DiagnosticKind::GeneratedArtifact,
                format!("{REASON}_path_invalid"),
            )
            .with_path(field),
        ));
    }
    confined_governance_path(root, &path, field, &format!("{REASON}_path_invalid"))?;
    Ok(path)
}

fn pending_recovery_journal(root: &Path) -> Option<std::path::PathBuf> {
    let directory = open_absolute_directory(root, false)
        .ok()?
        .open_or_create_directory(std::ffi::OsStr::new("target"), false)
        .ok()?
        .open_or_create_directory(std::ffi::OsStr::new("registry-reconciliation"), false)
        .ok()?;
    directory.entry_names().ok()?.into_iter().find_map(|name| {
        (Path::new(&name).extension() == Some(std::ffi::OsStr::new("json"))
            && directory
                .open_regular_file(&name)
                .is_ok_and(|file| file.is_some()))
        .then(|| root.join("target/registry-reconciliation").join(name))
    })
}

fn remove_recovery_journal_if_unchanged(
    root: &Path,
    path: &PackagePath,
    expected: &[u8],
    target_lock: &TargetLock,
) -> std::io::Result<()> {
    let (directory, leaf) = open_package_parent_no_follow(root, path, false)?;
    let mut file = directory
        .open_regular_file(&leaf)?
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "journal unavailable"))?;
    let identity = crate::fs::no_follow_directory::regular_file_identity(&file)?;
    use std::io::Read as _;
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take((MAX_RECOVERY_JOURNAL_BYTES as u64) + 1)
        .read_to_end(&mut bytes)?;
    if bytes != expected || bytes.len() > MAX_RECOVERY_JOURNAL_BYTES {
        return Err(std::io::Error::other("recovery journal changed"));
    }
    let current = directory
        .open_regular_file(&leaf)?
        .ok_or_else(|| std::io::Error::other("recovery journal disappeared"))?;
    if crate::fs::no_follow_directory::regular_file_identity(&current)? != identity {
        return Err(std::io::Error::other("recovery journal identity changed"));
    }
    target_lock.remove_regular_file_under_lock(&directory, &leaf, identity)?;
    directory.sync_all()
}

#[allow(clippy::too_many_arguments)]
fn inputs_still_match(
    previous_root: &Path,
    current_root: &Path,
    previous_projection: &CatalogTargetProjection,
    current_projection: &CatalogTargetProjection,
    previous_revisions: &BTreeMap<String, PromotionDeclarationTargetRevision>,
    current_revisions: &BTreeMap<String, PromotionDeclarationTargetRevision>,
    audit: &CatalogGovernanceFileRef,
    audit_bytes: &[u8],
    request: Option<&(
        npa_package::CatalogRegistryChangeRequest,
        CatalogChangeRequestRef,
    )>,
    registry_path: &PackagePath,
    registry_bytes: &[u8],
) -> bool {
    let current_audit = read_package_regular_file_no_follow(current_root, &audit.path).ok();
    if read_package_regular_file_no_follow(current_root, registry_path)
        .ok()
        .as_deref()
        != Some(registry_bytes)
        || current_audit.as_deref() != Some(audit_bytes)
    {
        return false;
    }
    if let Some((expected, reference)) = request {
        let Some(bytes) = read_package_regular_file_no_follow(current_root, &reference.path).ok()
        else {
            return false;
        };
        let parsed = std::str::from_utf8(&bytes).ok().and_then(|source| {
            npa_package::parse_catalog_registry_change_request_json(source).ok()
        });
        if package_file_hash(&bytes) != reference.file_hash || parsed.as_ref() != Some(expected) {
            return false;
        }
    }
    let Ok(current) = load_snapshot(current_root) else {
        return false;
    };
    let Ok(previous) = load_snapshot(previous_root) else {
        return false;
    };
    let previous_matches = projection(previous_root, &previous).ok().as_ref()
        == Some(previous_projection)
        && package_revisions(previous_root, &previous).ok().as_ref() == Some(previous_revisions);
    previous_matches
        && projection(current_root, &current).ok().as_ref() == Some(current_projection)
        && package_revisions(current_root, &current).ok().as_ref() == Some(current_revisions)
}

fn comparison_rows(
    old_routes: &BTreeMap<
        String,
        (
            npa_package::CatalogRouteRef,
            PromotionDeclarationTargetRevision,
        ),
    >,
    current: &BTreeMap<String, PromotionDeclarationTargetRevision>,
    event: &CatalogChangeEvent,
) -> Vec<CatalogRegistryComparison> {
    let mut modules = old_routes
        .keys()
        .chain(current.keys())
        .cloned()
        .collect::<Vec<_>>();
    modules.sort();
    modules.dedup();
    modules
        .into_iter()
        .map(|module| {
            let old = old_routes.get(&module);
            let new = current.get(&module);
            let revised = event
                .revised_routes
                .iter()
                .find(|row| row.target_module.as_dotted() == module);
            let added = event
                .added_targets
                .iter()
                .find(|row| row.target_module.as_dotted() == module);
            let lifecycle = event.lifecycle_changes.iter().find(|change| {
                change
                    .old_routes
                    .iter()
                    .any(|route| route.target_module.as_dotted() == module)
            });
            let status = if let Some(change) = lifecycle {
                match change.kind.as_str() {
                    "rename" => "renamed",
                    "replacement" => "replaced",
                    "split" => "split",
                    "merge" => "merged",
                    _ => "retired",
                }
            } else if revised.is_some() {
                "revision_appended"
            } else if added.is_some() {
                "catalog_target_added"
            } else {
                "unchanged"
            };
            let old_revision_hash =
                old.and_then(|(_, revision)| catalog_target_revision_hash(revision).ok());
            let new_revision_hash = if status == "unchanged" {
                old_revision_hash
            } else {
                revised
                    .map(|row| &row.target_revision)
                    .or(new)
                    .and_then(|revision| catalog_target_revision_hash(revision).ok())
            };
            let owner_id = old
                .map(|(route, _)| route.owner_id)
                .or_else(|| added.map(|row| row.owner_id));
            CatalogRegistryComparison {
                module: npa_cert::Name::from_dotted(module),
                status: status.to_owned(),
                owner_id,
                old_revision_hash,
                new_revision_hash,
            }
        })
        .collect()
}

fn registry_schema(registry: &ParsedPromotionOriginRegistry) -> &str {
    match registry {
        ParsedPromotionOriginRegistry::V1(value) => &value.schema,
        ParsedPromotionOriginRegistry::V2(value) => &value.schema,
        ParsedPromotionOriginRegistry::V3(value) => &value.schema,
    }
}

fn registry_self_hash(registry: &ParsedPromotionOriginRegistry) -> PackageHash {
    match registry {
        ParsedPromotionOriginRegistry::V1(value) => value.registry_hash,
        ParsedPromotionOriginRegistry::V2(value) => value.registry_hash,
        ParsedPromotionOriginRegistry::V3(value) => value.registry_hash,
    }
}

fn previous_registry_self_hash(
    registry: &npa_package::PromotionOriginRegistryV3,
    input_schema: &str,
) -> Option<PackageHash> {
    let previous = reconstruct_previous_registry(registry, input_schema)?;
    let file_hash = match &previous {
        ParsedPromotionOriginRegistry::V1(value) => {
            package_file_hash(value.canonical_json().ok()?.as_bytes())
        }
        ParsedPromotionOriginRegistry::V2(value) => {
            package_file_hash(value.canonical_json().ok()?.as_bytes())
        }
        ParsedPromotionOriginRegistry::V3(value) => {
            package_file_hash(value.canonical_json().ok()?.as_bytes())
        }
    };
    (registry.catalog_change_events.last()?.input_registry_hash == file_hash)
        .then(|| registry_self_hash(&previous))
}

fn reconstruct_previous_registry(
    registry: &npa_package::PromotionOriginRegistryV3,
    input_schema: &str,
) -> Option<ParsedPromotionOriginRegistry> {
    let event = registry.catalog_change_events.last()?;
    let added = event
        .added_targets
        .iter()
        .map(|row| row.owner_id)
        .collect::<BTreeSet<_>>();
    let mut previous = registry.clone();
    previous.catalog_change_events.pop();
    previous.generation = previous.generation.checked_sub(1)?;
    previous
        .entries
        .retain(|entry| !added.contains(&entry.owner_id()));
    previous.refresh_hash().ok()?;
    match input_schema {
        npa_package::MATHLIB_PROMOTION_ORIGIN_REGISTRY_V3_SCHEMA => {
            Some(ParsedPromotionOriginRegistry::V3(previous))
        }
        npa_package::MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA => {
            let mut v2 = npa_package::PromotionOriginRegistryV2 {
                schema: npa_package::MATHLIB_PROMOTION_ORIGIN_REGISTRY_V2_SCHEMA.to_owned(),
                registry_id: previous.registry_id,
                registry_version: 2,
                generation: previous.generation,
                target_package: previous.target_package,
                entries: previous
                    .entries
                    .into_iter()
                    .filter_map(|entry| match entry {
                        PromotionOriginEntryV3::SourceV2(entry) => Some(entry),
                        PromotionOriginEntryV3::CatalogTargetV1(_) => None,
                    })
                    .collect(),
                unresolved_legacy_targets: previous.unresolved_legacy_targets,
                registry_hash: PackageHash::new([0; 32]),
                proof_evidence: false,
            };
            v2.refresh_hash().ok()?;
            Some(ParsedPromotionOriginRegistry::V2(v2))
        }
        npa_package::MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA => {
            let entries = previous
                .entries
                .into_iter()
                .map(|entry| match entry {
                    PromotionOriginEntryV3::SourceV2(
                        npa_package::PromotionOriginEntryV2::WholeModuleV1(entry),
                    ) => Some(*entry),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            let mut v1 = npa_package::PromotionOriginRegistry {
                schema: npa_package::MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
                registry_id: previous.registry_id,
                registry_version: 1,
                generation: previous.generation,
                target_package: previous.target_package,
                entries,
                unresolved_legacy_targets: previous.unresolved_legacy_targets,
                registry_hash: PackageHash::new([0; 32]),
                proof_evidence: false,
            };
            v1.refresh_hash().ok()?;
            Some(ParsedPromotionOriginRegistry::V1(v1))
        }
        _ => None,
    }
}

fn registry_as_v3(
    registry: &ParsedPromotionOriginRegistry,
) -> Result<npa_package::PromotionOriginRegistryV3, ()> {
    match registry {
        ParsedPromotionOriginRegistry::V1(value) => {
            migrate_promotion_origin_registry_v1_to_v3(value).map_err(|_| ())
        }
        ParsedPromotionOriginRegistry::V2(value) => {
            migrate_promotion_origin_registry_v2_to_v3(value).map_err(|_| ())
        }
        ParsedPromotionOriginRegistry::V3(value) => Ok(value.clone()),
    }
}

fn transition_comparisons(
    previous: &ParsedPromotionOriginRegistry,
    proposed: &npa_package::PromotionOriginRegistryV3,
    event: &CatalogChangeEvent,
) -> Result<Vec<CatalogRegistryComparison>, ()> {
    let previous = registry_as_v3(previous)?;
    let old = active_catalog_routes(&previous).map_err(|_| ())?;
    let new = active_catalog_routes(proposed).map_err(|_| ())?;
    let current = new
        .into_iter()
        .map(|(module, (_, revision))| (module, revision))
        .collect::<BTreeMap<_, _>>();
    let mut comparisons = comparison_rows(&old, &current, event);
    for revised in &event.revised_routes {
        if let Some(row) = comparisons
            .iter_mut()
            .find(|row| row.module == revised.target_module)
        {
            row.old_revision_hash = Some(revised.previous_revision_hash);
        }
    }
    Ok(comparisons)
}

fn valid_transition(
    previous: &ParsedPromotionOriginRegistry,
    proposed: &npa_package::PromotionOriginRegistryV3,
    previous_revision_hashes: &BTreeMap<String, PackageHash>,
) -> bool {
    match previous {
        ParsedPromotionOriginRegistry::V1(value) => {
            npa_package::validate_promotion_origin_registry_v1_to_v3_reconciliation_with_previous_hashes(
                value,
                proposed,
                previous_revision_hashes,
            )
            .is_ok()
        }
        ParsedPromotionOriginRegistry::V2(value) => {
            npa_package::validate_promotion_origin_registry_v2_to_v3_reconciliation_with_previous_hashes(
                value,
                proposed,
                previous_revision_hashes,
            )
            .is_ok()
        }
        ParsedPromotionOriginRegistry::V3(value) => {
            npa_package::validate_promotion_origin_registry_v3_transition_with_previous_hashes(
                value,
                proposed,
                previous_revision_hashes,
            )
            .is_ok()
        }
    }
}

fn version_greater(current: &str, previous: &str) -> bool {
    let parse = |value: &str| {
        let parts = value
            .split('.')
            .map(str::parse::<u64>)
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        (parts.len() == 3).then(|| (parts[0], parts[1], parts[2]))
    };
    parse(current)
        .zip(parse(previous))
        .is_some_and(|(current, previous)| current > previous)
}

const RECOVERY_JOURNAL_SCHEMA: &str = "npa.mathlib.catalog_registry_recovery.v2";
const RECOVERY_JOURNAL_DOMAIN: &[u8] = b"NPA-MATHLIB-CATALOG-REGISTRY-RECOVERY-v2\0";
const MAX_RECOVERY_JOURNAL_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
struct RecoveryJournal {
    legacy_v1: bool,
    root_hash: PackageHash,
    out: PackagePath,
    old_registry_file_hash: PackageHash,
    new_registry_file_hash: PackageHash,
    attestation_file_hash: PackageHash,
    old_registry: Vec<u8>,
    attestation: Vec<u8>,
    registry: Vec<u8>,
    journal_hash: PackageHash,
}

fn recovery_journal_json(
    root: &Path,
    out: &PackagePath,
    old_registry: &[u8],
    attestation: &[u8],
    registry: &[u8],
) -> String {
    let root_hash = fs::canonicalize(root)
        .map(|path| package_file_hash(path.to_string_lossy().as_bytes()))
        .unwrap_or(PackageHash::new([0; 32]));
    let mut journal = RecoveryJournal {
        legacy_v1: false,
        root_hash,
        out: out.clone(),
        old_registry_file_hash: package_file_hash(old_registry),
        new_registry_file_hash: package_file_hash(registry),
        attestation_file_hash: package_file_hash(attestation),
        old_registry: old_registry.to_vec(),
        attestation: attestation.to_vec(),
        registry: registry.to_vec(),
        journal_hash: PackageHash::new([0; 32]),
    };
    journal.journal_hash = recovery_journal_hash(&journal);
    recovery_journal_canonical_json(&journal)
}

fn recovery_journal_canonical_json(journal: &RecoveryJournal) -> String {
    format!(
        concat!(
            "{{\"schema\":\"{}\",\"root_hash\":\"{}\",\"out_path_hex\":\"{}\",",
            "\"old_registry_file_hash\":\"{}\",\"new_registry_file_hash\":\"{}\",",
            "\"attestation_file_hash\":\"{}\",\"old_registry_hex\":\"{}\",",
            "\"attestation_hex\":\"{}\",\"registry_hex\":\"{}\",\"journal_hash\":\"{}\",",
            "\"proof_evidence\":false}}\n"
        ),
        RECOVERY_JOURNAL_SCHEMA,
        npa_package::format_package_hash(&journal.root_hash),
        encode_hex(journal.out.as_str().as_bytes()),
        npa_package::format_package_hash(&journal.old_registry_file_hash),
        npa_package::format_package_hash(&journal.new_registry_file_hash),
        npa_package::format_package_hash(&journal.attestation_file_hash),
        encode_hex(&journal.old_registry),
        encode_hex(&journal.attestation),
        encode_hex(&journal.registry),
        npa_package::format_package_hash(&journal.journal_hash),
    )
}

fn recovery_journal_hash(journal: &RecoveryJournal) -> PackageHash {
    let mut copy = journal.clone();
    copy.journal_hash = PackageHash::new([0; 32]);
    let mut bytes = RECOVERY_JOURNAL_DOMAIN.to_vec();
    bytes.extend_from_slice(recovery_journal_canonical_json(&copy).as_bytes());
    package_file_hash(&bytes)
}

fn parse_recovery_journal(source: &str) -> Option<RecoveryJournal> {
    if source.len() > MAX_RECOVERY_JOURNAL_BYTES {
        return None;
    }
    match json_string_field(source, "schema")? {
        RECOVERY_JOURNAL_SCHEMA => parse_recovery_journal_v2(source),
        "npa.mathlib.catalog_registry_recovery.v1" => parse_recovery_journal_v1(source),
        _ => None,
    }
}

fn parse_recovery_journal_v2(source: &str) -> Option<RecoveryJournal> {
    let hash = |field| {
        json_string_field(source, field)
            .and_then(|value| npa_package::parse_package_hash(value, field).ok())
    };
    let out = String::from_utf8(decode_hex(json_string_field(source, "out_path_hex")?)?).ok()?;
    let journal = RecoveryJournal {
        legacy_v1: false,
        root_hash: hash("root_hash")?,
        out: PackagePath::new(out),
        old_registry_file_hash: hash("old_registry_file_hash")?,
        new_registry_file_hash: hash("new_registry_file_hash")?,
        attestation_file_hash: hash("attestation_file_hash")?,
        old_registry: decode_hex(json_string_field(source, "old_registry_hex")?)?,
        attestation: decode_hex(json_string_field(source, "attestation_hex")?)?,
        registry: decode_hex(json_string_field(source, "registry_hex")?)?,
        journal_hash: hash("journal_hash")?,
    };
    if source != recovery_journal_canonical_json(&journal)
        || journal.journal_hash != recovery_journal_hash(&journal)
        || journal.old_registry_file_hash != package_file_hash(&journal.old_registry)
        || journal.new_registry_file_hash != package_file_hash(&journal.registry)
        || journal.attestation_file_hash != package_file_hash(&journal.attestation)
    {
        return None;
    }
    Some(journal)
}

fn parse_recovery_journal_v1(source: &str) -> Option<RecoveryJournal> {
    let hash = |field| {
        json_string_field(source, field)
            .and_then(|value| npa_package::parse_package_hash(value, field).ok())
    };
    let journal = RecoveryJournal {
        legacy_v1: true,
        root_hash: hash("root_hash")?,
        out: PackagePath::new(json_string_field(source, "out_path")?),
        old_registry_file_hash: hash("old_registry_file_hash")?,
        new_registry_file_hash: PackageHash::new([0; 32]),
        attestation_file_hash: PackageHash::new([0; 32]),
        old_registry: Vec::new(),
        attestation: decode_hex(json_string_field(source, "attestation_hex")?)?,
        registry: decode_hex(json_string_field(source, "registry_hex")?)?,
        journal_hash: PackageHash::new([0; 32]),
    };
    let expected = format!(
        concat!(
            "{{\"schema\":\"npa.mathlib.catalog_registry_recovery.v1\",",
            "\"root_hash\":\"{}\",\"out_path\":\"{}\",\"old_registry_file_hash\":\"{}\",",
            "\"attestation_hex\":\"{}\",\"registry_hex\":\"{}\",\"proof_evidence\":false}}\n"
        ),
        npa_package::format_package_hash(&journal.root_hash),
        journal.out.as_str(),
        npa_package::format_package_hash(&journal.old_registry_file_hash),
        encode_hex(&journal.attestation),
        encode_hex(&journal.registry),
    );
    if source != expected {
        return None;
    }
    Some(RecoveryJournal {
        new_registry_file_hash: package_file_hash(&journal.registry),
        attestation_file_hash: package_file_hash(&journal.attestation),
        ..journal
    })
}

fn recover(root: &Path, path: &Path) -> CommandResult {
    let root_display = render_package_root(root);
    let raw = match path.to_str() {
        Some(value)
            if value.starts_with("target/registry-reconciliation/") && value.ends_with(".json") =>
        {
            value
        }
        _ => {
            return failed(
                root,
                "promotion_registry_reconciliation_recovery_invalid",
                "--recover",
            )
        }
    };
    let logical = PackagePath::new(raw);
    let journal_bytes = match read_governance_artifact(
        root,
        &logical,
        "--recover",
        "promotion_registry_reconciliation_recovery_invalid",
    ) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let target_lock = match TargetLock::acquire(root) {
        Ok(value) => value,
        Err(_) => return failed(root, "promotion_registry_concurrent_update", "--root"),
    };
    let source = match String::from_utf8(journal_bytes.clone()) {
        Ok(value) => value,
        Err(_) => {
            return failed(
                root,
                "promotion_registry_reconciliation_recovery_invalid",
                "--recover",
            )
        }
    };
    let Some(journal) = parse_recovery_journal(&source) else {
        return failed(
            root,
            "promotion_registry_reconciliation_recovery_invalid",
            "--recover",
        );
    };
    let expected_root_hash = match fs::canonicalize(root) {
        Ok(value) => package_file_hash(value.to_string_lossy().as_bytes()),
        Err(_) => return failed(root, "package_root_unavailable", "--root"),
    };
    if journal.root_hash != expected_root_hash
        || governance_path(root, Path::new(journal.out.as_str()), "--out", true).is_err()
    {
        return failed(
            root,
            "promotion_registry_reconciliation_recovery_invalid",
            "--recover",
        );
    }
    let registry_path = PackagePath::new(MATHLIB_PROMOTION_REGISTRY_PATH);
    let existing = match read_governance_artifact(
        root,
        &registry_path,
        MATHLIB_PROMOTION_REGISTRY_PATH,
        "promotion_registry_reconciliation_recovery_invalid",
    ) {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let proposed = std::str::from_utf8(&journal.registry)
        .ok()
        .and_then(|source| npa_package::parse_promotion_origin_registry_v3_json(source).ok());
    let proposed_event = proposed
        .as_ref()
        .and_then(|registry| registry.catalog_change_events.last());
    let parsed_attestation = std::str::from_utf8(&journal.attestation)
        .ok()
        .and_then(|source| parse_catalog_registry_sync_attestation_json(source).ok());
    let previous = if journal.legacy_v1 {
        if package_file_hash(&existing) == journal.old_registry_file_hash {
            std::str::from_utf8(&existing)
                .ok()
                .and_then(|source| parse_promotion_origin_registry_versioned(source).ok())
        } else {
            proposed.as_ref().and_then(|proposed| {
                parsed_attestation.as_ref().and_then(|attestation| {
                    reconstruct_previous_registry(proposed, &attestation.input_registry.schema)
                })
            })
        }
    } else {
        std::str::from_utf8(&journal.old_registry)
            .ok()
            .and_then(|source| parse_promotion_origin_registry_versioned(source).ok())
    };
    let recovery_previous_hashes = proposed_event
        .map(|event| {
            event
                .revised_routes
                .iter()
                .map(|row| (row.target_module.as_dotted(), row.previous_revision_hash))
                .collect::<BTreeMap<_, _>>()
        })
        .unwrap_or_default();
    if previous.as_ref().is_none_or(|previous| {
        proposed
            .as_ref()
            .is_none_or(|proposed| !valid_transition(previous, proposed, &recovery_previous_hashes))
    }) {
        return failed(
            root,
            "promotion_registry_reconciliation_recovery_invalid",
            "--recover",
        );
    }
    let expected_comparisons = previous
        .as_ref()
        .zip(proposed.as_ref())
        .zip(proposed_event)
        .and_then(|((previous, proposed), event)| {
            transition_comparisons(previous, proposed, event).ok()
        });
    if proposed_event.is_none_or(|event| {
        event.input_registry_hash != journal.old_registry_file_hash
            || event.attestation.path != journal.out
            || parsed_attestation.as_ref().is_none_or(|attestation| {
                expected_comparisons
                    .as_ref()
                    .is_none_or(|expected_comparisons| {
                        validate_catalog_registry_sync_attestation_against_transition(
                            attestation,
                            event,
                            registry_self_hash(previous.as_ref().expect("checked above")),
                            expected_comparisons,
                        )
                        .is_err()
                    })
            })
    }) {
        return failed(
            root,
            "promotion_registry_reconciliation_recovery_invalid",
            "--recover",
        );
    }
    let current = match load_snapshot(root) {
        Ok(value) => value,
        Err(result) => return result,
    };
    if let Err(diagnostic) = validate_checked_generated(&current) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    if let Some(proposed) = &proposed {
        if let Err(diagnostic) = validate_registry_v3_target(root, &current, proposed) {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    let actual_attestation = read_governance_artifact(
        root,
        &journal.out,
        journal.out.as_str(),
        "promotion_registry_reconciliation_recovery_invalid",
    )
    .ok();
    match recovery_disposition(
        &existing,
        &journal.registry,
        journal.old_registry_file_hash,
        actual_attestation.as_deref(),
        &journal.attestation,
    ) {
        RecoveryDisposition::AlreadyComplete => {}
        RecoveryDisposition::Apply => {
            if let Err(diagnostic) = write_governance_artifact(
                root,
                &journal.out,
                &journal.attestation,
                GovernanceOutputPolicy::CreateOrIdentical,
                REASON,
            ) {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
            }
            if let Err(diagnostic) = replace_governance_artifact_if_unchanged(
                root,
                &registry_path,
                &journal.registry,
                &existing,
                REASON,
            ) {
                return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
            }
        }
        RecoveryDisposition::Irreconcilable => {
            return failed(
                root,
                "promotion_registry_reconciliation_recovery_irreconcilable",
                MATHLIB_PROMOTION_REGISTRY_PATH,
            )
        }
    }
    let validation = run_package_validate_promotion_origin_registry(
        PackageValidatePromotionOriginRegistryOptions {
            common: crate::args::PackageCommonOptions {
                root: root.to_path_buf(),
                json: false,
            },
            source_roots: Vec::new(),
            previous_registry: None,
        },
    );
    if validation.status != CommandStatus::Passed {
        return validation;
    }
    if remove_recovery_journal_if_unchanged(root, &logical, &journal_bytes, &target_lock).is_err() {
        return failed(
            root,
            "promotion_registry_reconciliation_recovery_cleanup_failed",
            raw,
        );
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics.push(CommandDiagnostic::info(
        DiagnosticKind::PackagePolicy,
        "recovery_completed",
    ));
    result
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RecoveryDisposition {
    AlreadyComplete,
    Apply,
    Irreconcilable,
}

fn recovery_disposition(
    existing_registry: &[u8],
    proposed_registry: &[u8],
    old_registry_hash: PackageHash,
    actual_attestation: Option<&[u8]>,
    proposed_attestation: &[u8],
) -> RecoveryDisposition {
    if existing_registry == proposed_registry {
        return if actual_attestation == Some(proposed_attestation) {
            RecoveryDisposition::AlreadyComplete
        } else {
            RecoveryDisposition::Irreconcilable
        };
    }
    if package_file_hash(existing_registry) != old_registry_hash
        || actual_attestation.is_some_and(|actual| actual != proposed_attestation)
    {
        return RecoveryDisposition::Irreconcilable;
    }
    RecoveryDisposition::Apply
}

fn encode_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn decode_hex(value: &str) -> Option<Vec<u8>> {
    if !value.len().is_multiple_of(2) {
        return None;
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let digit = |byte: u8| match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                _ => None,
            };
            Some((digit(pair[0])? << 4) | digit(pair[1])?)
        })
        .collect()
}

fn json_string_field<'a>(source: &'a str, field: &str) -> Option<&'a str> {
    let marker = format!("\"{field}\":\"");
    let start = source.find(&marker)? + marker.len();
    let end = source[start..].find('"')? + start;
    Some(&source[start..end])
}

fn failed(root: &Path, reason: &str, path: impl Into<String>) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        render_package_root(root),
        vec![CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path)],
    )
}

fn recovery_required(
    root: &Path,
    diagnostic: Box<CommandDiagnostic>,
    journal: &PackagePath,
) -> CommandResult {
    CommandResult::failed(
        COMMAND,
        render_package_root(root),
        vec![
            *diagnostic,
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "promotion_recovery_required")
                .with_path(journal.as_str()),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        sync::atomic::{AtomicU64, Ordering},
        time::{SystemTime, UNIX_EPOCH},
    };

    fn revision(meta: PackageHash, replay: PackageHash) -> PromotionDeclarationTargetRevision {
        PromotionDeclarationTargetRevision {
            target_version: npa_package::PackageVersion::new("0.2.1"),
            target_source_file_hash: PackageHash::new([1; 32]),
            target_meta_file_hash: meta,
            target_replay_file_hash: replay,
            target_certificate_file_hash: PackageHash::new([2; 32]),
            target_certificate_hash: PackageHash::new([3; 32]),
            target_export_hash: PackageHash::new([4; 32]),
            target_axiom_report_hash: PackageHash::new([5; 32]),
            theorems: Vec::new(),
        }
    }

    #[test]
    fn recovery_payload_hex_round_trips() {
        let bytes = b"{\"registry\":\"canonical\"}\n";
        assert_eq!(
            decode_hex(&encode_hex(bytes)).as_deref(),
            Some(bytes.as_slice())
        );
        assert!(decode_hex("0").is_none());
        assert!(decode_hex("zz").is_none());
    }

    #[test]
    fn recovery_journal_binds_all_payloads_and_rejects_noncanonical_edits() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "npa-registry-journal-{}-{nonce}",
            std::process::id(),
        ));
        fs::create_dir_all(&root).unwrap();
        let source = recovery_journal_json(
            &root,
            &PackagePath::new("docs/promotion/sync.json"),
            b"old registry",
            b"attestation",
            b"new registry",
        );
        let parsed = parse_recovery_journal(&source).unwrap();
        assert_eq!(parsed.old_registry, b"old registry");
        assert_eq!(parsed.attestation, b"attestation");
        assert_eq!(parsed.registry, b"new registry");
        assert!(parse_recovery_journal(&source.replacen(
            "\"registry_hex\":\"",
            "\"unknown\":false,\"registry_hex\":\"",
            1
        ))
        .is_none());
        assert!(parse_recovery_journal(&source.replacen("6e6577", "6f6577", 1)).is_none());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn recovery_journal_accepts_canonical_legacy_v1_for_upgrade_recovery() {
        let root_hash = PackageHash::new([1; 32]);
        let old_hash = PackageHash::new([2; 32]);
        let attestation = b"legacy attestation";
        let registry = b"legacy proposed registry";
        let source = format!(
            concat!(
                "{{\"schema\":\"npa.mathlib.catalog_registry_recovery.v1\",",
                "\"root_hash\":\"{}\",\"out_path\":\"docs/promotion/sync.json\",",
                "\"old_registry_file_hash\":\"{}\",\"attestation_hex\":\"{}\",",
                "\"registry_hex\":\"{}\",\"proof_evidence\":false}}\n"
            ),
            npa_package::format_package_hash(&root_hash),
            npa_package::format_package_hash(&old_hash),
            encode_hex(attestation),
            encode_hex(registry),
        );
        let parsed = parse_recovery_journal(&source).unwrap();
        assert!(parsed.legacy_v1);
        assert_eq!(parsed.old_registry_file_hash, old_hash);
        assert_eq!(parsed.attestation, attestation);
        assert_eq!(parsed.registry, registry);
        assert!(parse_recovery_journal(&source.replacen(
            "\"out_path\":",
            "\"unknown\":false,\"out_path\":",
            1,
        ))
        .is_none());
    }

    #[test]
    fn recovery_state_machine_covers_crash_boundaries() {
        let old = b"old registry";
        let proposed = b"proposed registry";
        let attestation = b"attestation";
        let old_hash = package_file_hash(old);
        assert_eq!(
            recovery_disposition(old, proposed, old_hash, None, attestation),
            RecoveryDisposition::Apply
        );
        assert_eq!(
            recovery_disposition(old, proposed, old_hash, Some(attestation), attestation),
            RecoveryDisposition::Apply
        );
        assert_eq!(
            recovery_disposition(proposed, proposed, old_hash, Some(attestation), attestation),
            RecoveryDisposition::AlreadyComplete
        );
        assert_eq!(
            recovery_disposition(old, proposed, old_hash, Some(b"conflict"), attestation),
            RecoveryDisposition::Irreconcilable
        );
        assert_eq!(
            recovery_disposition(b"third state", proposed, old_hash, None, attestation),
            RecoveryDisposition::Irreconcilable
        );
    }

    #[test]
    fn version_comparison_is_numeric_and_allows_skips() {
        assert!(version_greater("0.10.0", "0.2.9"));
        assert!(version_greater("4.0.0", "0.2.1"));
        assert!(!version_greater("0.2.1", "0.2.1"));
    }

    #[test]
    fn legacy_zero_meta_and_replay_require_an_explicit_overlay() {
        let zero = PackageHash::new([0; 32]);
        let legacy = revision(zero, zero);
        let complete = revision(PackageHash::new([6; 32]), PackageHash::new([7; 32]));
        assert!(same_artifacts(&legacy, &complete));
        assert!(!same_complete_artifacts(&legacy, &complete));
        let mut overlaid = legacy;
        complete_legacy_revision(&mut overlaid, &complete);
        assert_eq!(
            catalog_target_revision_hash(&overlaid).unwrap(),
            catalog_target_revision_hash(&complete).unwrap()
        );
    }

    #[test]
    fn pending_recovery_journal_blocks_normal_operation() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "npa-registry-recovery-{}-{nonce}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let directory = root.join("target/registry-reconciliation");
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("event.json"), b"pending").unwrap();
        assert!(pending_recovery_journal(&root).is_some());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn reconciliation_lock_rejects_a_concurrent_writer() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "npa-registry-lock-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        let first = TargetLock::acquire(&root).unwrap();
        assert!(TargetLock::acquire(&root).is_err());
        drop(first);
        assert!(TargetLock::acquire(&root).is_ok());
        fs::remove_dir_all(root).unwrap();
    }
}
