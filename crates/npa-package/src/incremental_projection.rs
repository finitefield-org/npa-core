//! Incremental generated-artifact projection planning.
//!
//! These plans are optimization metadata only. They are never proof evidence and
//! do not replace canonical generated artifact bytes or source-free checker
//! verdicts.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    artifacts::{normalize_checker_summaries, PackageCheckerSummary},
    audit_selection::package_lock_reverse_dependencies,
    error::{PackageArtifactError, PackageArtifactResult, PackageLockError},
    lock::{build_package_lock_graph, PackageLockManifest},
};

/// Stable trust-boundary note for incremental generated-artifact planning.
pub const PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY: &str =
    "incremental generated-artifact planning is not proof evidence; canonical artifacts and checker verdicts dominate";

/// Projection strategy selected for a checked generated artifact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageIncrementalProjectionMode {
    /// Only the impacted module set needs to be recomputed.
    Incremental,
    /// Global metadata changed, so the whole projection must be regenerated.
    Full,
}

impl PackageIncrementalProjectionMode {
    /// Return the stable mode string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Incremental => "incremental",
            Self::Full => "full",
        }
    }
}

/// One module selected by incremental generated-artifact planning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageIncrementalProjectionModule {
    /// Selected module name.
    pub module: Name,
    /// Stable reason codes explaining why the module is impacted.
    pub reason_codes: Vec<String>,
}

/// Deterministic incremental projection plan for one generated artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageIncrementalProjectionPlan {
    /// Stable generated artifact name.
    pub artifact: String,
    /// Whether module-level incremental projection is allowed.
    pub mode: PackageIncrementalProjectionMode,
    /// Stable reason codes that forced a full projection.
    pub full_reason_codes: Vec<String>,
    /// Impacted modules in current package-lock topological order.
    pub impacted_modules: Vec<PackageIncrementalProjectionModule>,
    /// Trust-boundary note for diagnostics and tests.
    pub trust_boundary: String,
    /// Always false: planning metadata is not proof evidence.
    pub proof_evidence: bool,
}

impl PackageIncrementalProjectionPlan {
    /// Return true when no current module or global metadata invalidates the checked artifact.
    pub fn is_incremental_unchanged(&self) -> bool {
        self.mode == PackageIncrementalProjectionMode::Incremental
            && self.impacted_modules.is_empty()
            && self.full_reason_codes.is_empty()
            && !self.proof_evidence
    }

    /// Return impacted module names as a deterministic set.
    pub fn impacted_module_names(&self) -> BTreeSet<Name> {
        self.impacted_modules
            .iter()
            .map(|module| module.module.clone())
            .collect()
    }
}

pub(crate) fn package_incremental_full_projection_plan(
    artifact: &str,
    lock: &PackageLockManifest,
    reasons: impl IntoIterator<Item = impl Into<String>>,
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let reason_codes = normalized_reason_codes(reasons);
    let modules = package_lock_topological_order(lock)?
        .into_iter()
        .map(|module| PackageIncrementalProjectionModule {
            module,
            reason_codes: reason_codes.clone(),
        })
        .collect();
    Ok(PackageIncrementalProjectionPlan {
        artifact: artifact.to_owned(),
        mode: PackageIncrementalProjectionMode::Full,
        full_reason_codes: reason_codes,
        impacted_modules: modules,
        trust_boundary: PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY.to_owned(),
        proof_evidence: false,
    })
}

pub(crate) fn package_incremental_projection_plan_from_changed_modules(
    artifact: &str,
    lock: &PackageLockManifest,
    full_reasons: impl IntoIterator<Item = impl Into<String>>,
    changed_modules: BTreeMap<Name, BTreeSet<String>>,
) -> PackageArtifactResult<PackageIncrementalProjectionPlan> {
    let full_reason_codes = normalized_reason_codes(full_reasons);
    if !full_reason_codes.is_empty() {
        return package_incremental_full_projection_plan(artifact, lock, full_reason_codes);
    }

    let topological_order = package_lock_topological_order(lock)?;
    let current_modules = topological_order.iter().cloned().collect::<BTreeSet<_>>();
    let mut impacted = changed_modules;
    for changed in impacted.keys().cloned().collect::<Vec<_>>() {
        if !current_modules.contains(&changed) {
            return package_incremental_full_projection_plan(
                artifact,
                lock,
                ["module_removed_or_missing_from_current_lock"],
            );
        }
    }

    let reverse = package_lock_reverse_dependencies(lock)?;
    for changed in impacted.keys().cloned().collect::<Vec<_>>() {
        for dependent in reverse_dependency_closure(&reverse, &changed) {
            impacted
                .entry(dependent)
                .or_default()
                .insert(format!("reverse_dependency_of:{}", changed.as_dotted()));
        }
    }

    let impacted_modules = topological_order
        .into_iter()
        .filter_map(|module| {
            impacted.remove(&module).map(|reasons| {
                let reason_codes = reasons.into_iter().collect();
                PackageIncrementalProjectionModule {
                    module,
                    reason_codes,
                }
            })
        })
        .collect();

    Ok(PackageIncrementalProjectionPlan {
        artifact: artifact.to_owned(),
        mode: PackageIncrementalProjectionMode::Incremental,
        full_reason_codes: Vec::new(),
        impacted_modules,
        trust_boundary: PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY.to_owned(),
        proof_evidence: false,
    })
}

pub(crate) fn package_lock_topological_order(
    lock: &PackageLockManifest,
) -> PackageArtifactResult<Vec<Name>> {
    build_package_lock_graph(lock)
        .map(|graph| graph.topological_order)
        .map_err(package_lock_graph_error)
}

pub(crate) fn push_reason(reasons: &mut Vec<String>, condition: bool, reason: &str) {
    if condition {
        reasons.push(reason.to_owned());
    }
}

pub(crate) fn add_changed_reason(
    changed: &mut BTreeMap<Name, BTreeSet<String>>,
    module: &Name,
    condition: bool,
    reason: &str,
) {
    if condition {
        changed
            .entry(module.clone())
            .or_default()
            .insert(reason.to_owned());
    }
}

pub(crate) fn checker_summaries_match(
    checked: &[PackageCheckerSummary],
    current: &[PackageCheckerSummary],
) -> bool {
    let mut checked = checked.to_vec();
    let mut current = current.to_vec();
    normalize_checker_summaries(&mut checked);
    normalize_checker_summaries(&mut current);
    checked == current
}

pub(crate) fn normalized_reason_codes(
    reasons: impl IntoIterator<Item = impl Into<String>>,
) -> Vec<String> {
    reasons
        .into_iter()
        .map(Into::into)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn reverse_dependency_closure(
    reverse: &BTreeMap<Name, Vec<Name>>,
    changed: &Name,
) -> BTreeSet<Name> {
    let mut closure = BTreeSet::new();
    let mut pending = reverse.get(changed).cloned().unwrap_or_default();
    while let Some(module) = pending.pop() {
        if !closure.insert(module.clone()) {
            continue;
        }
        if let Some(next) = reverse.get(&module) {
            pending.extend(next.iter().cloned());
        }
    }
    closure
}

fn package_lock_graph_error(error: PackageLockError) -> PackageArtifactError {
    PackageArtifactError::summary_mismatch(
        "package_lock",
        "package_lock",
        "valid acyclic package lock graph",
        format!("{:?}", error.reason_code),
    )
}

#[cfg(test)]
mod tests {
    use npa_cert::Name;

    use crate::{
        package_axiom_report_incremental_projection_plan, package_axiom_report_summary,
        package_checksum_only_signature_policy, package_publish_plan_incremental_projection_plan,
        package_theorem_index_incremental_projection_plan, package_theorem_index_summary,
        package_verified_export_summary_incremental_projection_plan, PackageArtifactFileReference,
        PackageArtifactOrigin, PackageArtifactPolicy, PackageAuditImportIdentity,
        PackageDownstreamImportBundle, PackageHash, PackageId, PackageIncrementalProjectionMode,
        PackageIncrementalProjectionPlan, PackageLockEntry, PackageLockEntryOrigin,
        PackageLockImport, PackageLockManifest, PackageLockManifestReference, PackagePath,
        PackagePublishRelease, PackagePublishReleaseReference, PackagePublishSummary,
        PackageRegistryArtifactHashes, PackageRegistryImport, PackageRegistryModule,
        PackageTheoremIndexArtifact, PackageTheoremIndexEntry, PackageTheoremIndexKind,
        PackageTheoremIndexMode, PackageTheoremStatement, PackageVersion,
        PACKAGE_AXIOM_REPORT_SCHEMA, PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY,
        PACKAGE_LOCK_SCHEMA, PACKAGE_MANIFEST_SCHEMA, PACKAGE_PUBLISH_PLAN_SCHEMA,
        PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE, PACKAGE_THEOREM_INDEX_SCHEMA,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL,
        PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA, PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY,
        REGISTRY_MODULE_SCHEMA,
    };
    use crate::{
        PackageAxiomPolicyStatus, PackageAxiomPolicyStatusKind, PackageAxiomReport,
        PackageAxiomReportIncrementalProjectionInput, PackageAxiomReportModule, PackageGlobalRef,
        PackagePublishPlan, PackageVerifiedExportSummary, PackageVerifiedExportSummaryModule,
    };

    #[test]
    fn package_incremental_generated_artifacts_unchanged_are_reusable_not_evidence() {
        let fixture = Fixture::new(hash(10), hash(20));
        let axiom_report = fixture.axiom_report();
        let theorem_index = fixture.theorem_index();
        let export_summary = fixture.export_summary();
        let publish_plan = fixture.publish_plan();

        let plans = vec![
            package_axiom_report_incremental_projection_plan(
                PackageAxiomReportIncrementalProjectionInput {
                    report: &axiom_report,
                    package: &fixture.package,
                    version: &fixture.version,
                    manifest: &fixture.manifest_ref,
                    package_lock: &fixture.lock_ref,
                    policy: &fixture.policy,
                    checker_summaries: &[],
                    current_lock: &fixture.lock,
                },
            )
            .unwrap(),
            package_theorem_index_incremental_projection_plan(
                &theorem_index,
                &fixture.package,
                &fixture.version,
                &fixture.manifest_ref,
                &fixture.lock_ref,
                &[],
                &fixture.lock,
            )
            .unwrap(),
            package_verified_export_summary_incremental_projection_plan(
                &export_summary,
                &fixture.package,
                &fixture.version,
                &fixture.core_spec,
                &fixture.certificate_format,
                fixture.lock_ref.file_hash,
                &fixture.lock,
            )
            .unwrap(),
            package_publish_plan_incremental_projection_plan(
                &publish_plan,
                &fixture.package,
                &fixture.version,
                &publish_plan.release,
                &fixture.lock,
                &[],
            )
            .unwrap(),
        ];

        for plan in plans {
            assert_eq!(plan.mode, PackageIncrementalProjectionMode::Incremental);
            assert!(plan.is_incremental_unchanged());
            assert!(plan.impacted_modules.is_empty());
            assert!(!plan.proof_evidence);
            assert_eq!(
                plan.trust_boundary,
                PACKAGE_INCREMENTAL_PROJECTION_TRUST_BOUNDARY
            );
        }
    }

    #[test]
    fn package_incremental_generated_artifacts_select_reverse_dependents_deterministically() {
        let checked = Fixture::new(hash(10), hash(20));
        let current = Fixture::new(hash(99), hash(77));
        let axiom_report = checked.axiom_report();
        let theorem_index = checked.theorem_index();
        let export_summary = checked.export_summary();

        let axiom_plan = package_axiom_report_incremental_projection_plan(
            PackageAxiomReportIncrementalProjectionInput {
                report: &axiom_report,
                package: &checked.package,
                version: &checked.version,
                manifest: &checked.manifest_ref,
                package_lock: &current.lock_ref,
                policy: &checked.policy,
                checker_summaries: &[],
                current_lock: &current.lock,
            },
        )
        .unwrap();
        assert_impacted_modules(&axiom_plan, &["Fixture.A", "Fixture.B"]);
        assert_reason(&axiom_plan, "Fixture.A", "export_hash_changed");
        assert_reason(&axiom_plan, "Fixture.B", "reverse_dependency_of:Fixture.A");

        let theorem_plan = package_theorem_index_incremental_projection_plan(
            &theorem_index,
            &checked.package,
            &checked.version,
            &checked.manifest_ref,
            &current.lock_ref,
            &[],
            &current.lock,
        )
        .unwrap();
        assert_impacted_modules(&theorem_plan, &["Fixture.A", "Fixture.B"]);
        assert_reason(&theorem_plan, "Fixture.A", "export_hash_changed");
        assert_reason(
            &theorem_plan,
            "Fixture.B",
            "reverse_dependency_of:Fixture.A",
        );

        let export_plan = package_verified_export_summary_incremental_projection_plan(
            &export_summary,
            &checked.package,
            &checked.version,
            &checked.core_spec,
            &checked.certificate_format,
            current.lock_ref.file_hash,
            &current.lock,
        )
        .unwrap();
        assert_impacted_modules(&export_plan, &["Fixture.A", "Fixture.B"]);
        assert_reason(&export_plan, "Fixture.A", "export_hash_changed");
        assert_reason(&export_plan, "Fixture.B", "direct_import_identity_changed");
    }

    #[test]
    fn package_incremental_generated_artifacts_global_metadata_forces_full() {
        let fixture = Fixture::new(hash(10), hash(20));
        let mut report = fixture.axiom_report();
        report.policy.allow_custom_axioms = true;

        let plan = package_axiom_report_incremental_projection_plan(
            PackageAxiomReportIncrementalProjectionInput {
                report: &report,
                package: &fixture.package,
                version: &fixture.version,
                manifest: &fixture.manifest_ref,
                package_lock: &fixture.lock_ref,
                policy: &fixture.policy,
                checker_summaries: &[],
                current_lock: &fixture.lock,
            },
        )
        .unwrap();

        assert_eq!(plan.mode, PackageIncrementalProjectionMode::Full);
        assert_eq!(plan.full_reason_codes, vec!["policy_changed"]);
        assert_impacted_modules(&plan, &["Fixture.A", "Fixture.B"]);
        assert!(!plan.proof_evidence);
    }

    #[derive(Clone)]
    struct Fixture {
        package: PackageId,
        version: PackageVersion,
        core_spec: String,
        kernel_profile: String,
        certificate_format: String,
        checker_profile: String,
        manifest_ref: PackageArtifactFileReference,
        lock_ref: PackageArtifactFileReference,
        policy: PackageArtifactPolicy,
        lock: PackageLockManifest,
    }

    impl Fixture {
        fn new(module_a_export_hash: PackageHash, lock_file_hash: PackageHash) -> Self {
            let package = PackageId::new("fixture-package");
            let version = PackageVersion::new("0.1.0");
            let manifest_ref = PackageArtifactFileReference {
                path: PackagePath::new("npa-package.toml"),
                file_hash: hash(1),
            };
            let lock_ref = PackageArtifactFileReference {
                path: PackagePath::new("generated/package-lock.json"),
                file_hash: lock_file_hash,
            };
            let module_a = lock_entry(
                "Fixture.A",
                "Fixture/A/certificate.npcert",
                [module_a_export_hash, hash(11), hash(12), hash(13)],
                Vec::new(),
            );
            let module_b = lock_entry(
                "Fixture.B",
                "Fixture/B/certificate.npcert",
                [hash(20), hash(21), hash(22), hash(23)],
                vec![PackageLockImport {
                    module: name("Fixture.A"),
                    export_hash: module_a_export_hash,
                    certificate_hash: hash(11),
                }],
            );
            let lock = PackageLockManifest {
                schema: PACKAGE_LOCK_SCHEMA.to_owned(),
                package: package.clone(),
                version: version.clone(),
                manifest: PackageLockManifestReference {
                    path: manifest_ref.path.clone(),
                    file_hash: manifest_ref.file_hash,
                },
                entries: vec![module_a, module_b],
            };
            Self {
                package,
                version,
                core_spec: "npa.core.v0.1".to_owned(),
                kernel_profile: "npa.kernel.v0.1".to_owned(),
                certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
                checker_profile: "npa.checker.reference.v0.1".to_owned(),
                manifest_ref,
                lock_ref,
                policy: PackageArtifactPolicy {
                    allow_custom_axioms: false,
                    allowed_axioms: Vec::new(),
                },
                lock,
            }
        }

        fn axiom_report(&self) -> PackageAxiomReport {
            let modules = self
                .lock
                .entries
                .iter()
                .map(|entry| PackageAxiomReportModule {
                    module: entry.module.clone(),
                    origin: artifact_origin(entry.origin),
                    export_hash: entry.export_hash,
                    certificate_hash: entry.certificate_hash,
                    axiom_report_hash: entry.axiom_report_hash,
                    certificate_file_hash: entry.certificate_file_hash,
                    direct_axioms: Vec::new(),
                    transitive_axioms: Vec::new(),
                    policy_status: PackageAxiomPolicyStatus {
                        status: PackageAxiomPolicyStatusKind::Ok,
                        violations: Vec::new(),
                    },
                })
                .collect::<Vec<_>>();
            PackageAxiomReport {
                schema: PACKAGE_AXIOM_REPORT_SCHEMA.to_owned(),
                package: self.package.clone(),
                version: self.version.clone(),
                manifest: self.manifest_ref.clone(),
                package_lock: self.lock_ref.clone(),
                policy: self.policy.clone(),
                summary: package_axiom_report_summary(&modules),
                modules,
                checker_summaries: Vec::new(),
                package_axiom_report_hash: hash(0),
            }
            .with_computed_hash()
            .unwrap()
        }

        fn theorem_index(&self) -> crate::PackageTheoremIndex {
            let entries = self
                .lock
                .entries
                .iter()
                .map(|entry| PackageTheoremIndexEntry {
                    global_ref: PackageGlobalRef {
                        module: entry.module.clone(),
                        name: name("theorem"),
                        export_hash: entry.export_hash,
                        certificate_hash: entry.certificate_hash,
                        decl_interface_hash: hash(30),
                    },
                    kind: PackageTheoremIndexKind::Theorem,
                    statement: PackageTheoremStatement {
                        core_hash: hash(31),
                        head: None,
                        constants: Vec::new(),
                    },
                    modes: vec![PackageTheoremIndexMode::Exact],
                    tags: Vec::new(),
                    axiom_dependencies: Vec::new(),
                    module_axiom_report_hash: entry.axiom_report_hash,
                    artifact: PackageTheoremIndexArtifact {
                        origin: artifact_origin(entry.origin),
                        certificate: entry.certificate.clone(),
                    },
                })
                .collect::<Vec<_>>();
            crate::PackageTheoremIndex {
                schema: PACKAGE_THEOREM_INDEX_SCHEMA.to_owned(),
                package: self.package.clone(),
                version: self.version.clone(),
                manifest: self.manifest_ref.clone(),
                package_lock: self.lock_ref.clone(),
                index_profile: PACKAGE_THEOREM_INDEX_CERTIFICATE_DERIVED_PROFILE.to_owned(),
                summary: package_theorem_index_summary(&entries),
                entries,
                checker_summaries: Vec::new(),
                theorem_index_hash: hash(0),
            }
            .with_computed_hash()
            .unwrap()
        }

        fn export_summary(&self) -> PackageVerifiedExportSummary {
            let modules = self
                .lock
                .entries
                .iter()
                .map(|entry| PackageVerifiedExportSummaryModule {
                    module: entry.module.clone(),
                    origin: artifact_origin(entry.origin),
                    certificate: entry.certificate.clone(),
                    certificate_file_hash: entry.certificate_file_hash,
                    export_hash: entry.export_hash,
                    certificate_hash: entry.certificate_hash,
                    axiom_report_hash: entry.axiom_report_hash,
                    direct_imports: entry
                        .imports
                        .iter()
                        .map(|import| PackageAuditImportIdentity {
                            module: import.module.clone(),
                            export_hash: import.export_hash,
                            certificate_hash: import.certificate_hash,
                        })
                        .collect(),
                    exported_globals: Vec::new(),
                    module_axioms: Vec::new(),
                    core_features: Vec::new(),
                })
                .collect();
            PackageVerifiedExportSummary {
                schema: PACKAGE_VERIFIED_EXPORT_SUMMARY_SCHEMA.to_owned(),
                package: self.package.clone(),
                version: self.version.clone(),
                core_spec: self.core_spec.clone(),
                certificate_format: self.certificate_format.clone(),
                package_lock_hash: self.lock_ref.file_hash,
                module_order: PACKAGE_VERIFIED_EXPORT_SUMMARY_MODULE_ORDER_TOPOLOGICAL.to_owned(),
                trusted: false,
                trust_boundary: PACKAGE_VERIFIED_EXPORT_SUMMARY_TRUST_BOUNDARY.to_owned(),
                modules,
                summary_hash: hash(0),
            }
            .with_computed_hash()
            .unwrap()
        }

        fn publish_plan(&self) -> PackagePublishPlan {
            let release = self.publish_release();
            PackagePublishPlan {
                schema: PACKAGE_PUBLISH_PLAN_SCHEMA.to_owned(),
                package: self.package.clone(),
                version: self.version.clone(),
                release,
                artifacts: Vec::new(),
                module_registry_entries: self.registry_entries(),
                downstream_import_bundle: PackageDownstreamImportBundle {
                    package: self.package.clone(),
                    version: self.version.clone(),
                    modules: Vec::new(),
                },
                checker_summaries: Vec::new(),
                signature_policy: package_checksum_only_signature_policy(),
                summary: PackagePublishSummary {
                    local_module_count: 2,
                    external_import_count: 0,
                    artifact_count: 0,
                    registry_entry_count: 2,
                    checker_summary_count: 0,
                },
                publish_plan_hash: hash(0),
            }
        }

        fn publish_release(&self) -> PackagePublishRelease {
            PackagePublishRelease {
                core_spec: self.core_spec.clone(),
                kernel_profile: self.kernel_profile.clone(),
                certificate_format: self.certificate_format.clone(),
                checker_profile: self.checker_profile.clone(),
                manifest: release_ref(self.manifest_ref.clone(), None, PACKAGE_MANIFEST_SCHEMA),
                package_lock: release_ref(self.lock_ref.clone(), None, PACKAGE_LOCK_SCHEMA),
                axiom_report: release_ref(
                    PackageArtifactFileReference {
                        path: PackagePath::new("generated/axiom-report.json"),
                        file_hash: hash(40),
                    },
                    Some(hash(41)),
                    PACKAGE_AXIOM_REPORT_SCHEMA,
                ),
                theorem_index: release_ref(
                    PackageArtifactFileReference {
                        path: PackagePath::new("generated/theorem-index.json"),
                        file_hash: hash(42),
                    },
                    Some(hash(43)),
                    PACKAGE_THEOREM_INDEX_SCHEMA,
                ),
            }
        }

        fn registry_entries(&self) -> Vec<PackageRegistryModule> {
            self.lock
                .entries
                .iter()
                .map(|entry| PackageRegistryModule {
                    schema: REGISTRY_MODULE_SCHEMA.to_owned(),
                    package: self.package.clone(),
                    package_version: self.version.clone(),
                    module: entry.module.clone(),
                    core_spec: self.core_spec.clone(),
                    kernel_profile: self.kernel_profile.clone(),
                    certificate_format: self.certificate_format.clone(),
                    export_hash: entry.export_hash,
                    certificate_hash: entry.certificate_hash,
                    axiom_report_hash: entry.axiom_report_hash,
                    certificate: PackageArtifactFileReference {
                        path: entry.certificate.clone(),
                        file_hash: entry.certificate_file_hash,
                    },
                    imports: entry
                        .imports
                        .iter()
                        .map(|import| PackageRegistryImport {
                            module: import.module.clone(),
                            origin: PackageArtifactOrigin::Local,
                            package: None,
                            version: None,
                            export_hash: import.export_hash,
                            certificate_hash: import.certificate_hash,
                        })
                        .collect(),
                    checker_results: Vec::new(),
                    artifact_hashes: PackageRegistryArtifactHashes {
                        package_lock_file_hash: self.lock_ref.file_hash,
                        axiom_report_file_hash: hash(40),
                        theorem_index_file_hash: hash(42),
                    },
                })
                .collect()
        }
    }

    fn lock_entry(
        module: &str,
        certificate: &str,
        hashes: [PackageHash; 4],
        imports: Vec<PackageLockImport>,
    ) -> PackageLockEntry {
        PackageLockEntry {
            module: name(module),
            origin: PackageLockEntryOrigin::Local,
            certificate: PackagePath::new(certificate),
            export_hash: hashes[0],
            certificate_hash: hashes[1],
            axiom_report_hash: hashes[2],
            certificate_file_hash: hashes[3],
            imports,
            package: None,
            version: None,
        }
    }

    fn release_ref(
        reference: PackageArtifactFileReference,
        content_hash: Option<PackageHash>,
        schema: &str,
    ) -> PackagePublishReleaseReference {
        PackagePublishReleaseReference {
            path: reference.path,
            file_hash: reference.file_hash,
            content_hash,
            schema: Some(schema.to_owned()),
        }
    }

    fn assert_impacted_modules(plan: &PackageIncrementalProjectionPlan, expected: &[&str]) {
        assert_eq!(
            plan.impacted_modules
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            expected
        );
    }

    fn assert_reason(plan: &PackageIncrementalProjectionPlan, module: &str, reason: &str) {
        let module = plan
            .impacted_modules
            .iter()
            .find(|impacted| impacted.module.as_dotted() == module)
            .unwrap();
        assert!(module.reason_codes.iter().any(|actual| actual == reason));
    }

    fn artifact_origin(origin: PackageLockEntryOrigin) -> PackageArtifactOrigin {
        match origin {
            PackageLockEntryOrigin::Local => PackageArtifactOrigin::Local,
            PackageLockEntryOrigin::External => PackageArtifactOrigin::External,
        }
    }

    fn name(value: &str) -> Name {
        Name::from_dotted(value)
    }

    fn hash(byte: u8) -> PackageHash {
        PackageHash::new([byte; 32])
    }
}
