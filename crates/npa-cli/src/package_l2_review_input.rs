//! Implementation of `npa package prepare-l2-review-input`.

use std::{cell::RefCell, collections::BTreeMap, fs, path::Path};

use npa_api::PackageArtifactReferenceSummaryMode;
use npa_cert::{verify_module_cert_hashes, Name};
use npa_package::{
    package_file_hash, parse_l2_acceptance_policy_json, parse_package_axiom_report_json,
    parse_package_theorem_index_json, L2AcceptancePolicy, L2ReviewInput, L2ReviewInputImport,
    L2ReviewInputPolicy, L2ReviewInputSource, PackageArtifactOrigin, PackageAxiomReport,
    PackageHash, PackageLockEntryOrigin, PackagePath, PackageTheoremIndex,
};

use crate::{
    args::PackageL2ReviewInputOptions,
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::{join_package_path, render_package_path},
    governance_writer::{
        confined_governance_path, write_governance_artifact, GovernanceOutputPolicy,
    },
    package::load_package_root,
    package_artifacts::{
        load_package_audit_snapshot, LoadedPackageAuditSnapshot, PackageGeneratedArtifactReadMode,
        PACKAGE_AXIOM_REPORT_PATH, PACKAGE_LOCK_PATH, PACKAGE_THEOREM_INDEX_PATH,
    },
};

const COMMAND: &str = "package prepare-l2-review-input";
type ReviewInputKey = (Name, Name);
type CachedReviewInput = (L2ReviewInput, Vec<u8>);

pub(crate) struct L2ReviewInputContext {
    policy: L2AcceptancePolicy,
    policy_hash: PackageHash,
    audit: LoadedPackageAuditSnapshot,
    axiom: PackageAxiomReport,
    index: PackageTheoremIndex,
    inputs: RefCell<BTreeMap<ReviewInputKey, CachedReviewInput>>,
}

/// Export one immutable theorem-specific review input.
pub fn run_package_prepare_l2_review_input(options: PackageL2ReviewInputOptions) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let root_display = loaded.root_display.clone();
    let result = build_review_input(&loaded, &options);
    let (input, bytes) = match result {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let out = PackagePath::new(options.out.to_string_lossy());
    let output_path = match confined_governance_path(
        &loaded.root,
        &out,
        "--out",
        "l2_review_output_not_package_relative",
    ) {
        Ok(path) => path,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    if options.check {
        match fs::read(&output_path) {
            Ok(existing) if existing == bytes => {}
            _ => {
                return CommandResult::failed(
                    COMMAND,
                    root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::GeneratedArtifact,
                        "l2_review_output_stale",
                    )
                    .with_path(render_package_path(&out))],
                );
            }
        }
    } else if let Err(diagnostic) = write_governance_artifact(
        &loaded.root,
        &out,
        &bytes,
        GovernanceOutputPolicy::CreateOrIdentical,
        "l2_review",
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "l2_review_input".to_owned(),
        path: render_package_path(&out),
    });
    result.diagnostics.push(
        CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "l2_review_input_ready")
            .with_module(input.source.module.as_dotted())
            .with_field(input.source.theorem.as_dotted())
            .with_actual_value(npa_package::format_package_hash(&input.input_hash)),
    );
    result
}

pub(crate) fn build_review_input(
    loaded: &crate::package::LoadedPackageRoot,
    options: &PackageL2ReviewInputOptions,
) -> Result<(L2ReviewInput, Vec<u8>), Box<CommandDiagnostic>> {
    L2ReviewInputContext::load(loaded, &options.policy)?.build(
        loaded,
        &options.module,
        &options.declaration,
    )
}

impl L2ReviewInputContext {
    pub(crate) fn theorem_index(&self) -> &PackageTheoremIndex {
        &self.index
    }

    pub(crate) fn load(
        loaded: &crate::package::LoadedPackageRoot,
        policy_path: &Path,
    ) -> Result<Self, Box<CommandDiagnostic>> {
        let policy_bytes = fs::read(policy_path)
            .map_err(|_| diagnostic("l2_review_policy_read_failed", "--policy"))?;
        let policy_source = std::str::from_utf8(&policy_bytes)
            .map_err(|_| diagnostic("l2_review_policy_read_failed", "--policy"))?;
        let policy = parse_l2_acceptance_policy_json(policy_source)
            .map_err(|_| diagnostic("l2_review_policy_not_current", "--policy"))?;
        Self::from_policy(loaded, policy, package_file_hash(&policy_bytes))
    }

    pub(crate) fn from_policy(
        loaded: &crate::package::LoadedPackageRoot,
        policy: L2AcceptancePolicy,
        policy_hash: PackageHash,
    ) -> Result<Self, Box<CommandDiagnostic>> {
        if policy.policy_version != 2
            || policy.validator_profile != "npa.l2_acceptance.validator.v2"
            || policy.review_protocol != "npa.l2.subagent-review.v2"
        {
            return Err(diagnostic("l2_review_policy_not_current", "--policy"));
        }
        let audit = load_package_audit_snapshot(
            &loaded.root,
            COMMAND,
            PackageGeneratedArtifactReadMode::all(),
            PackageArtifactReferenceSummaryMode::Include,
        )
        .map_err(|_| diagnostic("l2_review_generated_identity_mismatch", "generated"))?;
        let axiom_source = audit
            .checked_generated
            .axiom_report_json
            .as_deref()
            .ok_or_else(|| {
                diagnostic(
                    "l2_review_generated_identity_mismatch",
                    PACKAGE_AXIOM_REPORT_PATH,
                )
            })?;
        let axiom = parse_package_axiom_report_json(axiom_source).map_err(|_| {
            diagnostic(
                "l2_review_generated_identity_mismatch",
                PACKAGE_AXIOM_REPORT_PATH,
            )
        })?;
        let index_source = audit
            .checked_generated
            .theorem_index_json
            .as_deref()
            .ok_or_else(|| {
                diagnostic(
                    "l2_review_theorem_index_missing",
                    PACKAGE_THEOREM_INDEX_PATH,
                )
            })?;
        let index = parse_package_theorem_index_json(index_source).map_err(|_| {
            diagnostic(
                "l2_review_generated_identity_mismatch",
                PACKAGE_THEOREM_INDEX_PATH,
            )
        })?;
        let expected_axiom = audit.snapshot.project_axiom_report().map_err(|_| {
            diagnostic(
                "l2_review_generated_identity_mismatch",
                PACKAGE_AXIOM_REPORT_PATH,
            )
        })?;
        let expected_index = audit.snapshot.project_theorem_index().map_err(|_| {
            diagnostic(
                "l2_review_generated_identity_mismatch",
                PACKAGE_THEOREM_INDEX_PATH,
            )
        })?;
        if axiom != expected_axiom || index != expected_index {
            return Err(diagnostic(
                "l2_review_generated_identity_mismatch",
                "generated",
            ));
        }
        let lock = &audit.snapshot.package_lock_manifest;
        let manifest = loaded.validated.manifest();
        if lock.package != manifest.package
            || lock.version != manifest.version
            || axiom.package != manifest.package
            || axiom.version != manifest.version
            || index.package != manifest.package
            || index.version != manifest.version
        {
            return Err(diagnostic(
                "l2_review_generated_identity_mismatch",
                "npa-package.toml",
            ));
        }
        Ok(Self {
            policy,
            policy_hash,
            audit,
            axiom,
            index,
            inputs: RefCell::new(BTreeMap::new()),
        })
    }

    pub(crate) fn build(
        &self,
        loaded: &crate::package::LoadedPackageRoot,
        module: &str,
        declaration: &str,
    ) -> Result<(L2ReviewInput, Vec<u8>), Box<CommandDiagnostic>> {
        let module_name = Name::from_dotted(module);
        let theorem_name = Name::from_dotted(declaration);
        let key = (module_name.clone(), theorem_name.clone());
        if let Some(input) = self.inputs.borrow().get(&key) {
            return Ok(input.clone());
        }
        let input = self.build_uncached(loaded, module_name, theorem_name)?;
        self.inputs.borrow_mut().insert(key, input.clone());
        Ok(input)
    }

    fn build_uncached(
        &self,
        loaded: &crate::package::LoadedPackageRoot,
        module_name: Name,
        theorem_name: Name,
    ) -> Result<(L2ReviewInput, Vec<u8>), Box<CommandDiagnostic>> {
        let policy = &self.policy;
        let axiom = &self.axiom;
        let index = &self.index;
        let lock = &self.audit.snapshot.package_lock_manifest;
        let manifest = loaded.validated.manifest();
        let module = manifest
            .modules
            .iter()
            .find(|item| item.module == module_name)
            .ok_or_else(|| diagnostic("l2_review_module_missing", "--module"))?;
        let theorem = index
            .entries
            .iter()
            .find(|entry| {
                entry.global_ref.module == module_name
                    && entry.global_ref.name == theorem_name
                    && entry.artifact.origin == PackageArtifactOrigin::Local
            })
            .ok_or_else(|| diagnostic("l2_review_declaration_missing", "--declaration"))?;
        if theorem.kind != npa_package::PackageTheoremIndexKind::Theorem {
            return Err(diagnostic(
                "l2_review_declaration_not_theorem",
                "--declaration",
            ));
        }
        let source_bytes = read_path(
            &loaded.root,
            &module.source,
            "l2_review_manifest_hash_mismatch",
        )?;
        let certificate_bytes = read_path(
            &loaded.root,
            &module.certificate,
            "l2_review_manifest_hash_mismatch",
        )?;
        let certificate = verify_module_cert_hashes(&certificate_bytes).map_err(|_| {
            diagnostic(
                "l2_review_manifest_hash_mismatch",
                module.certificate.as_str(),
            )
        })?;
        if package_file_hash(&source_bytes) != module.expected_source_hash
            || package_file_hash(&certificate_bytes) != module.expected_certificate_file_hash
            || npa_package::PackageHash::from(certificate.hashes.certificate_hash)
                != module.expected_certificate_hash
            || npa_package::PackageHash::from(certificate.hashes.export_hash)
                != module.expected_export_hash
            || npa_package::PackageHash::from(certificate.hashes.axiom_report_hash)
                != module.expected_axiom_report_hash
            || theorem.global_ref.certificate_hash != module.expected_certificate_hash
        {
            return Err(diagnostic(
                "l2_review_manifest_hash_mismatch",
                module.certificate.as_str(),
            ));
        }
        let axiom_module = axiom
            .modules
            .iter()
            .find(|entry| {
                entry.module == module_name && entry.origin == PackageArtifactOrigin::Local
            })
            .ok_or_else(|| {
                diagnostic(
                    "l2_review_generated_identity_mismatch",
                    PACKAGE_AXIOM_REPORT_PATH,
                )
            })?;
        let lock_entry = lock
            .entries
            .iter()
            .find(|entry| {
                entry.module == module_name && entry.origin == PackageLockEntryOrigin::Local
            })
            .ok_or_else(|| {
                diagnostic("l2_review_generated_identity_mismatch", PACKAGE_LOCK_PATH)
            })?;
        let mut imports = Vec::new();
        for import in &lock_entry.imports {
            let provider = lock
                .entries
                .iter()
                .find(|entry| entry.module == import.module)
                .ok_or_else(|| {
                    diagnostic("l2_review_generated_identity_mismatch", PACKAGE_LOCK_PATH)
                })?;
            imports.push(L2ReviewInputImport {
                module: import.module.clone(),
                origin: match provider.origin {
                    PackageLockEntryOrigin::Local => PackageArtifactOrigin::Local,
                    PackageLockEntryOrigin::External => PackageArtifactOrigin::External,
                },
                package: provider
                    .package
                    .clone()
                    .unwrap_or_else(|| manifest.package.clone()),
                version: provider
                    .version
                    .clone()
                    .unwrap_or_else(|| manifest.version.clone()),
                export_hash: import.export_hash,
                certificate_hash: import.certificate_hash,
            });
        }
        let input = L2ReviewInput {
            schema: "npa.l2.review-input.v2".to_owned(),
            policy: L2ReviewInputPolicy {
                policy_id: policy.policy_id.clone(),
                policy_version: policy.policy_version,
                policy_file_hash: self.policy_hash,
                review_protocol: policy.review_protocol.clone(),
                accepted_level: policy.accepted_level.clone(),
                required_roles: policy.required_roles.clone(),
                required_checks: policy.required_checks.clone(),
            },
            source: L2ReviewInputSource {
                package: manifest.package.clone(),
                version: manifest.version.clone(),
                module: module_name,
                theorem: theorem_name,
                source_path: module.source.clone(),
                source_file_hash: package_file_hash(&source_bytes),
                statement_hash: theorem.statement.core_hash,
                certificate_hash: module.expected_certificate_hash,
                certificate_file_hash: module.expected_certificate_file_hash,
                export_hash: module.expected_export_hash,
                axiom_report_hash: axiom_module.axiom_report_hash,
                direct_imports: imports,
            },
            input_hash: package_file_hash(&[]),
            proof_evidence: false,
        }
        .with_computed_hash()
        .map_err(|_| diagnostic("l2_review_generated_identity_mismatch", "review-input"))?;
        let bytes = input
            .canonical_json()
            .map_err(|_| diagnostic("l2_review_output_write_failed", "--out"))?
            .into_bytes();
        Ok((input, bytes))
    }
}

fn read_path(
    root: &Path,
    path: &PackagePath,
    reason: &str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    let full = join_package_path(root, path, path.as_str())?;
    fs::read(full).map_err(|_| diagnostic(reason, path.as_str()))
}

fn diagnostic(reason: &str, path: &str) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path))
}
