//! Implementation of `npa package validate-l2-acceptance`.

use std::{collections::BTreeSet, fs, path::Path};

use npa_package::{
    format_package_hash, package_file_hash, parse_l2_acceptance_json,
    parse_l2_acceptance_policy_json, parse_l2_acceptance_v2_json, parse_package_theorem_index_json,
    L2Acceptance, L2AcceptanceAuthorityStatus, L2AcceptanceEntry, L2AcceptancePolicy,
    PackageArtifactError, PackageArtifactOrigin, PackageTheoremIndex, PackageTheoremIndexEntry,
    PackageTheoremIndexKind,
};

use crate::{
    args::PackageL2AcceptanceOptions,
    diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind},
    package::load_package_root,
    package_artifacts::PACKAGE_THEOREM_INDEX_PATH,
    package_l2_acceptance_aggregate::validate_l2_acceptance_v2_current_with_context,
    package_l2_review_input::L2ReviewInputContext,
};

const COMMAND: &str = "package validate-l2-acceptance";

/// Validate L2 decisions against the canonical authority and current package snapshot.
pub fn run_package_validate_l2_acceptance(options: PackageL2AcceptanceOptions) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let root_display = loaded.root_display.clone();
    let policy_display = display_path(&options.policy);
    let acceptance_display = display_path(&options.acceptance);

    let policy_bytes = match read_file(&options.policy, &policy_display, "l2_policy_read_failed") {
        Ok(bytes) => bytes,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let policy_source = match std::str::from_utf8(&policy_bytes) {
        Ok(source) => source,
        Err(_) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_policy_utf8_failed",
                )
                .with_path(policy_display)],
            );
        }
    };
    let policy = match parse_l2_acceptance_policy_json(policy_source) {
        Ok(policy) => policy,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![artifact_diagnostic(&policy_display, &error)],
            );
        }
    };

    let acceptance_bytes = match read_file(
        &options.acceptance,
        &acceptance_display,
        "l2_acceptance_read_failed",
    ) {
        Ok(bytes) => bytes,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    };
    let acceptance_source = match std::str::from_utf8(&acceptance_bytes) {
        Ok(source) => source,
        Err(_) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_acceptance_utf8_failed",
                )
                .with_path(acceptance_display)],
            );
        }
    };
    if policy.policy_version == 2 {
        return run_v2_validation(
            &options,
            &loaded,
            &policy,
            &policy_bytes,
            acceptance_source,
            &acceptance_display,
            &policy_display,
        );
    }
    let acceptance = match parse_l2_acceptance_json(acceptance_source) {
        Ok(acceptance) => acceptance,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![artifact_diagnostic(&acceptance_display, &error)],
            );
        }
    };

    let theorem_index_path = options.common.root.join(PACKAGE_THEOREM_INDEX_PATH);
    let theorem_index_source = match fs::read_to_string(&theorem_index_path) {
        Ok(source) => source,
        Err(_) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "l2_theorem_index_missing",
                )
                .with_path(PACKAGE_THEOREM_INDEX_PATH)
                .with_expected_value("run `npa package index --root <proofs> --json` first")],
            );
        }
    };
    let theorem_index = match parse_package_theorem_index_json(&theorem_index_source) {
        Ok(index) => index,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![artifact_diagnostic(PACKAGE_THEOREM_INDEX_PATH, &error)],
            );
        }
    };

    let diagnostics = validate_current_snapshot(
        &policy,
        package_file_hash(&policy_bytes),
        &acceptance,
        &loaded,
        &theorem_index,
        &options.modules,
        &acceptance_display,
    );
    if !diagnostics.is_empty() {
        return CommandResult::failed(COMMAND, root_display, diagnostics);
    }

    let selected = selected_entries(&acceptance, &options.modules);
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics.push(
        CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "l2_acceptance_validated")
            .with_path(acceptance_display)
            .with_expected_value("hash-bound unanimous independent sub-agent L2 decisions")
            .with_actual_value(selected.len().to_string()),
    );
    result.diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::PackagePolicy,
            "l2_acceptance_not_proof_evidence",
        )
        .with_path(policy_display)
        .with_expected_value("canonical certificate verification remains authoritative")
        .with_actual_value("promotion-policy metadata only"),
    );
    for entry in selected {
        result.diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "l2_theorem_accepted")
                .with_module(entry.module.as_dotted())
                .with_field(entry.theorem.as_dotted())
                .with_actual_value(
                    entry
                        .approvals
                        .iter()
                        .map(|approval| approval.decision_id.as_str())
                        .collect::<Vec<_>>()
                        .join(","),
                ),
        );
    }
    result
}

fn run_v2_validation(
    options: &PackageL2AcceptanceOptions,
    loaded: &crate::package::LoadedPackageRoot,
    policy: &L2AcceptancePolicy,
    policy_bytes: &[u8],
    acceptance_source: &str,
    acceptance_display: &str,
    policy_display: &str,
) -> CommandResult {
    let root_display = loaded.root_display.clone();
    let ledger = match parse_l2_acceptance_v2_json(acceptance_source) {
        Ok(ledger) => ledger,
        Err(error) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![artifact_diagnostic(acceptance_display, &error)],
            );
        }
    };
    let policy_hash = package_file_hash(policy_bytes);
    let context = match L2ReviewInputContext::from_policy(loaded, policy.clone(), policy_hash) {
        Ok(context) => context,
        Err(diagnostic) => {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    };
    if let Err(diagnostic) = validate_l2_acceptance_v2_current_with_context(
        loaded,
        &ledger,
        policy,
        policy_hash,
        &context,
    ) {
        return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
    }
    let index = context.theorem_index();
    let manifest = loaded.validated.manifest();
    if ledger.source_package != manifest.package
        || ledger.source_version != manifest.version
        || index.package != manifest.package
        || index.version != manifest.version
    {
        return CommandResult::failed(
            COMMAND,
            root_display,
            vec![CommandDiagnostic::error(
                DiagnosticKind::PackagePolicy,
                "l2_generated_identity_mismatch",
            )
            .with_path(acceptance_display)],
        );
    }
    for entry in &ledger.entries {
        let Some(theorem) = index.entries.iter().find(|theorem| {
            theorem.kind == PackageTheoremIndexKind::Theorem
                && theorem.artifact.origin == PackageArtifactOrigin::Local
                && theorem.global_ref.module == entry.module
                && theorem.global_ref.name == entry.theorem
        }) else {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_theorem_not_current",
                )
                .with_module(entry.module.as_dotted())
                .with_field(entry.theorem.as_dotted())],
            );
        };
        if theorem.statement.core_hash != entry.statement_hash
            || theorem.global_ref.certificate_hash != entry.certificate_hash
            || entry.accepted_level != policy.accepted_level
        {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_theorem_hash_mismatch",
                )
                .with_module(entry.module.as_dotted())
                .with_field(entry.theorem.as_dotted())],
            );
        }
    }
    for module in &options.modules {
        for theorem in index.entries.iter().filter(|theorem| {
            theorem.kind == PackageTheoremIndexKind::Theorem
                && theorem.artifact.origin == PackageArtifactOrigin::Local
                && theorem.global_ref.module == *module
        }) {
            if !ledger
                .entries
                .iter()
                .any(|entry| entry.module == *module && entry.theorem == theorem.global_ref.name)
            {
                return CommandResult::failed(
                    COMMAND,
                    root_display,
                    vec![CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_selected_module_theorem_missing",
                    )
                    .with_module(module.as_dotted())
                    .with_field(theorem.global_ref.name.as_dotted())],
                );
            }
        }
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics.push(
        CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "l2_acceptance_validated")
            .with_path(acceptance_display)
            .with_actual_value(ledger.entries.len().to_string()),
    );
    result.diagnostics.push(
        CommandDiagnostic::info(
            DiagnosticKind::PackagePolicy,
            "l2_acceptance_not_proof_evidence",
        )
        .with_path(policy_display),
    );
    result
}

fn validate_current_snapshot(
    policy: &L2AcceptancePolicy,
    policy_file_hash: npa_package::PackageHash,
    acceptance: &L2Acceptance,
    loaded: &crate::package::LoadedPackageRoot,
    theorem_index: &PackageTheoremIndex,
    selected_modules: &[npa_cert::Name],
    acceptance_path: &str,
) -> Vec<CommandDiagnostic> {
    let mut diagnostics = Vec::new();
    if acceptance.policy_id != policy.policy_id {
        diagnostics.push(value_mismatch(
            acceptance_path,
            "policy_id",
            &policy.policy_id,
            &acceptance.policy_id,
        ));
    }
    if acceptance.policy_version != policy.policy_version {
        diagnostics.push(value_mismatch(
            acceptance_path,
            "policy_version",
            policy.policy_version.to_string(),
            acceptance.policy_version.to_string(),
        ));
    }
    if acceptance.policy_file_hash != policy_file_hash {
        diagnostics.push(hash_mismatch(
            acceptance_path,
            "policy_file_hash",
            policy_file_hash,
            acceptance.policy_file_hash,
        ));
    }

    let manifest = loaded.validated.manifest();
    if acceptance.source_package != manifest.package {
        diagnostics.push(value_mismatch(
            acceptance_path,
            "source_package",
            manifest.package.as_str(),
            acceptance.source_package.as_str(),
        ));
    }
    if acceptance.source_version != manifest.version {
        diagnostics.push(value_mismatch(
            acceptance_path,
            "source_version",
            manifest.version.as_str(),
            acceptance.source_version.as_str(),
        ));
    }
    if theorem_index.package != manifest.package {
        diagnostics.push(value_mismatch(
            PACKAGE_THEOREM_INDEX_PATH,
            "package",
            manifest.package.as_str(),
            theorem_index.package.as_str(),
        ));
    }
    if theorem_index.version != manifest.version {
        diagnostics.push(value_mismatch(
            PACKAGE_THEOREM_INDEX_PATH,
            "version",
            manifest.version.as_str(),
            theorem_index.version.as_str(),
        ));
    }

    for entry in &acceptance.entries {
        validate_entry(
            policy,
            entry,
            theorem_index,
            &manifest.modules,
            acceptance_path,
            &mut diagnostics,
        );
    }

    for module in selected_modules {
        let module_name = module.as_dotted();
        let current = theorem_index
            .entries
            .iter()
            .filter(|entry| {
                entry.kind == PackageTheoremIndexKind::Theorem
                    && entry.artifact.origin == PackageArtifactOrigin::Local
                    && entry.global_ref.module == *module
            })
            .collect::<Vec<_>>();
        if current.is_empty() {
            diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_selected_module_has_no_local_theorems",
                )
                .with_path(PACKAGE_THEOREM_INDEX_PATH)
                .with_module(module_name),
            );
            continue;
        }
        let accepted = acceptance
            .entries
            .iter()
            .filter(|entry| entry.module == *module)
            .map(|entry| entry.theorem.as_dotted())
            .collect::<BTreeSet<_>>();
        for entry in current {
            let theorem = entry.global_ref.name.as_dotted();
            if !accepted.contains(&theorem) {
                diagnostics.push(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_selected_module_theorem_missing",
                    )
                    .with_path(acceptance_path)
                    .with_module(module.as_dotted())
                    .with_field(theorem)
                    .with_expected_value("current hash-bound L2 acceptance")
                    .with_actual_value("missing"),
                );
            }
        }
    }
    diagnostics
}

fn validate_entry(
    policy: &L2AcceptancePolicy,
    entry: &L2AcceptanceEntry,
    theorem_index: &PackageTheoremIndex,
    manifest_modules: &[npa_package::PackageModule],
    acceptance_path: &str,
    diagnostics: &mut Vec<CommandDiagnostic>,
) {
    let required_roles = policy.required_roles.iter().collect::<BTreeSet<_>>();
    let approval_roles = entry
        .approvals
        .iter()
        .map(|approval| &approval.reviewer_role)
        .collect::<BTreeSet<_>>();
    if approval_roles != required_roles {
        diagnostics.push(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "l2_review_quorum_mismatch")
                .with_path(acceptance_path)
                .with_module(entry.module.as_dotted())
                .with_field("approvals")
                .with_expected_value(policy.required_roles.join(","))
                .with_actual_value(
                    entry
                        .approvals
                        .iter()
                        .map(|approval| approval.reviewer_role.as_str())
                        .collect::<Vec<_>>()
                        .join(","),
                ),
        );
    }

    let required_checks = policy.required_checks.iter().collect::<BTreeSet<_>>();
    for approval in &entry.approvals {
        let authority = policy.authorities.iter().find(|authority| {
            authority.authority == approval.authority
                && authority.authority_version == approval.authority_version
        });
        match authority {
            None => diagnostics.push(
                CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "l2_authority_not_allowed")
                    .with_path(acceptance_path)
                    .with_module(entry.module.as_dotted())
                    .with_field("authority")
                    .with_actual_value(format!(
                        "{}@{}",
                        approval.authority, approval.authority_version
                    )),
            ),
            Some(authority) if authority.status != L2AcceptanceAuthorityStatus::Active => {
                diagnostics.push(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_authority_not_active",
                    )
                    .with_path(acceptance_path)
                    .with_module(entry.module.as_dotted())
                    .with_field("authority")
                    .with_expected_value("active")
                    .with_actual_value(authority.status.as_str()),
                );
            }
            Some(authority) if authority.reviewer_role != approval.reviewer_role => {
                diagnostics.push(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_reviewer_role_mismatch",
                    )
                    .with_path(acceptance_path)
                    .with_module(entry.module.as_dotted())
                    .with_field("reviewer_role")
                    .with_expected_value(&authority.reviewer_role)
                    .with_actual_value(&approval.reviewer_role),
                );
            }
            Some(authority)
                if !approval
                    .agent_task
                    .starts_with(&authority.agent_task_prefix) =>
            {
                diagnostics.push(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_agent_task_prefix_mismatch",
                    )
                    .with_path(acceptance_path)
                    .with_module(entry.module.as_dotted())
                    .with_field("agent_task")
                    .with_expected_value(&authority.agent_task_prefix)
                    .with_actual_value(&approval.agent_task),
                );
            }
            Some(authority)
                if !approval
                    .decision_id
                    .starts_with(&authority.decision_id_prefix) =>
            {
                diagnostics.push(
                    CommandDiagnostic::error(
                        DiagnosticKind::PackagePolicy,
                        "l2_decision_id_prefix_mismatch",
                    )
                    .with_path(acceptance_path)
                    .with_module(entry.module.as_dotted())
                    .with_field("decision_id")
                    .with_expected_value(&authority.decision_id_prefix)
                    .with_actual_value(&approval.decision_id),
                );
            }
            Some(_) => {}
        }
        if approval.review_protocol != policy.review_protocol {
            diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_review_protocol_mismatch",
                )
                .with_path(acceptance_path)
                .with_module(entry.module.as_dotted())
                .with_field("review_protocol")
                .with_expected_value(&policy.review_protocol)
                .with_actual_value(&approval.review_protocol),
            );
        }
        let actual_checks = approval.checks.iter().collect::<BTreeSet<_>>();
        if actual_checks != required_checks {
            diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::PackagePolicy,
                    "l2_review_checks_mismatch",
                )
                .with_path(acceptance_path)
                .with_module(entry.module.as_dotted())
                .with_field("checks")
                .with_expected_value(policy.required_checks.join(","))
                .with_actual_value(approval.checks.join(",")),
            );
        }
    }

    let current = theorem_index.entries.iter().find(|current| {
        current.kind == PackageTheoremIndexKind::Theorem
            && current.artifact.origin == PackageArtifactOrigin::Local
            && current.global_ref.module == entry.module
            && current.global_ref.name == entry.theorem
    });
    let Some(current) = current else {
        diagnostics.push(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "l2_local_theorem_not_found")
                .with_path(PACKAGE_THEOREM_INDEX_PATH)
                .with_module(entry.module.as_dotted())
                .with_field(entry.theorem.as_dotted()),
        );
        return;
    };
    match manifest_modules
        .iter()
        .find(|module| module.module == entry.module)
    {
        Some(module) if module.expected_certificate_hash != current.global_ref.certificate_hash => {
            diagnostics.push(
                hash_mismatch(
                    PACKAGE_THEOREM_INDEX_PATH,
                    "certificate_hash",
                    module.expected_certificate_hash,
                    current.global_ref.certificate_hash,
                )
                .with_module(entry.module.as_dotted()),
            );
        }
        None => diagnostics.push(
            CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "l2_manifest_module_missing")
                .with_path("npa-package.toml")
                .with_module(entry.module.as_dotted()),
        ),
        Some(_) => {}
    }
    compare_entry_hashes(entry, current, acceptance_path, diagnostics);
}

fn compare_entry_hashes(
    accepted: &L2AcceptanceEntry,
    current: &PackageTheoremIndexEntry,
    acceptance_path: &str,
    diagnostics: &mut Vec<CommandDiagnostic>,
) {
    if accepted.statement_hash != current.statement.core_hash {
        diagnostics.push(
            hash_mismatch(
                acceptance_path,
                "statement_hash",
                current.statement.core_hash,
                accepted.statement_hash,
            )
            .with_module(accepted.module.as_dotted()),
        );
    }
    if accepted.certificate_hash != current.global_ref.certificate_hash {
        diagnostics.push(
            hash_mismatch(
                acceptance_path,
                "certificate_hash",
                current.global_ref.certificate_hash,
                accepted.certificate_hash,
            )
            .with_module(accepted.module.as_dotted()),
        );
    }
}

fn selected_entries<'a>(
    acceptance: &'a L2Acceptance,
    modules: &[npa_cert::Name],
) -> Vec<&'a L2AcceptanceEntry> {
    acceptance
        .entries
        .iter()
        .filter(|entry| modules.is_empty() || modules.contains(&entry.module))
        .collect()
}

fn read_file(
    path: &Path,
    display: &str,
    reason: &'static str,
) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
    fs::read(path).map_err(|_| {
        Box::new(CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason).with_path(display))
    })
}

fn artifact_diagnostic(path: &str, error: &PackageArtifactError) -> CommandDiagnostic {
    let mut diagnostic =
        CommandDiagnostic::error(DiagnosticKind::PackagePolicy, error.reason_code.as_str())
            .with_path(path)
            .with_field(&error.path);
    if let Some(expected) = &error.expected_value {
        diagnostic = diagnostic.with_expected_value(expected);
    }
    if let Some(actual) = &error.actual_value {
        diagnostic = diagnostic.with_actual_value(actual);
    }
    diagnostic
}

fn hash_mismatch(
    path: &str,
    field: &str,
    expected: npa_package::PackageHash,
    actual: npa_package::PackageHash,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::HashMismatch, "l2_hash_mismatch")
        .with_path(path)
        .with_field(field)
        .with_hashes(format_package_hash(&expected), format_package_hash(&actual))
}

fn value_mismatch(
    path: &str,
    field: &str,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::PackagePolicy, "l2_value_mismatch")
        .with_path(path)
        .with_field(field)
        .with_expected_value(expected)
        .with_actual_value(actual)
}

fn display_path(path: &Path) -> String {
    if path.as_os_str().is_empty() {
        ".".to_owned()
    } else if path.is_absolute() {
        "<absolute-path>".to_owned()
    } else {
        path.to_string_lossy().replace('\\', "/")
    }
}
