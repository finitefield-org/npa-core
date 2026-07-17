//! Implementation of `npa package aggregate-l2-acceptance`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
};

use npa_package::{
    merge_l2_acceptance_v2_entries, package_file_hash, parse_l2_acceptance_policy_json,
    parse_l2_acceptance_v2_json, parse_l2_review_input_json, parse_l2_review_report_json,
    L2AcceptanceApprovalV2, L2AcceptanceAuthorityStatus, L2AcceptanceEntryV2,
    L2AcceptanceReviewReportRef, L2AcceptanceV2, L2ReviewInput, L2ReviewReport, PackagePath,
};

use crate::{
    args::PackageL2AcceptanceAggregateOptions,
    diagnostic::{CommandArtifact, CommandDiagnostic, CommandResult, DiagnosticKind},
    fs::render_package_path,
    governance_writer::{
        confined_governance_path, lock_governance_artifact, write_governance_artifact,
        GovernanceArtifactLock, GovernanceOutputPolicy,
    },
    package::load_package_root,
    package_l2_review_input::L2ReviewInputContext,
};

const COMMAND: &str = "package aggregate-l2-acceptance";

struct AggregatedAcceptance {
    bytes: Vec<u8>,
    existing_snapshot: Option<Vec<u8>>,
}

#[derive(Default)]
pub(crate) struct L2AcceptanceFileSnapshot {
    files: BTreeMap<PackagePath, Vec<u8>>,
}

impl L2AcceptanceFileSnapshot {
    fn capture(
        &mut self,
        path: PackagePath,
        bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
        if let Some(existing) = self.files.get(&path) {
            if existing != &bytes {
                return Err(diagnostic("l2_acceptance_concurrent_update", path.as_str()));
            }
            return Ok(existing.clone());
        }
        self.files.insert(path, bytes.clone());
        Ok(bytes)
    }

    fn read(
        &mut self,
        root: &std::path::Path,
        path: &PackagePath,
        reason: &str,
    ) -> Result<Vec<u8>, Box<CommandDiagnostic>> {
        if let Some(bytes) = self.files.get(path) {
            return Ok(bytes.clone());
        }
        let full = confined_governance_path(root, path, path.as_str(), reason)?;
        let bytes = fs::read(full).map_err(|_| diagnostic(reason, path.as_str()))?;
        self.capture(path.clone(), bytes)
    }
}

/// Aggregate unchanged unanimous review reports into a report-backed v2 ledger.
pub fn run_package_aggregate_l2_acceptance(
    options: PackageL2AcceptanceAggregateOptions,
) -> CommandResult {
    let loaded = match load_package_root(&options.common.root, COMMAND) {
        Ok(loaded) => loaded,
        Err(result) => return result,
    };
    let root_display = loaded.root_display.clone();
    let out = PackagePath::new(options.out.to_string_lossy());
    let full_out = match confined_governance_path(
        &loaded.root,
        &out,
        "--out",
        "l2_aggregate_output_not_package_relative",
    ) {
        Ok(path) => path,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let in_place = options
        .existing
        .as_ref()
        .is_some_and(|path| path == &options.out);
    let mut in_place_lock = None;
    let result = aggregate(&loaded, &options, &mut in_place_lock);
    let output = match result {
        Ok(value) => value,
        Err(diagnostic) => return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]),
    };
    let bytes = output.bytes;
    let existing_snapshot = output.existing_snapshot;
    if options.check {
        if !check_output_matches(&full_out, &bytes, existing_snapshot.as_deref(), in_place) {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![CommandDiagnostic::error(
                    DiagnosticKind::GeneratedArtifact,
                    "l2_aggregate_output_stale",
                )
                .with_path(render_package_path(&out))],
            );
        }
    } else {
        let write = if in_place {
            in_place_lock.as_ref().map_or_else(
                || Err(diagnostic("l2_aggregate_concurrent_update", out.as_str())),
                |lock| {
                    lock.replace_if_unchanged(
                        &bytes,
                        existing_snapshot.as_deref().unwrap_or_default(),
                    )
                },
            )
        } else {
            write_governance_artifact(
                &loaded.root,
                &out,
                &bytes,
                GovernanceOutputPolicy::CreateOrIdentical,
                "l2_aggregate",
            )
        };
        if let Err(diagnostic) = write {
            return CommandResult::failed(COMMAND, root_display, vec![*diagnostic]);
        }
    }
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.artifacts.push(CommandArtifact {
        kind: "l2_acceptance".to_owned(),
        path: render_package_path(&out),
    });
    result.diagnostics.push(CommandDiagnostic::info(
        DiagnosticKind::PackagePolicy,
        "l2_acceptance_aggregated",
    ));
    result
}

fn check_output_matches(
    full_out: &std::path::Path,
    expected: &[u8],
    existing_snapshot: Option<&[u8]>,
    in_place: bool,
) -> bool {
    if in_place {
        existing_snapshot == Some(expected)
    } else {
        fs::read(full_out).ok().as_deref() == Some(expected)
    }
}

fn aggregate(
    loaded: &crate::package::LoadedPackageRoot,
    options: &PackageL2AcceptanceAggregateOptions,
    in_place_lock: &mut Option<GovernanceArtifactLock>,
) -> Result<AggregatedAcceptance, Box<CommandDiagnostic>> {
    let policy_bytes = fs::read(&options.policy)
        .map_err(|_| diagnostic("l2_aggregate_policy_mismatch", "--policy"))?;
    let policy = parse_l2_acceptance_policy_json(
        std::str::from_utf8(&policy_bytes)
            .map_err(|_| diagnostic("l2_aggregate_policy_mismatch", "--policy"))?,
    )
    .map_err(|_| diagnostic("l2_aggregate_policy_mismatch", "--policy"))?;
    if policy.policy_version != 2
        || policy.validator_profile != "npa.l2_acceptance.validator.v2"
        || policy.review_protocol != "npa.l2.subagent-review.v2"
    {
        return Err(diagnostic("l2_aggregate_policy_mismatch", "--policy"));
    }
    let policy_hash = package_file_hash(&policy_bytes);
    let review_context = L2ReviewInputContext::from_policy(loaded, policy.clone(), policy_hash)
        .map_err(|_| diagnostic("l2_aggregate_input_stale", "generated"))?;
    let mut file_snapshot = L2AcceptanceFileSnapshot::default();
    let mut inputs = Vec::new();
    for path in &options.review_inputs {
        let package_path = PackagePath::new(path.to_string_lossy());
        let bytes = file_snapshot.read(
            &loaded.root,
            &package_path,
            "l2_aggregate_input_noncanonical",
        )?;
        let source = std::str::from_utf8(&bytes)
            .map_err(|_| diagnostic("l2_aggregate_input_noncanonical", package_path.as_str()))?;
        let input = parse_l2_review_input_json(source)
            .map_err(|_| diagnostic("l2_aggregate_input_noncanonical", package_path.as_str()))?;
        let current = review_context
            .build(
                loaded,
                &input.source.module.as_dotted(),
                &input.source.theorem.as_dotted(),
            )
            .map_err(|_| diagnostic("l2_aggregate_input_stale", package_path.as_str()))?
            .0;
        if input != current {
            return Err(diagnostic(
                "l2_aggregate_input_stale",
                package_path.as_str(),
            ));
        }
        inputs.push((package_path, bytes, input));
    }
    let mut reports = Vec::new();
    for path in &options.reviews {
        let package_path = PackagePath::new(path.to_string_lossy());
        let bytes = file_snapshot.read(
            &loaded.root,
            &package_path,
            "l2_aggregate_report_noncanonical",
        )?;
        let report =
            parse_l2_review_report_json(std::str::from_utf8(&bytes).map_err(|_| {
                diagnostic("l2_aggregate_report_noncanonical", package_path.as_str())
            })?)
            .map_err(|_| diagnostic("l2_aggregate_report_noncanonical", package_path.as_str()))?;
        reports.push((package_path, bytes, report));
    }

    let mut new_entries = Vec::new();
    let mut used_reports = BTreeSet::new();
    for (input_path, input_bytes, input) in &inputs {
        validate_input_policy(input, &policy, package_file_hash(&policy_bytes))?;
        let matching = reports
            .iter()
            .enumerate()
            .filter(|(_, (_, _, report))| report.input_hash == input.input_hash)
            .collect::<Vec<_>>();
        if matching.len() != policy.required_roles.len() {
            return Err(diagnostic(
                "l2_aggregate_quorum_incomplete",
                input_path.as_str(),
            ));
        }
        let mut roles = BTreeSet::new();
        let mut tasks = BTreeSet::new();
        let mut approvals = Vec::new();
        for (report_index, (report_path, report_bytes, report)) in matching {
            used_reports.insert(report_index);
            validate_report(
                report,
                report_path,
                input,
                input_path,
                input_bytes,
                &policy,
                package_file_hash(&policy_bytes),
            )?;
            if !roles.insert(report.reviewer_role.clone())
                || !tasks.insert(report.agent_task.clone())
            {
                return Err(diagnostic(
                    "l2_aggregate_reviewer_task_reused",
                    report_path.as_str(),
                ));
            }
            approvals.push(L2AcceptanceApprovalV2 {
                authority: report.authority.clone(),
                authority_version: report.authority_version,
                decision_id: report.decision_id.clone(),
                reviewer_role: report.reviewer_role.clone(),
                agent_task: report.agent_task.clone(),
                review_protocol: report.review_protocol.clone(),
                input_hash: report.input_hash,
                review_report: L2AcceptanceReviewReportRef {
                    path: report_path.clone(),
                    file_hash: package_file_hash(report_bytes),
                },
                verdict: report.verdict.clone(),
            });
        }
        if roles != policy.required_roles.iter().cloned().collect() {
            return Err(diagnostic(
                "l2_aggregate_quorum_incomplete",
                input_path.as_str(),
            ));
        }
        new_entries.push(L2AcceptanceEntryV2 {
            module: input.source.module.clone(),
            theorem: input.source.theorem.clone(),
            statement_hash: input.source.statement_hash,
            certificate_hash: input.source.certificate_hash,
            accepted_level: input.policy.accepted_level.clone(),
            approvals,
        });
    }
    if used_reports.len() != reports.len() {
        return Err(diagnostic("l2_aggregate_quorum_conflict", "--review"));
    }
    let manifest = loaded.validated.manifest();
    let mut existing_snapshot = None;
    let base = if let Some(existing) = &options.existing {
        let path = PackagePath::new(existing.to_string_lossy());
        let in_place_write = !options.check && existing == &options.out;
        let bytes = if in_place_write {
            let lock = lock_governance_artifact(&loaded.root, &path, "l2_aggregate")?;
            let bytes = lock
                .read_existing()
                .map_err(|_| diagnostic("l2_aggregate_existing_stale", path.as_str()))?;
            let bytes = file_snapshot.capture(path.clone(), bytes)?;
            *in_place_lock = Some(lock);
            bytes
        } else {
            file_snapshot.read(&loaded.root, &path, "l2_aggregate_existing_stale")?
        };
        if existing == &options.out {
            existing_snapshot = Some(bytes.clone());
        }
        let ledger = parse_l2_acceptance_v2_json(
            std::str::from_utf8(&bytes)
                .map_err(|_| diagnostic("l2_aggregate_existing_stale", path.as_str()))?,
        )
        .map_err(|_| diagnostic("l2_aggregate_existing_stale", path.as_str()))?;
        if ledger.source_package != manifest.package || ledger.source_version != manifest.version {
            return Err(diagnostic("l2_aggregate_existing_stale", path.as_str()));
        }
        validate_l2_acceptance_v2_current_with_context_and_snapshot(
            loaded,
            &ledger,
            &policy,
            policy_hash,
            &review_context,
            &mut file_snapshot,
        )?;
        for entry in &ledger.entries {
            let current = review_context
                .build(
                    loaded,
                    &entry.module.as_dotted(),
                    &entry.theorem.as_dotted(),
                )
                .map_err(|_| diagnostic("l2_aggregate_existing_stale", path.as_str()))?
                .0;
            if current.source.statement_hash != entry.statement_hash
                || current.source.certificate_hash != entry.certificate_hash
                || entry
                    .approvals
                    .iter()
                    .any(|approval| approval.input_hash != current.input_hash)
            {
                return Err(diagnostic("l2_aggregate_existing_stale", path.as_str()));
            }
        }
        ledger
    } else {
        L2AcceptanceV2 {
            schema: "npa.l2_acceptance.v2".to_owned(),
            policy_id: policy.policy_id.clone(),
            policy_version: policy.policy_version,
            policy_file_hash: policy_hash,
            source_package: manifest.package.clone(),
            source_version: manifest.version.clone(),
            aggregator_agent_task: "/root".to_owned(),
            entries: Vec::new(),
            proof_evidence: false,
        }
    };
    let replacements = options
        .replacements
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let new_keys = new_entries
        .iter()
        .map(|entry| (entry.module.clone(), entry.theorem.clone()))
        .collect::<BTreeSet<_>>();
    if !replacements.is_subset(&new_keys) {
        return Err(diagnostic(
            "l2_aggregate_replacement_not_authorized",
            "--replace",
        ));
    }
    let ledger = merge_l2_acceptance_v2_entries(base, new_entries, &replacements)
        .map_err(|_| diagnostic("l2_aggregate_replacement_not_authorized", "--replace"))?;
    validate_l2_acceptance_v2_current_with_context_and_snapshot(
        loaded,
        &ledger,
        &policy,
        policy_hash,
        &review_context,
        &mut file_snapshot,
    )?;
    Ok(AggregatedAcceptance {
        bytes: ledger
            .canonical_json()
            .map_err(|_| diagnostic("l2_aggregate_output_write_failed", "--out"))?
            .into_bytes(),
        existing_snapshot,
    })
}

/// Validate a v2 ledger against its policy and immutable reports.
pub(crate) fn validate_l2_acceptance_v2_current(
    loaded: &crate::package::LoadedPackageRoot,
    ledger: &L2AcceptanceV2,
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    let context = L2ReviewInputContext::from_policy(loaded, policy.clone(), policy_hash)
        .map_err(|_| diagnostic("l2_acceptance_input_stale", "generated"))?;
    validate_l2_acceptance_v2_current_with_context(loaded, ledger, policy, policy_hash, &context)
}

pub(crate) fn validate_l2_acceptance_v2_current_with_context(
    loaded: &crate::package::LoadedPackageRoot,
    ledger: &L2AcceptanceV2,
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
    context: &L2ReviewInputContext,
) -> Result<(), Box<CommandDiagnostic>> {
    let mut file_snapshot = L2AcceptanceFileSnapshot::default();
    validate_l2_acceptance_v2_current_with_context_and_snapshot(
        loaded,
        ledger,
        policy,
        policy_hash,
        context,
        &mut file_snapshot,
    )
}

pub(crate) fn validate_l2_acceptance_v2_current_with_context_and_snapshot(
    loaded: &crate::package::LoadedPackageRoot,
    ledger: &L2AcceptanceV2,
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
    context: &L2ReviewInputContext,
    file_snapshot: &mut L2AcceptanceFileSnapshot,
) -> Result<(), Box<CommandDiagnostic>> {
    let manifest = loaded.validated.manifest();
    if ledger.source_package != manifest.package || ledger.source_version != manifest.version {
        return Err(diagnostic(
            "l2_acceptance_generated_identity_mismatch",
            "l2-acceptance.json",
        ));
    }
    if ledger.policy_id != policy.policy_id
        || ledger.policy_version != policy.policy_version
        || ledger.policy_file_hash != policy_hash
    {
        return Err(diagnostic(
            "l2_acceptance_policy_mismatch",
            "l2-acceptance.json",
        ));
    }
    for entry in &ledger.entries {
        let current = context
            .build(
                loaded,
                &entry.module.as_dotted(),
                &entry.theorem.as_dotted(),
            )
            .map_err(|_| diagnostic("l2_acceptance_input_stale", &entry.module.as_dotted()))?
            .0;
        let mut roles = BTreeSet::new();
        let mut tasks = BTreeSet::new();
        for approval in &entry.approvals {
            let bytes = file_snapshot.read(
                &loaded.root,
                &approval.review_report.path,
                "l2_acceptance_report_missing",
            )?;
            if package_file_hash(&bytes) != approval.review_report.file_hash {
                return Err(diagnostic(
                    "l2_acceptance_report_hash_mismatch",
                    approval.review_report.path.as_str(),
                ));
            }
            let report =
                parse_l2_review_report_json(std::str::from_utf8(&bytes).map_err(|_| {
                    diagnostic(
                        "l2_acceptance_report_noncanonical",
                        approval.review_report.path.as_str(),
                    )
                })?)
                .map_err(|_| {
                    diagnostic(
                        "l2_acceptance_report_noncanonical",
                        approval.review_report.path.as_str(),
                    )
                })?;
            if approval.authority != report.authority
                || approval.authority_version != report.authority_version
                || approval.decision_id != report.decision_id
                || approval.reviewer_role != report.reviewer_role
                || approval.agent_task != report.agent_task
                || approval.review_protocol != report.review_protocol
                || approval.input_hash != report.input_hash
                || approval.verdict != report.verdict
                || report.verdict != "accepted"
            {
                return Err(diagnostic(
                    "l2_acceptance_report_projection_mismatch",
                    approval.review_report.path.as_str(),
                ));
            }
            validate_report_policy(&report, policy, policy_hash)?;
            validate_report_authority(&report, policy, approval.review_report.path.as_str())?;
            let input_bytes = file_snapshot.read(
                &loaded.root,
                &report.input_path,
                "l2_acceptance_input_missing",
            )?;
            if package_file_hash(&input_bytes) != report.input_file_hash {
                return Err(diagnostic(
                    "l2_acceptance_input_hash_mismatch",
                    report.input_path.as_str(),
                ));
            }
            let input =
                parse_l2_review_input_json(std::str::from_utf8(&input_bytes).map_err(|_| {
                    diagnostic(
                        "l2_acceptance_input_noncanonical",
                        report.input_path.as_str(),
                    )
                })?)
                .map_err(|_| {
                    diagnostic(
                        "l2_acceptance_input_noncanonical",
                        report.input_path.as_str(),
                    )
                })?;
            if input.input_hash != report.input_hash
                || input.source.module != entry.module
                || input.source.theorem != entry.theorem
                || input.source.statement_hash != entry.statement_hash
                || input.source.certificate_hash != entry.certificate_hash
                || input.policy.policy_id != policy.policy_id
                || input.policy.policy_version != policy.policy_version
                || input.policy.policy_file_hash != policy_hash
            {
                return Err(diagnostic(
                    "l2_acceptance_input_stale",
                    report.input_path.as_str(),
                ));
            }
            validate_input_policy(&input, policy, policy_hash)?;
            if input != current {
                return Err(diagnostic(
                    "l2_acceptance_input_stale",
                    report.input_path.as_str(),
                ));
            }
            roles.insert(report.reviewer_role.clone());
            tasks.insert(report.agent_task.clone());
        }
        if roles != policy.required_roles.iter().cloned().collect()
            || tasks.len() != policy.required_roles.len()
            || entry.accepted_level != policy.accepted_level
        {
            return Err(diagnostic(
                "l2_acceptance_quorum_incomplete",
                &entry.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_input_policy(
    input: &L2ReviewInput,
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    if input.policy.policy_id != policy.policy_id
        || input.policy.policy_version != policy.policy_version
        || input.policy.policy_file_hash != policy_hash
        || input.policy.review_protocol != policy.review_protocol
        || input.policy.accepted_level != policy.accepted_level
        || input.policy.required_roles != policy.required_roles
        || input.policy.required_checks != policy.required_checks
    {
        return Err(diagnostic("l2_aggregate_input_stale", "--review-input"));
    }
    Ok(())
}

fn validate_report(
    report: &L2ReviewReport,
    report_path: &PackagePath,
    input: &L2ReviewInput,
    input_path: &PackagePath,
    input_bytes: &[u8],
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    validate_report_policy(report, policy, policy_hash)?;
    if &report.input_path != input_path
        || report.input_file_hash != package_file_hash(input_bytes)
        || report.input_hash != input.input_hash
    {
        return Err(diagnostic(
            "l2_aggregate_report_hash_mismatch",
            report_path.as_str(),
        ));
    }
    validate_report_authority(report, policy, report_path.as_str())?;
    if report.verdict != "accepted" {
        return Err(diagnostic(
            "l2_aggregate_non_accept_verdict",
            report_path.as_str(),
        ));
    }
    Ok(())
}

fn validate_report_policy(
    report: &L2ReviewReport,
    policy: &npa_package::L2AcceptancePolicy,
    policy_hash: npa_package::PackageHash,
) -> Result<(), Box<CommandDiagnostic>> {
    if report.policy_id != policy.policy_id
        || report.policy_version != policy.policy_version
        || report.policy_file_hash != policy_hash
        || report.review_protocol != policy.review_protocol
        || report
            .check_results
            .iter()
            .map(|result| &result.check)
            .ne(policy.required_checks.iter())
    {
        return Err(diagnostic(
            "l2_aggregate_report_policy_mismatch",
            "--review",
        ));
    }
    Ok(())
}

fn validate_report_authority(
    report: &L2ReviewReport,
    policy: &npa_package::L2AcceptancePolicy,
    path: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    let authority = policy
        .authorities
        .iter()
        .find(|authority| {
            authority.authority == report.authority
                && authority.authority_version == report.authority_version
                && authority.status == L2AcceptanceAuthorityStatus::Active
        })
        .ok_or_else(|| diagnostic("l2_aggregate_unknown_authority", path))?;
    if authority.reviewer_role != report.reviewer_role
        || !report.agent_task.starts_with(&authority.agent_task_prefix)
        || !report
            .decision_id
            .starts_with(&authority.decision_id_prefix)
    {
        return Err(diagnostic("l2_aggregate_unknown_authority", path));
    }
    Ok(())
}

fn diagnostic(reason: &str, path: &str) -> Box<CommandDiagnostic> {
    Box::new(CommandDiagnostic::error(DiagnosticKind::PackagePolicy, reason).with_path(path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn acceptance_file_snapshot_reuses_the_first_bytes() {
        let root =
            std::env::temp_dir().join(format!("npa-l2-acceptance-snapshot-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        let path = PackagePath::new("review.json");
        fs::write(root.join(path.as_str()), b"first").unwrap();

        let mut snapshot = L2AcceptanceFileSnapshot::default();
        assert_eq!(snapshot.read(&root, &path, "read").unwrap(), b"first");
        fs::write(root.join(path.as_str()), b"second").unwrap();
        assert_eq!(snapshot.read(&root, &path, "read").unwrap(), b"first");

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn in_place_check_uses_the_existing_snapshot_without_rereading_output() {
        let missing = std::env::temp_dir().join(format!(
            "npa-l2-acceptance-missing-output-{}",
            std::process::id()
        ));
        let _ = fs::remove_file(&missing);

        assert!(check_output_matches(
            &missing,
            b"captured",
            Some(b"captured"),
            true,
        ));
        assert!(!check_output_matches(
            &missing,
            b"captured",
            Some(b"different"),
            true,
        ));
        assert!(!check_output_matches(
            &missing,
            b"captured",
            Some(b"captured"),
            false,
        ));
    }
}
