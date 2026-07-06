//! `npa package gate-plan` command.

use std::process::Command;

use npa_package::{package_gate_plan_from_paths, PackageGatePlan};

use crate::args::PackageGatePlanOptions;
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::render_package_root;

const COMMAND: &str = "package gate-plan";

/// Run `npa package gate-plan`.
pub fn run_package_gate_plan(options: PackageGatePlanOptions) -> CommandResult {
    let root_display = render_package_root(&options.common.root);
    let changed_files = match changed_files_from_git_base(&options.base) {
        Ok(paths) => paths,
        Err(message) => {
            return CommandResult::failed(
                COMMAND,
                root_display,
                vec![
                    CommandDiagnostic::error(DiagnosticKind::Internal, "git_diff_failed")
                        .with_field("--base")
                        .with_actual_value(message),
                ],
            );
        }
    };
    let plan = package_gate_plan_from_paths(changed_files);
    command_result_from_gate_plan(root_display, &options.base, &plan)
}

fn changed_files_from_git_base(base: &str) -> Result<Vec<String>, String> {
    let repo_root = git_repo_root()?;
    let range = format!("{base}...HEAD");
    let output = Command::new("git")
        .args(["diff", "--name-only", &range])
        .current_dir(repo_root)
        .output()
        .map_err(|error| format!("failed to run git diff: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            return Err(format!("git diff exited with status {}", output.status));
        }
        return Err(stderr);
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::to_owned)
        .collect())
}

fn git_repo_root() -> Result<String, String> {
    let output = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .map_err(|error| format!("failed to run git rev-parse: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            return Err(format!(
                "git rev-parse exited with status {}",
                output.status
            ));
        }
        return Err(stderr);
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn command_result_from_gate_plan(
    root_display: String,
    base: &str,
    plan: &PackageGatePlan,
) -> CommandResult {
    let mut result = CommandResult::passed(COMMAND, root_display);
    result.diagnostics = vec![
        plan_diagnostic("base", base),
        plan_diagnostic("changed_path_count", plan.changed_files.len().to_string()),
        plan_diagnostic("changed_files", plan.changed_files.join(",")),
        plan_diagnostic("changed_modules", plan.changed_modules.join(",")),
        plan_diagnostic(
            "package_generated_artifacts",
            plan.package_generated_artifacts.join(","),
        ),
        plan_diagnostic("impact_class", plan.impact_class.as_str()),
        plan_diagnostic("required_commands", plan.required_commands.join(";")),
        plan_diagnostic("selected_commands", plan.required_commands.join(";")),
        plan_diagnostic(
            "optional_local_acceleration_commands",
            plan.optional_local_acceleration_commands.join(";"),
        ),
        plan_diagnostic("escalation_reasons", plan.escalation_reasons.join(";")),
        CommandDiagnostic::info(DiagnosticKind::PackagePolicy, "gate_plan_trust_boundary")
            .with_field("trust_boundary_note")
            .with_actual_value(plan.trust_boundary_note.clone()),
    ];
    result
}

fn plan_diagnostic(field: &'static str, actual_value: impl Into<String>) -> CommandDiagnostic {
    CommandDiagnostic::info(DiagnosticKind::PackagePolicy, format!("gate_plan_{field}"))
        .with_field(field)
        .with_actual_value(actual_value)
}
