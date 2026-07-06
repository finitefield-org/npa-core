//! Shared package root loading and package command entry points.

use std::fs;
use std::path::{Path, PathBuf};

use npa_package::{parse_and_validate_manifest_str, PackagePath, ValidatedPackageManifest};

use crate::args::PackageCommand;
use crate::diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind};
use crate::fs::{artifact_io_error, join_package_path, render_package_path, render_package_root};
use crate::package_artifacts::run_package_check_generated;
use crate::package_axiom_report::run_package_axiom_report;
use crate::package_build::run_package_build_certs;
use crate::package_check::run_package_check;
use crate::package_export_summary::run_package_export_summary;
use crate::package_gate_plan::run_package_gate_plan;
use crate::package_hashes::run_package_check_hashes;
use crate::package_high_trust::run_package_high_trust;
use crate::package_index::run_package_index;
use crate::package_publish::run_package_publish_plan;
use crate::package_verify::run_package_verify_certs;

/// Package-relative manifest path used by CLR-04 package commands.
pub const PACKAGE_MANIFEST_PATH: &str = "npa-package.toml";

/// Loaded and validated package root data.
#[derive(Clone, Debug)]
pub struct LoadedPackageRoot {
    /// Root path used for filesystem reads.
    pub root: PathBuf,
    /// Sanitized root display string for diagnostics.
    pub root_display: String,
    /// Package-relative manifest path.
    pub manifest_path: PackagePath,
    /// Manifest source bytes decoded as UTF-8.
    pub manifest_source: String,
    /// Validated package manifest and graph.
    pub validated: ValidatedPackageManifest,
}

/// Load and validate `npa-package.toml` from a package root.
pub fn load_package_root(
    root: impl AsRef<Path>,
    command: impl Into<String>,
) -> Result<LoadedPackageRoot, CommandResult> {
    let root = root.as_ref();
    let command = command.into();
    let root_display = render_package_root(root);
    let manifest_path = PackagePath::new(PACKAGE_MANIFEST_PATH);
    let full_manifest_path = match join_package_path(root, &manifest_path, "$.manifest") {
        Ok(path) => path,
        Err(diagnostic) => {
            return Err(CommandResult::failed(
                command,
                root_display,
                vec![*diagnostic],
            ));
        }
    };

    let manifest_source = match fs::read_to_string(&full_manifest_path) {
        Ok(source) => source,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let diagnostic =
                CommandDiagnostic::error(DiagnosticKind::PackageManifest, "manifest_missing")
                    .with_path(render_package_path(&manifest_path));
            return Err(CommandResult::failed(
                command,
                root_display,
                vec![diagnostic],
            ));
        }
        Err(_) => {
            let diagnostic =
                artifact_io_error("manifest_missing", render_package_path(&manifest_path));
            return Err(CommandResult::failed(
                command,
                root_display,
                vec![diagnostic],
            ));
        }
    };

    let validated = match parse_and_validate_manifest_str(&manifest_source) {
        Ok(validated) => validated,
        Err(error) => {
            let diagnostic = CommandDiagnostic::from_package_manifest_error(&error);
            return Err(CommandResult::failed(
                command,
                root_display,
                vec![diagnostic],
            ));
        }
    };

    Ok(LoadedPackageRoot {
        root: root.to_path_buf(),
        root_display,
        manifest_path,
        manifest_source,
        validated,
    })
}

/// Run a package command implemented so far in CLR-04.
pub fn run_package_command(command: PackageCommand) -> CommandResult {
    match command {
        PackageCommand::Check(options) => run_package_check(options),
        PackageCommand::BuildCerts(options) => run_package_build_certs(options),
        PackageCommand::AxiomReport(options) => run_package_axiom_report(options),
        PackageCommand::Index(options) => run_package_index(options),
        PackageCommand::ExportSummary(options) => run_package_export_summary(options),
        PackageCommand::VerifyCerts(options) => run_package_verify_certs(options),
        PackageCommand::CheckHashes(options) => run_package_check_hashes(options),
        PackageCommand::PublishPlan(options) => run_package_publish_plan(options),
        PackageCommand::CheckGenerated(options) => run_package_check_generated(options),
        PackageCommand::HighTrust(options) => run_package_high_trust(*options),
        PackageCommand::GatePlan(options) => run_package_gate_plan(options),
    }
}
