//! Filesystem helpers owned by the CLI orchestration layer.

use std::path::{Path, PathBuf};

use npa_package::{validate_package_path, PackagePath};

use crate::diagnostic::{CommandDiagnostic, DiagnosticKind};

/// Render a package root without exposing host-local absolute paths.
pub fn render_package_root(root: &Path) -> String {
    if root.as_os_str().is_empty() {
        ".".to_owned()
    } else if root.is_absolute() {
        "<absolute-root>".to_owned()
    } else {
        normalize_path_separators(&root.to_string_lossy())
    }
}

/// Join a validated package-relative path to a package root.
pub fn join_package_path(
    root: &Path,
    package_path: &PackagePath,
    manifest_field_path: impl Into<String>,
) -> Result<PathBuf, Box<CommandDiagnostic>> {
    validate_package_path(package_path, manifest_field_path.into())
        .map_err(|error| Box::new(CommandDiagnostic::from_package_manifest_error(&error)))?;
    Ok(root.join(package_path.as_str()))
}

/// Return a deterministic package-relative path display string.
pub fn render_package_path(path: &PackagePath) -> String {
    path.as_str().to_owned()
}

fn normalize_path_separators(path: &str) -> String {
    path.replace('\\', "/")
}

/// Build a deterministic artifact IO diagnostic.
pub fn artifact_io_error(
    reason_code: impl Into<String>,
    package_path: impl Into<String>,
) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::ArtifactIo, reason_code).with_path(package_path)
}
