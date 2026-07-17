//! Filesystem helpers owned by the CLI orchestration layer.

use std::{
    ffi::{OsStr, OsString},
    path::{Component, Path, PathBuf},
};

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

/// Validate an explicit package output path against its selected package root.
pub(crate) fn validate_package_output_path(
    root: &Path,
    package_path: &PackagePath,
    field: &str,
) -> Result<(), Box<CommandDiagnostic>> {
    validate_package_path(package_path, field)
        .map_err(|error| Box::new(CommandDiagnostic::from_package_manifest_error(&error)))?;

    let current_dir = if root.is_relative() {
        Some(
            std::env::current_dir()
                .map_err(|_| Box::new(package_output_root_resolution_diagnostic()))?,
        )
    } else {
        None
    };
    let marker = package_root_marker(root, current_dir.as_deref())
        .map_err(|_| Box::new(package_output_root_resolution_diagnostic()))?;
    let Some(marker) = marker else {
        return Ok(());
    };

    if package_output_path_repeats_root(package_path, &marker) {
        return Err(Box::new(
            CommandDiagnostic::error(DiagnosticKind::Usage, "package_output_path_repeats_root")
                .with_path(render_package_path(package_path))
                .with_field(field)
                .with_expected_value("path relative to --root without the package-root directory")
                .with_actual_value("root-qualified path"),
        ));
    }

    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PackageRootMarkerError {
    CurrentDirectoryRequired,
}

fn package_root_marker(
    root: &Path,
    current_dir: Option<&Path>,
) -> Result<Option<OsString>, PackageRootMarkerError> {
    let resolved = if root.is_relative() {
        let current_dir = current_dir.ok_or(PackageRootMarkerError::CurrentDirectoryRequired)?;
        current_dir.join(root)
    } else {
        root.to_path_buf()
    };
    let mut normal_components = Vec::new();
    for component in resolved.components() {
        match component {
            Component::Prefix(_) | Component::RootDir => normal_components.clear(),
            Component::CurDir => {}
            Component::ParentDir => {
                normal_components.pop();
            }
            Component::Normal(component) => normal_components.push(component.to_os_string()),
        }
    }
    Ok(normal_components.pop())
}

fn package_output_path_repeats_root(package_path: &PackagePath, marker: &OsStr) -> bool {
    Path::new(package_path.as_str())
        .components()
        .any(|component| matches!(component, Component::Normal(value) if value == marker))
}

fn package_output_root_resolution_diagnostic() -> CommandDiagnostic {
    CommandDiagnostic::error(
        DiagnosticKind::ArtifactIo,
        "package_output_root_resolution_failed",
    )
    .with_field("--root")
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn package_root_marker_resolves_absolute_relative_and_current_directory_roots() {
        let current_dir = std::env::temp_dir()
            .join("npa-cli-package-output-path-tests")
            .join("workspace")
            .join("proofs");
        let absolute = current_dir.join("nested").join("package");

        assert_eq!(
            package_root_marker(&absolute, None).unwrap(),
            Some(OsString::from("package"))
        );
        assert_eq!(
            package_root_marker(Path::new("nested/proofs"), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("."), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("temporary/.."), Some(&current_dir)).unwrap(),
            Some(OsString::from("proofs"))
        );
        assert_eq!(
            package_root_marker(Path::new("proofs"), None),
            Err(PackageRootMarkerError::CurrentDirectoryRequired)
        );
    }

    #[test]
    fn package_root_marker_returns_none_for_a_filesystem_root() {
        let root = std::env::temp_dir();
        let filesystem_root = root.ancestors().last().unwrap();

        assert_eq!(package_root_marker(filesystem_root, None).unwrap(), None);
    }

    #[test]
    fn package_output_path_classification_uses_exact_components() {
        let cases = [
            ("generated/candidate.metadata.json", "proofs", false),
            ("target/candidates/candidate.metadata.json", "proofs", false),
            ("proofs/generated/candidate.metadata.json", "proofs", true),
            (
                "npa-project-example/proofs/generated/candidate.metadata.json",
                "proofs",
                true,
            ),
            (
                "workspace/run/proofs/generated/candidate.metadata.json",
                "proofs",
                true,
            ),
            ("generated/proofs.json", "proofs", false),
            ("generated/proofs-data/candidate.json", "proofs", false),
            ("generated/candidate.json", "generated", true),
            ("target/candidates/candidate.json", "target", true),
        ];

        for (path, marker, expected) in cases {
            assert_eq!(
                package_output_path_repeats_root(&PackagePath::new(path), OsStr::new(marker)),
                expected,
                "{path} with marker {marker}"
            );
        }
    }

    #[test]
    fn package_output_path_validation_preserves_lexical_failures() {
        let root = std::env::temp_dir().join("proofs");
        for path in [
            "",
            "/absolute.json",
            ".",
            "..",
            "generated//output.json",
            "generated/../output.json",
            "https://example.invalid/output.json",
            "generated\\output.json",
        ] {
            let diagnostic =
                validate_package_output_path(&root, &PackagePath::new(path), "--out").unwrap_err();
            assert_eq!(diagnostic.kind, DiagnosticKind::PackageManifest, "{path}");
            assert_eq!(diagnostic.reason_code, "invalid_path", "{path}");
            assert_eq!(diagnostic.path.as_deref(), Some("--out"), "{path}");
            assert_eq!(diagnostic.actual_value.as_deref(), Some(path), "{path}");
        }
    }

    #[test]
    fn package_output_path_validation_returns_the_stable_repeated_root_diagnostic() {
        let root = std::env::temp_dir().join("proofs");
        let path = PackagePath::new("workspace/proofs/generated/output.json");

        let diagnostic = validate_package_output_path(&root, &path, "--out").unwrap_err();

        assert_eq!(diagnostic.kind, DiagnosticKind::Usage);
        assert_eq!(diagnostic.reason_code, "package_output_path_repeats_root");
        assert_eq!(diagnostic.path.as_deref(), Some(path.as_str()));
        assert_eq!(diagnostic.field.as_deref(), Some("--out"));
        assert_eq!(
            diagnostic.expected_value.as_deref(),
            Some("path relative to --root without the package-root directory")
        );
        assert_eq!(
            diagnostic.actual_value.as_deref(),
            Some("root-qualified path")
        );
    }

    #[test]
    fn package_output_root_resolution_diagnostic_is_sanitized() {
        let diagnostic = package_output_root_resolution_diagnostic();

        assert_eq!(diagnostic.kind, DiagnosticKind::ArtifactIo);
        assert_eq!(
            diagnostic.reason_code,
            "package_output_root_resolution_failed"
        );
        assert_eq!(diagnostic.field.as_deref(), Some("--root"));
        assert_eq!(diagnostic.path, None);
        assert_eq!(diagnostic.expected_value, None);
        assert_eq!(diagnostic.actual_value, None);
    }
}
