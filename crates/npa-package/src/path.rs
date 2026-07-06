//! Package-relative path validation helpers.

use crate::error::{PackageManifestError, PackageManifestResult};

/// Package-relative path string accepted by `npa.package.v0.1`.
///
/// Validation is lexical and package-relative. It does not require file
/// existence, resolve symlinks, fetch registries, or consult the network.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackagePath(pub String);

impl PackagePath {
    /// Build a package path wrapper from a path string.
    pub fn new(path: impl Into<String>) -> Self {
        Self(path.into())
    }

    /// Return the package-relative path string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Validate the lexical package-relative path grammar.
///
/// This does not touch the filesystem, require the path to exist, canonicalize
/// symlinks, or contact registries.
pub fn validate_package_path(
    path: &PackagePath,
    error_path: impl Into<String>,
) -> PackageManifestResult<()> {
    let value = path.as_str();
    let valid = !value.is_empty()
        && !value.starts_with('/')
        && !value.contains('\\')
        && !value.chars().any(char::is_control)
        && !has_uri_scheme(value)
        && value
            .split('/')
            .all(|component| !component.is_empty() && component != "." && component != "..");

    if valid {
        Ok(())
    } else {
        Err(PackageManifestError::invalid_path(error_path, value))
    }
}

fn has_uri_scheme(value: &str) -> bool {
    let Some(colon_index) = value.find(':') else {
        return false;
    };
    if value
        .find('/')
        .is_some_and(|slash_index| slash_index < colon_index)
    {
        return false;
    }

    let scheme = &value[..colon_index];
    let mut bytes = scheme.bytes();
    bytes.next().is_some_and(|byte| byte.is_ascii_alphabetic())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'-' | b'.'))
}
