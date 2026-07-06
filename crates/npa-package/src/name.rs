//! Package name type adapters.

use crate::error::{PackageManifestError, PackageManifestResult};

/// Canonical dotted name type shared with certificate artifacts.
pub type CanonicalPackageName = npa_cert::Name;

/// Package identity for `npa.package.v0.1` manifests.
///
/// Validation fixes the grammar to lowercase ASCII package ids beginning with a
/// letter and continuing with letters, digits, or hyphens.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageId(pub String);

impl PackageId {
    /// Build a package id wrapper from a package id string.
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    /// Return the package id string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Validate the `npa.package.v0.1` package id grammar.
pub fn validate_package_id(id: &PackageId, path: impl Into<String>) -> PackageManifestResult<()> {
    let value = id.as_str();
    let valid = !value.is_empty()
        && value.len() <= 64
        && value
            .bytes()
            .next()
            .is_some_and(|byte| byte.is_ascii_lowercase())
        && value
            .bytes()
            .skip(1)
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-');

    if valid {
        Ok(())
    } else {
        Err(PackageManifestError::invalid_package_id(path, value))
    }
}

/// Validate a canonical dotted module name.
pub fn validate_canonical_module_name(
    name: &CanonicalPackageName,
    path: impl Into<String>,
) -> PackageManifestResult<()> {
    validate_canonical_name(name, path, PackageManifestError::invalid_module_name)
}

/// Validate a canonical dotted declaration summary name.
pub fn validate_canonical_declaration_name(
    name: &CanonicalPackageName,
    path: impl Into<String>,
) -> PackageManifestResult<()> {
    validate_canonical_name(name, path, PackageManifestError::invalid_declaration_name)
}

/// Validate a canonical dotted axiom name.
pub fn validate_canonical_axiom_name(
    name: &CanonicalPackageName,
    path: impl Into<String>,
) -> PackageManifestResult<()> {
    validate_canonical_name(name, path, PackageManifestError::invalid_axiom_name)
}

fn validate_canonical_name(
    name: &CanonicalPackageName,
    path: impl Into<String>,
    error: impl FnOnce(String, String) -> PackageManifestError,
) -> PackageManifestResult<()> {
    if name.is_canonical() {
        Ok(())
    } else {
        Err(error(path.into(), name.as_dotted()))
    }
}
