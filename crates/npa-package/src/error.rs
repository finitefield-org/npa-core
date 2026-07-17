//! Structured package manifest error types.

/// Result type for package manifest parsing and validation.
pub type PackageManifestResult<T> = Result<T, PackageManifestError>;

/// Result type for package lock parsing and validation.
pub type PackageLockResult<T> = Result<T, PackageLockError>;

/// Result type for generated package artifact parsing and validation.
pub type PackageArtifactResult<T> = Result<T, PackageArtifactError>;

/// Stable package manifest error payload.
///
/// Tests should assert these structured fields instead of matching display text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageManifestError {
    /// Stable error category.
    pub kind: PackageManifestErrorKind,
    /// Stable manifest path, for example `$`, `policy.allowed_axioms`, or `modules[0].module`.
    pub path: String,
    /// Field name when the error is attached to one object field.
    pub field: Option<String>,
    /// Stable machine-readable reason code.
    pub reason_code: PackageManifestErrorReason,
    /// Expected value or type when useful.
    pub expected_value: Option<String>,
    /// Actual value or type when useful.
    pub actual_value: Option<String>,
}

impl PackageManifestError {
    /// Build a TOML syntax error.
    pub fn invalid_toml(message: impl Into<String>) -> Self {
        Self {
            kind: PackageManifestErrorKind::TomlSyntax,
            path: "$".to_owned(),
            field: None,
            reason_code: PackageManifestErrorReason::InvalidToml,
            expected_value: None,
            actual_value: Some(message.into()),
        }
    }

    /// Build a duplicate-field error reported by the TOML parser.
    pub fn duplicate_field(message: impl Into<String>) -> Self {
        Self {
            kind: PackageManifestErrorKind::Schema,
            path: "$".to_owned(),
            field: None,
            reason_code: PackageManifestErrorReason::DuplicateField,
            expected_value: None,
            actual_value: Some(message.into()),
        }
    }

    /// Build an unknown-field error.
    pub fn unknown_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self {
            kind: PackageManifestErrorKind::Schema,
            path: path.into(),
            field: Some(field.into()),
            reason_code: PackageManifestErrorReason::UnknownField,
            expected_value: None,
            actual_value: None,
        }
    }

    /// Build a missing-field error.
    pub fn missing_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self {
            kind: PackageManifestErrorKind::Schema,
            path: path.into(),
            field: Some(field.into()),
            reason_code: PackageManifestErrorReason::MissingField,
            expected_value: None,
            actual_value: None,
        }
    }

    /// Build a wrong-type error.
    pub fn wrong_type(
        path: impl Into<String>,
        field: Option<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self {
            kind: PackageManifestErrorKind::Schema,
            path: path.into(),
            field,
            reason_code: PackageManifestErrorReason::WrongType,
            expected_value: Some(expected.into()),
            actual_value: Some(actual.into()),
        }
    }

    /// Build an invalid-hash-format error.
    pub fn invalid_hash_format(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Hash,
            path,
            None,
            PackageManifestErrorReason::InvalidHashFormat,
            Some("sha256:<64 lowercase hex>".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an unsupported-schema error.
    pub fn unsupported_schema(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageManifestErrorKind::UnsupportedVersion,
            path,
            Some(field.into()),
            PackageManifestErrorReason::UnsupportedSchema,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-package-id error.
    pub fn invalid_package_id(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            None,
            PackageManifestErrorReason::InvalidPackageId,
            Some("lowercase ASCII package id".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-version error.
    pub fn invalid_version(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            None,
            PackageManifestErrorReason::InvalidVersion,
            Some("MAJOR.MINOR.PATCH without leading zeroes".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-profile error.
    pub fn invalid_profile(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            Some(field.into()),
            PackageManifestErrorReason::InvalidProfile,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-module-name error.
    pub fn invalid_module_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            None,
            PackageManifestErrorReason::InvalidModuleName,
            Some("canonical dotted name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-declaration-name error.
    pub fn invalid_declaration_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            None,
            PackageManifestErrorReason::InvalidDeclarationName,
            Some("canonical dotted name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-axiom-name error.
    pub fn invalid_axiom_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Domain,
            path,
            None,
            PackageManifestErrorReason::InvalidAxiomName,
            Some("canonical dotted name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-path error.
    pub fn invalid_path(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Path,
            path,
            None,
            PackageManifestErrorReason::InvalidPath,
            Some("lexical package-relative path".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a duplicate-module error.
    pub fn duplicate_module(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "module",
            PackageManifestErrorReason::DuplicateModule,
            actual,
        )
    }

    /// Build a duplicate-external-import error.
    pub fn duplicate_external_import(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "module",
            PackageManifestErrorReason::DuplicateExternalImport,
            actual,
        )
    }

    /// Build a duplicate-declaration summary error.
    pub fn duplicate_declaration(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "declaration",
            PackageManifestErrorReason::DuplicateDeclaration,
            actual,
        )
    }

    /// Build a duplicate-axiom error.
    pub fn duplicate_axiom(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "axiom",
            PackageManifestErrorReason::DuplicateAxiom,
            actual,
        )
    }

    /// Build a duplicate-artifact-path error.
    pub fn duplicate_artifact_path(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "artifact_path",
            PackageManifestErrorReason::DuplicateArtifactPath,
            actual,
        )
    }

    /// Build a local/external module collision error.
    pub fn local_external_module_collision(
        path: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::duplicate(
            path,
            "module",
            PackageManifestErrorReason::LocalExternalModuleCollision,
            actual,
        )
    }

    /// Build an unknown module import error.
    pub fn unknown_import(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Graph,
            path,
            Some("imports".to_owned()),
            PackageManifestErrorReason::UnknownImport,
            Some("local module or hash-pinned top-level external import".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a local module import cycle error.
    pub fn import_cycle(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageManifestErrorKind::Graph,
            path,
            Some("imports".to_owned()),
            PackageManifestErrorReason::ImportCycle,
            Some("acyclic local module graph".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a package axiom policy error.
    pub fn disallowed_axiom(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageManifestErrorKind::Policy,
            path,
            Some(field.into()),
            PackageManifestErrorReason::DisallowedAxiom,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    fn duplicate(
        path: impl Into<String>,
        field: impl Into<String>,
        reason_code: PackageManifestErrorReason,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageManifestErrorKind::Duplicate,
            path,
            Some(field.into()),
            reason_code,
            Some("unique value".to_owned()),
            Some(actual.into()),
        )
    }

    fn new(
        kind: PackageManifestErrorKind,
        path: impl Into<String>,
        field: Option<String>,
        reason_code: PackageManifestErrorReason,
        expected_value: Option<String>,
        actual_value: Option<String>,
    ) -> Self {
        Self {
            kind,
            path: path.into(),
            field,
            reason_code,
            expected_value,
            actual_value,
        }
    }
}

impl std::fmt::Display for PackageManifestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} at {}: {}",
            self.kind,
            self.path,
            self.reason_code.as_str()
        )
    }
}

impl std::error::Error for PackageManifestError {}

/// Stable package manifest error category.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageManifestErrorKind {
    /// TOML syntax or parser failure before schema validation.
    TomlSyntax,
    /// Closed-object schema, required field, or type validation failure.
    Schema,
    /// Unsupported schema version.
    UnsupportedVersion,
    /// Scalar domain validation failure.
    Domain,
    /// Duplicate package identity failure.
    Duplicate,
    /// Package-relative path validation failure.
    Path,
    /// Hash grammar validation failure.
    Hash,
    /// Import graph validation failure.
    Graph,
    /// Axiom policy validation failure.
    Policy,
}

/// Stable package manifest error reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageManifestErrorReason {
    /// TOML syntax is invalid.
    InvalidToml,
    /// A duplicate field was rejected.
    DuplicateField,
    /// A field is not part of the closed schema.
    UnknownField,
    /// A required field is absent.
    MissingField,
    /// A field has the wrong TOML type.
    WrongType,
    /// The schema field has the wrong value.
    WrongSchema,
    /// The schema version is unsupported.
    UnsupportedSchema,
    /// Package id grammar is invalid.
    InvalidPackageId,
    /// Package version grammar is invalid.
    InvalidVersion,
    /// Profile string is invalid.
    InvalidProfile,
    /// Module name grammar is invalid.
    InvalidModuleName,
    /// Declaration name grammar is invalid.
    InvalidDeclarationName,
    /// Axiom name grammar is invalid.
    InvalidAxiomName,
    /// Hash string grammar is invalid.
    InvalidHashFormat,
    /// Package path grammar is invalid.
    InvalidPath,
    /// Module name is duplicated.
    DuplicateModule,
    /// External import module is duplicated.
    DuplicateExternalImport,
    /// Declaration summary name is duplicated.
    DuplicateDeclaration,
    /// Axiom summary name is duplicated.
    DuplicateAxiom,
    /// Artifact path is duplicated.
    DuplicateArtifactPath,
    /// Local module and external import names collide.
    LocalExternalModuleCollision,
    /// Module import cannot be resolved.
    UnknownImport,
    /// Local module import graph has a cycle.
    ImportCycle,
    /// A module axiom is disallowed by package policy.
    DisallowedAxiom,
}

impl PackageManifestErrorReason {
    /// Return the stable wire reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidToml => "invalid_toml",
            Self::DuplicateField => "duplicate_field",
            Self::UnknownField => "unknown_field",
            Self::MissingField => "missing_field",
            Self::WrongType => "wrong_type",
            Self::WrongSchema => "wrong_schema",
            Self::UnsupportedSchema => "unsupported_schema",
            Self::InvalidPackageId => "invalid_package_id",
            Self::InvalidVersion => "invalid_version",
            Self::InvalidProfile => "invalid_profile",
            Self::InvalidModuleName => "invalid_module_name",
            Self::InvalidDeclarationName => "invalid_declaration_name",
            Self::InvalidAxiomName => "invalid_axiom_name",
            Self::InvalidHashFormat => "invalid_hash_format",
            Self::InvalidPath => "invalid_path",
            Self::DuplicateModule => "duplicate_module",
            Self::DuplicateExternalImport => "duplicate_external_import",
            Self::DuplicateDeclaration => "duplicate_declaration",
            Self::DuplicateAxiom => "duplicate_axiom",
            Self::DuplicateArtifactPath => "duplicate_artifact_path",
            Self::LocalExternalModuleCollision => "local_external_module_collision",
            Self::UnknownImport => "unknown_import",
            Self::ImportCycle => "import_cycle",
            Self::DisallowedAxiom => "disallowed_axiom",
        }
    }
}

/// Stable package lock error payload.
///
/// Package locks are generated JSON artifacts, separate from package manifests.
/// Tests should assert these structured fields instead of matching display text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockError {
    /// Stable error category.
    pub kind: PackageLockErrorKind,
    /// Stable artifact-local path, for example `$`, `manifest.file_hash`, or `entries[0].module`.
    pub path: String,
    /// Module context for entry-local package lock errors.
    pub module: Option<Box<String>>,
    /// Field name when the error is attached to one object field.
    pub field: Option<String>,
    /// Stable machine-readable reason code.
    pub reason_code: PackageLockErrorReason,
    /// Expected value or type when useful.
    pub expected_value: Option<String>,
    /// Actual value or type when useful.
    pub actual_value: Option<String>,
}

impl PackageLockError {
    /// Build a JSON syntax error.
    pub fn invalid_json(message: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            "$",
            None,
            PackageLockErrorReason::InvalidJson,
            Some("valid JSON object".to_owned()),
            Some(message.into()),
        )
    }

    /// Build a duplicate JSON object field error.
    pub fn duplicate_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::DuplicateField,
            Some("unique object field".to_owned()),
            None,
        )
    }

    /// Build an unknown-field error.
    pub fn unknown_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::UnknownField,
            None,
            None,
        )
    }

    /// Build a missing-field error.
    pub fn missing_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::MissingField,
            None,
            None,
        )
    }

    /// Build a wrong-type error.
    pub fn wrong_type(
        path: impl Into<String>,
        field: Option<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            field,
            PackageLockErrorReason::WrongType,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an unsupported lock schema error.
    pub fn unsupported_schema(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::LockSchemaInvalid,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-hash-format error.
    pub fn invalid_hash_format(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Hash,
            path,
            None,
            PackageLockErrorReason::InvalidHashFormat,
            Some("sha256:<64 lowercase hex>".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-package-id error.
    pub fn invalid_package_id(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Domain,
            path,
            None,
            PackageLockErrorReason::InvalidPackageId,
            Some("lowercase ASCII package id".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-version error.
    pub fn invalid_version(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Domain,
            path,
            None,
            PackageLockErrorReason::InvalidVersion,
            Some("MAJOR.MINOR.PATCH without leading zeroes".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-module-name error.
    pub fn invalid_module_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Domain,
            path,
            None,
            PackageLockErrorReason::InvalidModuleName,
            Some("canonical dotted name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-path error.
    pub fn invalid_path(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Path,
            path,
            None,
            PackageLockErrorReason::InvalidPath,
            Some("lexical package-relative path".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-origin error.
    pub fn invalid_origin(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some("origin".to_owned()),
            PackageLockErrorReason::InvalidOrigin,
            Some("local or external".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a duplicate-lock-entry error.
    pub fn duplicate_lock_entry(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "module",
            PackageLockErrorReason::DuplicateLockEntry,
            actual,
        )
    }

    /// Build a duplicate-certificate-path error.
    pub fn duplicate_certificate_path(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "certificate",
            PackageLockErrorReason::DuplicateCertificatePath,
            actual,
        )
    }

    /// Build a duplicate-import error within one lock entry.
    pub fn duplicate_import(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::duplicate(
            path,
            "module",
            PackageLockErrorReason::DuplicateImport,
            actual,
        )
    }

    /// Build an external-entry missing package or version error.
    pub fn external_field_required(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::ExternalFieldRequired,
            Some("present for origin = external".to_owned()),
            None,
        )
    }

    /// Build a local-entry forbidden package or version error.
    pub fn local_field_forbidden(
        path: impl Into<String>,
        field: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::LockSchema,
            path,
            Some(field.into()),
            PackageLockErrorReason::LocalFieldForbidden,
            Some("absent for origin = local".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a missing certificate artifact error.
    pub fn certificate_missing(path: impl Into<String>, expected: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::ArtifactIo,
            path,
            Some("certificate".to_owned()),
            PackageLockErrorReason::CertificateMissing,
            Some(expected.into()),
            None,
        )
    }

    /// Build an artifact read error.
    pub fn artifact_read_failed(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::ArtifactIo,
            path,
            Some(field.into()),
            PackageLockErrorReason::ArtifactReadFailed,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a certificate decode error.
    pub fn certificate_decode_failed(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateDecode,
            path,
            Some("certificate".to_owned()),
            PackageLockErrorReason::CertificateDecodeFailed,
            Some("decodable npa module certificate".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a certificate module identity mismatch error.
    pub fn certificate_module_mismatch(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::CertificateModuleMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a certificate file hash mismatch error.
    pub fn certificate_file_hash_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some(field.into()),
            PackageLockErrorReason::CertificateFileHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an export hash mismatch error.
    pub fn export_hash_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some(field.into()),
            PackageLockErrorReason::ExportHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an axiom report hash mismatch error.
    pub fn axiom_report_hash_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some(field.into()),
            PackageLockErrorReason::AxiomReportHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a certificate hash mismatch error.
    pub fn certificate_hash_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some(field.into()),
            PackageLockErrorReason::CertificateHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a missing high-trust import certificate hash error.
    pub fn import_certificate_hash_missing(path: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::CertificateIdentity,
            path,
            Some("certificate_hash".to_owned()),
            PackageLockErrorReason::ImportCertificateHashMissing,
            Some("present high-trust import certificate hash".to_owned()),
            None,
        )
    }

    /// Build a package-lock entry missing from the resolved lock graph.
    pub fn lock_entry_missing(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::LockEntryMissing,
            Some("package lock entry".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a package-lock entry origin mismatch error.
    pub fn lock_entry_origin_mismatch(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("origin".to_owned()),
            PackageLockErrorReason::LockEntryOriginMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an error for a manifest identity absent from the package lock.
    pub(crate) fn lock_entry_identity_missing(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some(field.into()),
            PackageLockErrorReason::LockEntryMissing,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a certificate import that is absent from the package manifest graph.
    pub fn manifest_import_missing(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::ManifestImportMissing,
            Some("manifest-resolved direct import".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a package manifest import that is absent from the certificate imports.
    pub fn certificate_import_missing(
        path: impl Into<String>,
        expected: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::CertificateImportMissing,
            Some(expected.into()),
            None,
        )
    }

    /// Build a certificate import that does not resolve to any package-lock entry.
    pub fn lock_import_missing(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::LockImportMissing,
            Some("local or external package-lock entry".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a lock import export-hash mismatch error.
    pub fn lock_import_export_hash_mismatch(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("export_hash".to_owned()),
            PackageLockErrorReason::LockImportExportHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a lock import certificate-hash mismatch error.
    pub fn lock_import_certificate_hash_mismatch(
        path: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("certificate_hash".to_owned()),
            PackageLockErrorReason::LockImportCertificateHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an external lock entry depending on a local entry error.
    pub fn external_import_depends_on_local(
        path: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("module".to_owned()),
            PackageLockErrorReason::ExternalImportDependsOnLocal,
            Some("external package-lock entry".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a package-lock import graph cycle error.
    pub fn lock_import_cycle(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageLockErrorKind::Graph,
            path,
            Some("imports".to_owned()),
            PackageLockErrorReason::LockImportCycle,
            Some("acyclic package-lock import graph".to_owned()),
            Some(actual.into()),
        )
    }

    fn duplicate(
        path: impl Into<String>,
        field: impl Into<String>,
        reason_code: PackageLockErrorReason,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageLockErrorKind::Duplicate,
            path,
            Some(field.into()),
            reason_code,
            Some("unique value".to_owned()),
            Some(actual.into()),
        )
    }

    fn new(
        kind: PackageLockErrorKind,
        path: impl Into<String>,
        field: Option<String>,
        reason_code: PackageLockErrorReason,
        expected_value: Option<String>,
        actual_value: Option<String>,
    ) -> Self {
        Self {
            kind,
            path: path.into(),
            module: None,
            field,
            reason_code,
            expected_value,
            actual_value,
        }
    }

    /// Attach module context while preserving the stable artifact-local path.
    pub fn with_module(mut self, module: impl Into<String>) -> Self {
        self.module = Some(Box::new(module.into()));
        self
    }

    fn display_path(&self) -> String {
        let Some(module) = &self.module else {
            return self.path.clone();
        };
        match self.path.find('.') {
            Some(split) => format!(
                "{} ({}){}",
                &self.path[..split],
                module,
                &self.path[split..]
            ),
            None => format!("{} ({})", self.path, module),
        }
    }
}

impl std::fmt::Display for PackageLockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} at {}: {}",
            self.kind,
            self.display_path(),
            self.reason_code.as_str()
        )
    }
}

impl std::error::Error for PackageLockError {}

/// Stable package lock error category.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageLockErrorKind {
    /// JSON syntax, closed-object schema, required field, or type validation failure.
    LockSchema,
    /// Scalar domain validation failure.
    Domain,
    /// Duplicate package lock identity failure.
    Duplicate,
    /// Package-relative path validation failure.
    Path,
    /// Hash grammar validation failure.
    Hash,
    /// Required package artifact bytes could not be read.
    ArtifactIo,
    /// Certificate bytes could not be decoded syntactically.
    CertificateDecode,
    /// Decoded certificate identity does not match the validated package manifest.
    CertificateIdentity,
    /// Package-lock import graph validation failure.
    Graph,
}

/// Stable package lock error reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageLockErrorReason {
    /// JSON syntax is invalid.
    InvalidJson,
    /// A duplicate object field was rejected.
    DuplicateField,
    /// A field is not part of the closed schema.
    UnknownField,
    /// A required field is absent.
    MissingField,
    /// A field has the wrong JSON type.
    WrongType,
    /// The lock schema field has the wrong value.
    LockSchemaInvalid,
    /// Hash string grammar is invalid.
    InvalidHashFormat,
    /// Package id grammar is invalid.
    InvalidPackageId,
    /// Package version grammar is invalid.
    InvalidVersion,
    /// Module name grammar is invalid.
    InvalidModuleName,
    /// Package path grammar is invalid.
    InvalidPath,
    /// Entry origin is neither local nor external.
    InvalidOrigin,
    /// Lock entry module is duplicated.
    DuplicateLockEntry,
    /// Lock entry certificate path is duplicated.
    DuplicateCertificatePath,
    /// Direct import module is duplicated within one lock entry.
    DuplicateImport,
    /// External entries must carry package and version.
    ExternalFieldRequired,
    /// Local entries must not carry package or version.
    LocalFieldForbidden,
    /// A required certificate artifact is absent.
    CertificateMissing,
    /// A package artifact could not be read.
    ArtifactReadFailed,
    /// Certificate bytes do not decode as an NPA module certificate.
    CertificateDecodeFailed,
    /// Certificate module name differs from the package manifest identity.
    CertificateModuleMismatch,
    /// Certificate file SHA-256 differs from the package manifest identity.
    CertificateFileHashMismatch,
    /// Certificate export hash differs from the package manifest identity.
    ExportHashMismatch,
    /// Certificate axiom report hash differs from the package manifest identity.
    AxiomReportHashMismatch,
    /// Certificate canonical hash differs from the package manifest identity.
    CertificateHashMismatch,
    /// A direct import lacks the high-trust certificate hash required by package locks.
    ImportCertificateHashMissing,
    /// A package-lock entry matching a manifest module or external import identity is missing.
    LockEntryMissing,
    /// A package-lock entry has the wrong local/external origin.
    LockEntryOriginMismatch,
    /// A certificate declares a direct import not present in the manifest graph.
    ManifestImportMissing,
    /// The manifest graph declares a direct import not present in the certificate.
    CertificateImportMissing,
    /// A certificate import cannot be resolved to a package-lock entry.
    LockImportMissing,
    /// A certificate import export hash differs from the resolved lock entry.
    LockImportExportHashMismatch,
    /// A certificate import certificate hash differs from the resolved lock entry.
    LockImportCertificateHashMismatch,
    /// An external certificate import resolves to a local package lock entry.
    ExternalImportDependsOnLocal,
    /// The package-lock import graph has a cycle.
    LockImportCycle,
}

impl PackageLockErrorReason {
    /// Return the stable wire reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidJson => "invalid_json",
            Self::DuplicateField => "duplicate_field",
            Self::UnknownField => "unknown_field",
            Self::MissingField => "missing_field",
            Self::WrongType => "wrong_type",
            Self::LockSchemaInvalid => "lock_schema_invalid",
            Self::InvalidHashFormat => "invalid_hash_format",
            Self::InvalidPackageId => "invalid_package_id",
            Self::InvalidVersion => "invalid_version",
            Self::InvalidModuleName => "invalid_module_name",
            Self::InvalidPath => "invalid_path",
            Self::InvalidOrigin => "invalid_origin",
            Self::DuplicateLockEntry => "duplicate_lock_entry",
            Self::DuplicateCertificatePath => "duplicate_certificate_path",
            Self::DuplicateImport => "duplicate_import",
            Self::ExternalFieldRequired => "external_field_required",
            Self::LocalFieldForbidden => "local_field_forbidden",
            Self::CertificateMissing => "certificate_missing",
            Self::ArtifactReadFailed => "artifact_read_failed",
            Self::CertificateDecodeFailed => "certificate_decode_failed",
            Self::CertificateModuleMismatch => "certificate_module_mismatch",
            Self::CertificateFileHashMismatch => "certificate_file_hash_mismatch",
            Self::ExportHashMismatch => "export_hash_mismatch",
            Self::AxiomReportHashMismatch => "axiom_report_hash_mismatch",
            Self::CertificateHashMismatch => "certificate_hash_mismatch",
            Self::ImportCertificateHashMissing => "import_certificate_hash_missing",
            Self::LockEntryMissing => "lock_entry_missing",
            Self::LockEntryOriginMismatch => "lock_entry_origin_mismatch",
            Self::ManifestImportMissing => "manifest_import_missing",
            Self::CertificateImportMissing => "certificate_import_missing",
            Self::LockImportMissing => "lock_import_missing",
            Self::LockImportExportHashMismatch => "lock_import_export_hash_mismatch",
            Self::LockImportCertificateHashMismatch => "lock_import_certificate_hash_mismatch",
            Self::ExternalImportDependsOnLocal => "external_import_depends_on_local",
            Self::LockImportCycle => "lock_import_cycle",
        }
    }
}

/// Stable generated package artifact error payload.
///
/// Package axiom reports and theorem indexes are generated metadata, separate
/// from package manifests, package locks, and proof evidence. Tests should
/// assert these structured fields instead of matching display text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageArtifactError {
    /// Stable error category.
    pub kind: PackageArtifactErrorKind,
    /// Stable artifact-local path, for example `$`, `modules[0].module`, or
    /// `entries[0].global_ref.name`.
    pub path: String,
    /// Field name when the error is attached to one object field.
    pub field: Option<String>,
    /// Stable machine-readable reason code.
    pub reason_code: PackageArtifactErrorReason,
    /// Expected value or type when useful.
    pub expected_value: Option<String>,
    /// Actual value or type when useful.
    pub actual_value: Option<String>,
}

impl PackageArtifactError {
    /// Build a JSON syntax error.
    pub fn invalid_json(message: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            "$",
            None,
            PackageArtifactErrorReason::InvalidJson,
            Some("valid JSON object".to_owned()),
            Some(message.into()),
        )
    }

    /// Build a duplicate JSON object field error.
    pub fn duplicate_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::DuplicateField,
            Some("unique object field".to_owned()),
            None,
        )
    }

    /// Build an unknown-field error.
    pub fn unknown_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::UnknownField,
            None,
            None,
        )
    }

    /// Build a missing-field error.
    pub fn missing_field(path: impl Into<String>, field: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::MissingField,
            None,
            None,
        )
    }

    /// Build a wrong-type error.
    pub fn wrong_type(
        path: impl Into<String>,
        field: Option<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            field,
            PackageArtifactErrorReason::WrongType,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an unsupported artifact schema error.
    pub fn unsupported_schema(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::UnsupportedSchema,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-hash-format error.
    pub fn invalid_hash_format(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Hash,
            path,
            None,
            PackageArtifactErrorReason::InvalidHashFormat,
            Some("sha256:<64 lowercase hex>".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-package-id error.
    pub fn invalid_package_id(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            None,
            PackageArtifactErrorReason::InvalidPackageId,
            Some("lowercase ASCII package id".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-version error.
    pub fn invalid_version(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            None,
            PackageArtifactErrorReason::InvalidVersion,
            Some("MAJOR.MINOR.PATCH without leading zeroes".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-module-name error.
    pub fn invalid_module_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            None,
            PackageArtifactErrorReason::InvalidModuleName,
            Some("canonical dotted module name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-declaration-name error.
    pub fn invalid_declaration_name(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            None,
            PackageArtifactErrorReason::InvalidDeclarationName,
            Some("canonical dotted declaration name".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid-path error.
    pub fn invalid_path(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::Path,
            path,
            None,
            PackageArtifactErrorReason::InvalidPath,
            Some("lexical package-relative path".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build an invalid enum value error.
    pub fn invalid_enum_value(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::InvalidEnumValue,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a duplicate identity error.
    pub fn duplicate(
        path: impl Into<String>,
        field: impl Into<String>,
        reason_code: PackageArtifactErrorReason,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::Duplicate,
            path,
            Some(field.into()),
            reason_code,
            Some("unique value".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a non-canonical generated artifact error.
    pub fn non_canonical(path: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::new(
            PackageArtifactErrorKind::CanonicalJson,
            path,
            None,
            PackageArtifactErrorReason::NonCanonicalOrder,
            Some("schema-defined canonical JSON bytes".to_owned()),
            Some(actual.into()),
        )
    }

    /// Build a stale self-hash error.
    pub fn self_hash_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::SelfHash,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::SelfHashMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a deterministic summary mismatch error.
    pub fn summary_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::Summary,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::SummaryMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a theorem-premise projection failure.
    pub fn theorem_premise_projection(
        reason_code: PackageArtifactErrorReason,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::Projection,
            "theorem_premise_report",
            None,
            reason_code,
            None,
            Some(actual.into()),
        )
    }

    /// Build a downstream import bundle mismatch error.
    pub fn downstream_import_bundle_mismatch(
        path: impl Into<String>,
        field: impl Into<String>,
        expected: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::Domain,
            path,
            Some(field.into()),
            PackageArtifactErrorReason::DownstreamImportBundleMismatch,
            Some(expected.into()),
            Some(actual.into()),
        )
    }

    /// Build a release-artifact self-reference error.
    pub fn release_artifact_self_reference(
        path: impl Into<String>,
        actual: impl Into<String>,
    ) -> Self {
        Self::new(
            PackageArtifactErrorKind::ArtifactSchema,
            path,
            Some("artifacts".to_owned()),
            PackageArtifactErrorReason::ReleaseArtifactSelfReference,
            Some("artifact list without generated/publish-plan.json".to_owned()),
            Some(actual.into()),
        )
    }

    fn new(
        kind: PackageArtifactErrorKind,
        path: impl Into<String>,
        field: Option<String>,
        reason_code: PackageArtifactErrorReason,
        expected_value: Option<String>,
        actual_value: Option<String>,
    ) -> Self {
        Self {
            kind,
            path: path.into(),
            field,
            reason_code,
            expected_value,
            actual_value,
        }
    }
}

impl std::fmt::Display for PackageArtifactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} at {}: {}",
            self.kind,
            self.path,
            self.reason_code.as_str()
        )
    }
}

impl std::error::Error for PackageArtifactError {}

/// Stable generated package artifact error category.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageArtifactErrorKind {
    /// JSON syntax, closed-object schema, required field, or type validation failure.
    ArtifactSchema,
    /// Scalar domain validation failure.
    Domain,
    /// Duplicate generated artifact identity failure.
    Duplicate,
    /// Package-relative path validation failure.
    Path,
    /// Hash grammar validation failure.
    Hash,
    /// Generated JSON bytes do not match canonical schema order.
    CanonicalJson,
    /// Generated artifact self-hash does not match canonical bytes excluding the self-hash field.
    SelfHash,
    /// Deterministic summary counts do not match artifact contents.
    Summary,
    /// Verified certificate data could not be projected into an audit artifact.
    Projection,
}

/// Stable generated package artifact error reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageArtifactErrorReason {
    /// JSON syntax is invalid.
    InvalidJson,
    /// A duplicate object field was rejected.
    DuplicateField,
    /// A field is not part of the closed schema.
    UnknownField,
    /// A required field is absent.
    MissingField,
    /// A field has the wrong JSON type.
    WrongType,
    /// The schema field has the wrong value.
    UnsupportedSchema,
    /// Hash string grammar is invalid.
    InvalidHashFormat,
    /// Package id grammar is invalid.
    InvalidPackageId,
    /// Package version grammar is invalid.
    InvalidVersion,
    /// Module name grammar is invalid.
    InvalidModuleName,
    /// Declaration name grammar is invalid.
    InvalidDeclarationName,
    /// Package path grammar is invalid.
    InvalidPath,
    /// An enum-like string field has an unsupported value.
    InvalidEnumValue,
    /// Module entry is duplicated.
    DuplicateModule,
    /// Axiom reference is duplicated.
    DuplicateAxiom,
    /// Checker summary is duplicated.
    DuplicateCheckerSummary,
    /// Theorem index entry is duplicated.
    DuplicateTheoremEntry,
    /// Theorem index mode is duplicated.
    DuplicateMode,
    /// Theorem index tag is duplicated.
    DuplicateTag,
    /// Statement constant reference is duplicated.
    DuplicateConstant,
    /// Policy violation entry is duplicated.
    DuplicateViolation,
    /// Release artifact entry is duplicated.
    DuplicateArtifact,
    /// Publish-plan artifact list references the publish plan itself.
    ReleaseArtifactSelfReference,
    /// Generated JSON object or array order is not canonical.
    NonCanonicalOrder,
    /// Self hash field differs from canonical bytes excluding that field.
    SelfHashMismatch,
    /// Summary count differs from deterministic contents.
    SummaryMismatch,
    /// Downstream import bundle does not match local registry seed entries.
    DownstreamImportBundleMismatch,
    /// The theorem-premise telescope limit was exhausted.
    TheoremPremiseTelescopeLimit,
    /// The theorem-premise weak-head-reduction fuel was exhausted.
    TheoremPremiseWhnfFuelLimit,
    /// The theorem-premise conversion fuel was exhausted.
    TheoremPremiseConversionFuelLimit,
    /// The theorem-premise expression traversal limit was exhausted.
    TheoremPremiseExpressionTraversalLimit,
    /// The theorem-premise dependency limit was exhausted.
    TheoremPremiseDependencyLimit,
    /// Verified theorem data contradicted report projection requirements.
    TheoremPremiseProjectionFailed,
}

impl PackageArtifactErrorReason {
    /// Return the stable wire reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidJson => "invalid_json",
            Self::DuplicateField => "duplicate_field",
            Self::UnknownField => "unknown_field",
            Self::MissingField => "missing_field",
            Self::WrongType => "wrong_type",
            Self::UnsupportedSchema => "unsupported_schema",
            Self::InvalidHashFormat => "invalid_hash_format",
            Self::InvalidPackageId => "invalid_package_id",
            Self::InvalidVersion => "invalid_version",
            Self::InvalidModuleName => "invalid_module_name",
            Self::InvalidDeclarationName => "invalid_declaration_name",
            Self::InvalidPath => "invalid_path",
            Self::InvalidEnumValue => "invalid_enum_value",
            Self::DuplicateModule => "duplicate_module",
            Self::DuplicateAxiom => "duplicate_axiom",
            Self::DuplicateCheckerSummary => "duplicate_checker_summary",
            Self::DuplicateTheoremEntry => "duplicate_theorem_entry",
            Self::DuplicateMode => "duplicate_mode",
            Self::DuplicateTag => "duplicate_tag",
            Self::DuplicateConstant => "duplicate_constant",
            Self::DuplicateViolation => "duplicate_violation",
            Self::DuplicateArtifact => "duplicate_artifact",
            Self::ReleaseArtifactSelfReference => "release_artifact_self_reference",
            Self::NonCanonicalOrder => "non_canonical_order",
            Self::SelfHashMismatch => "self_hash_mismatch",
            Self::SummaryMismatch => "summary_mismatch",
            Self::DownstreamImportBundleMismatch => "downstream_import_bundle_mismatch",
            Self::TheoremPremiseTelescopeLimit => "theorem_premise_telescope_limit",
            Self::TheoremPremiseWhnfFuelLimit => "theorem_premise_whnf_fuel_limit",
            Self::TheoremPremiseConversionFuelLimit => "theorem_premise_conversion_fuel_limit",
            Self::TheoremPremiseExpressionTraversalLimit => {
                "theorem_premise_expression_traversal_limit"
            }
            Self::TheoremPremiseDependencyLimit => "theorem_premise_dependency_limit",
            Self::TheoremPremiseProjectionFailed => "theorem_premise_projection_failed",
        }
    }
}
