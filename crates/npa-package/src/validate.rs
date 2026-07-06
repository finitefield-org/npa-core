//! Package manifest validation entry points.

use std::collections::{BTreeMap, BTreeSet};

use npa_cert::Name;

use crate::{
    error::{PackageManifestError, PackageManifestResult},
    graph::{resolve_package_graph, PackageGraph},
    manifest::{
        parse_manifest_str, PackageExternalImport, PackageManifest, PackageModule, PackagePolicy,
        PackageVersion,
    },
    name::{
        validate_canonical_axiom_name, validate_canonical_declaration_name,
        validate_canonical_module_name, validate_package_id,
    },
    path::{validate_package_path, PackagePath},
    schema::{
        CERTIFICATE_FORMAT_CANONICAL_V0_1, CHECKER_PROFILE_REFERENCE_V0_1, CORE_SPEC_V0_1,
        KERNEL_PROFILE_V0_1, PACKAGE_MANIFEST_SCHEMA,
    },
};

/// Options for manifest validation.
///
/// The current CLR-01 scalar validator has no tunable behavior, but this type
/// reserves a stable API surface for later path-root or policy flags.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackageManifestValidationOptions {
    _private: (),
}

/// Deterministic package manifest validation report.
///
/// CLR-01 currently stops at the first error, so the report contains either no
/// errors or one structured error. The vector shape is kept stable for callers
/// that want report-style handling without depending on human display strings.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackageManifestValidationReport {
    errors: Vec<PackageManifestError>,
}

impl PackageManifestValidationReport {
    /// Return whether validation completed without errors.
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    /// Return structured validation errors in deterministic pass order.
    pub fn errors(&self) -> &[PackageManifestError] {
        &self.errors
    }

    /// Return the first structured validation error, if any.
    pub fn first_error(&self) -> Option<&PackageManifestError> {
        self.errors.first()
    }

    /// Consume the report and return its structured validation errors.
    pub fn into_errors(self) -> Vec<PackageManifestError> {
        self.errors
    }

    fn valid() -> Self {
        Self { errors: Vec::new() }
    }

    fn from_error(error: PackageManifestError) -> Self {
        Self {
            errors: vec![error],
        }
    }
}

/// A package manifest that has passed validation implemented so far.
///
/// CLR-01 grows this value in phases. At CLR-01-08 it means closed-object
/// parsing, scalar domain checks, duplicate checks, import resolution, local
/// graph validation, and package axiom-policy validation have succeeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedPackageManifest {
    manifest: PackageManifest,
    graph: PackageGraph,
}

impl ValidatedPackageManifest {
    /// Return the validated manifest metadata.
    pub fn manifest(&self) -> &PackageManifest {
        &self.manifest
    }

    /// Return resolved import graph metadata.
    pub fn graph(&self) -> &PackageGraph {
        &self.graph
    }

    /// Consume the wrapper and return the manifest metadata.
    pub fn into_manifest(self) -> PackageManifest {
        self.manifest
    }

    /// Consume the wrapper and return manifest metadata plus graph metadata.
    pub fn into_parts(self) -> (PackageManifest, PackageGraph) {
        (self.manifest, self.graph)
    }
}

/// Parse and validate a package manifest string.
pub fn parse_and_validate_manifest_str(
    source: &str,
) -> PackageManifestResult<ValidatedPackageManifest> {
    validate_manifest(parse_manifest_str(source)?)
}

/// Parse and validate a package manifest string, returning a report.
pub fn validate_manifest_source_report(source: &str) -> PackageManifestValidationReport {
    match parse_and_validate_manifest_str(source) {
        Ok(_) => PackageManifestValidationReport::valid(),
        Err(error) => PackageManifestValidationReport::from_error(error),
    }
}

/// Validate an already parsed package manifest with default options.
pub fn validate_manifest(
    manifest: PackageManifest,
) -> PackageManifestResult<ValidatedPackageManifest> {
    validate_manifest_with_options(manifest, &PackageManifestValidationOptions::default())
}

/// Validate an already parsed package manifest, returning a report.
pub fn validate_manifest_report(manifest: PackageManifest) -> PackageManifestValidationReport {
    match validate_manifest(manifest) {
        Ok(_) => PackageManifestValidationReport::valid(),
        Err(error) => PackageManifestValidationReport::from_error(error),
    }
}

/// Validate an already parsed package manifest.
pub fn validate_manifest_with_options(
    manifest: PackageManifest,
    _options: &PackageManifestValidationOptions,
) -> PackageManifestResult<ValidatedPackageManifest> {
    validate_fixed_schema_and_profiles(&manifest)?;
    validate_scalar_domains(&manifest)?;
    validate_duplicate_domains(&manifest)?;
    let graph = resolve_package_graph(&manifest)?;
    validate_axiom_policy(&manifest)?;
    Ok(ValidatedPackageManifest { manifest, graph })
}

/// Validate the `MAJOR.MINOR.PATCH` package version grammar.
pub fn validate_package_version(
    version: &PackageVersion,
    path: impl Into<String>,
) -> PackageManifestResult<()> {
    let value = version.as_str();
    if is_valid_package_version(value) {
        Ok(())
    } else {
        Err(PackageManifestError::invalid_version(path, value))
    }
}

fn validate_fixed_schema_and_profiles(manifest: &PackageManifest) -> PackageManifestResult<()> {
    if manifest.schema != PACKAGE_MANIFEST_SCHEMA {
        return Err(PackageManifestError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_MANIFEST_SCHEMA,
            manifest.schema.clone(),
        ));
    }
    validate_exact_profile(
        "core_spec",
        "core_spec",
        &manifest.core_spec,
        CORE_SPEC_V0_1,
    )?;
    validate_exact_profile(
        "kernel_profile",
        "kernel_profile",
        &manifest.kernel_profile,
        KERNEL_PROFILE_V0_1,
    )?;
    validate_exact_profile(
        "certificate_format",
        "certificate_format",
        &manifest.certificate_format,
        CERTIFICATE_FORMAT_CANONICAL_V0_1,
    )?;
    validate_exact_profile(
        "checker_profile",
        "checker_profile",
        &manifest.checker_profile,
        CHECKER_PROFILE_REFERENCE_V0_1,
    )
}

fn validate_exact_profile(
    path: &str,
    field: &str,
    actual: &str,
    expected: &str,
) -> PackageManifestResult<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(PackageManifestError::invalid_profile(
            path, field, expected, actual,
        ))
    }
}

fn validate_scalar_domains(manifest: &PackageManifest) -> PackageManifestResult<()> {
    validate_package_id(&manifest.package, "package")?;
    validate_package_version(&manifest.version, "version")?;

    for (index, axiom) in manifest.policy.allowed_axioms.iter().enumerate() {
        validate_canonical_axiom_name(axiom, format!("policy.allowed_axioms[{index}]"))?;
    }

    if let Some(imports) = &manifest.imports {
        for (index, import) in imports.iter().enumerate() {
            let path = format!("imports[{index}]");
            validate_canonical_module_name(&import.module, format!("{path}.module"))?;
            validate_package_id(&import.package, format!("{path}.package"))?;
            validate_package_version(&import.version, format!("{path}.version"))?;
            validate_package_path(&import.certificate, format!("{path}.certificate"))?;
        }
    }

    for (index, module) in manifest.modules.iter().enumerate() {
        validate_module_scalar_domains(index, module)?;
    }

    Ok(())
}

fn validate_module_scalar_domains(
    index: usize,
    module: &PackageModule,
) -> PackageManifestResult<()> {
    let path = format!("modules[{index}]");
    validate_canonical_module_name(&module.module, format!("{path}.module"))?;
    validate_package_path(&module.source, format!("{path}.source"))?;
    validate_package_path(&module.certificate, format!("{path}.certificate"))?;
    validate_name_list(&module.imports, &format!("{path}.imports"), |name, path| {
        validate_canonical_module_name(name, path)
    })?;
    if let Some(meta) = &module.meta {
        validate_package_path(meta, format!("{path}.meta"))?;
    }
    if let Some(replay) = &module.replay {
        validate_package_path(replay, format!("{path}.replay"))?;
    }
    if let Some(inductives) = &module.inductives {
        validate_name_list(inductives, &format!("{path}.inductives"), |name, path| {
            validate_canonical_declaration_name(name, path)
        })?;
    }
    if let Some(definitions) = &module.definitions {
        validate_name_list(definitions, &format!("{path}.definitions"), |name, path| {
            validate_canonical_declaration_name(name, path)
        })?;
    }
    if let Some(theorems) = &module.theorems {
        validate_name_list(theorems, &format!("{path}.theorems"), |name, path| {
            validate_canonical_declaration_name(name, path)
        })?;
    }
    if let Some(axioms) = &module.axioms {
        validate_name_list(axioms, &format!("{path}.axioms"), |name, path| {
            validate_canonical_axiom_name(name, path)
        })?;
    }
    Ok(())
}

fn validate_name_list(
    names: &[Name],
    path: &str,
    validate: impl Fn(&Name, String) -> PackageManifestResult<()>,
) -> PackageManifestResult<()> {
    for (index, name) in names.iter().enumerate() {
        validate(name, format!("{path}[{index}]"))?;
    }
    Ok(())
}

fn validate_duplicate_domains(manifest: &PackageManifest) -> PackageManifestResult<()> {
    validate_duplicate_module_names(&manifest.modules)?;
    if let Some(imports) = &manifest.imports {
        validate_duplicate_external_imports(imports)?;
        validate_local_external_module_collisions(&manifest.modules, imports)?;
    }
    validate_duplicate_allowed_axioms(&manifest.policy)?;

    for (index, module) in manifest.modules.iter().enumerate() {
        validate_duplicate_declarations(index, module)?;
        validate_duplicate_module_axioms(index, module)?;
    }

    validate_duplicate_module_artifact_paths(&manifest.modules)
}

fn validate_duplicate_module_names(modules: &[PackageModule]) -> PackageManifestResult<()> {
    let mut seen = BTreeMap::<Name, usize>::new();
    for (index, module) in modules.iter().enumerate() {
        if seen.insert(module.module.clone(), index).is_some() {
            return Err(PackageManifestError::duplicate_module(
                format!("modules[{index}].module"),
                module.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_duplicate_external_imports(
    imports: &[PackageExternalImport],
) -> PackageManifestResult<()> {
    let mut seen = BTreeMap::<Name, usize>::new();
    for (index, import) in imports.iter().enumerate() {
        if seen.insert(import.module.clone(), index).is_some() {
            return Err(PackageManifestError::duplicate_external_import(
                format!("imports[{index}].module"),
                import.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_local_external_module_collisions(
    modules: &[PackageModule],
    imports: &[PackageExternalImport],
) -> PackageManifestResult<()> {
    let external_modules = imports
        .iter()
        .map(|import| import.module.clone())
        .collect::<BTreeSet<_>>();
    for (index, module) in modules.iter().enumerate() {
        if external_modules.contains(&module.module) {
            return Err(PackageManifestError::local_external_module_collision(
                format!("modules[{index}].module"),
                module.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_duplicate_allowed_axioms(policy: &PackagePolicy) -> PackageManifestResult<()> {
    validate_duplicate_names(
        &policy.allowed_axioms,
        "policy.allowed_axioms",
        PackageManifestError::duplicate_axiom,
    )
}

fn validate_duplicate_declarations(
    module_index: usize,
    module: &PackageModule,
) -> PackageManifestResult<()> {
    let mut seen = BTreeMap::<Name, String>::new();
    for (field, names) in [
        ("inductives", module.inductives.as_deref()),
        ("definitions", module.definitions.as_deref()),
        ("theorems", module.theorems.as_deref()),
    ] {
        if let Some(names) = names {
            for (index, name) in names.iter().enumerate() {
                let path = format!("modules[{module_index}].{field}[{index}]");
                if seen.insert(name.clone(), path.clone()).is_some() {
                    return Err(PackageManifestError::duplicate_declaration(
                        path,
                        name.as_dotted(),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_duplicate_module_axioms(
    module_index: usize,
    module: &PackageModule,
) -> PackageManifestResult<()> {
    if let Some(axioms) = &module.axioms {
        validate_duplicate_names(
            axioms,
            &format!("modules[{module_index}].axioms"),
            PackageManifestError::duplicate_axiom,
        )?;
    }
    Ok(())
}

fn validate_duplicate_names(
    names: &[Name],
    path: &str,
    error: impl Fn(String, String) -> PackageManifestError,
) -> PackageManifestResult<()> {
    let mut seen = BTreeMap::<Name, usize>::new();
    for (index, name) in names.iter().enumerate() {
        if seen.insert(name.clone(), index).is_some() {
            return Err(error(format!("{path}[{index}]"), name.as_dotted()));
        }
    }
    Ok(())
}

fn validate_duplicate_module_artifact_paths(
    modules: &[PackageModule],
) -> PackageManifestResult<()> {
    let mut seen = BTreeMap::<PackagePath, String>::new();
    for (module_index, module) in modules.iter().enumerate() {
        for (path_field, artifact_path) in module_artifact_paths(module) {
            let path = format!("modules[{module_index}].{path_field}");
            if seen.insert(artifact_path.clone(), path.clone()).is_some() {
                return Err(PackageManifestError::duplicate_artifact_path(
                    path,
                    artifact_path.as_str(),
                ));
            }
        }
    }
    Ok(())
}

fn module_artifact_paths(module: &PackageModule) -> Vec<(&'static str, &PackagePath)> {
    let mut paths = vec![
        ("source", &module.source),
        ("certificate", &module.certificate),
    ];
    if let Some(meta) = &module.meta {
        paths.push(("meta", meta));
    }
    if let Some(replay) = &module.replay {
        paths.push(("replay", replay));
    }
    paths
}

fn validate_axiom_policy(manifest: &PackageManifest) -> PackageManifestResult<()> {
    for (index, axiom) in manifest.policy.allowed_axioms.iter().enumerate() {
        if is_sorry_axiom(axiom) {
            return Err(PackageManifestError::disallowed_axiom(
                format!("policy.allowed_axioms[{index}]"),
                "allowed_axioms",
                "non-sorry axiom",
                axiom.as_dotted(),
            ));
        }
    }

    let allowed_axioms = manifest
        .policy
        .allowed_axioms
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    for (module_index, module) in manifest.modules.iter().enumerate() {
        let Some(axioms) = &module.axioms else {
            continue;
        };
        for (axiom_index, axiom) in axioms.iter().enumerate() {
            let path = format!("modules[{module_index}].axioms[{axiom_index}]");
            if is_sorry_axiom(axiom) {
                return Err(PackageManifestError::disallowed_axiom(
                    path,
                    "axioms",
                    "non-sorry axiom",
                    axiom.as_dotted(),
                ));
            }
            if !manifest.policy.allow_custom_axioms && !allowed_axioms.contains(axiom) {
                return Err(PackageManifestError::disallowed_axiom(
                    path,
                    "axioms",
                    "allowed axiom or allow_custom_axioms = true",
                    axiom.as_dotted(),
                ));
            }
        }
    }

    Ok(())
}

fn is_sorry_axiom(axiom: &Name) -> bool {
    axiom.as_dotted().contains("sorry")
}

fn is_valid_package_version(value: &str) -> bool {
    let mut segment_count = 0;
    for segment in value.split('.') {
        segment_count += 1;
        if segment.is_empty()
            || !segment.bytes().all(|byte| byte.is_ascii_digit())
            || (segment.len() > 1 && segment.starts_with('0'))
        {
            return false;
        }
    }
    segment_count == 3
}
