//! Read-only adopted interface-proposal surface-drift checking.
//!
//! This module is deliberately a curation gate. Proposal metadata, Human
//! elaboration, source bytes, and the resulting comparison are never proof
//! evidence. Certificate artifacts are used only as the already-established
//! target surface authority and are verified in memory through the existing
//! source-free certificate API.

use std::{
    collections::{BTreeMap, BTreeSet},
    io::Read,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

use npa_cert::{AxiomPolicy, DeclPayload, ExportKind, GlobalRef, Name, VerifiedModule};
use npa_frontend::{
    compile_human_source_to_core_output_with_source_interfaces, FileId, HumanCompileOptions,
    HumanImportedSourceInterface, VerifiedImport,
};
use npa_kernel::{Decl, Reducibility};
use npa_package::{
    format_package_hash, package_file_hash, parse_and_validate_interface_proposal,
    parse_and_validate_manifest_str, parse_package_hash, InterfaceProposal,
    InterfaceProposalDeclarationKind, PackageHash, ValidatedPackageManifest,
};

use crate::args::PackageCheckInterfaceProposalSurfaceOptions;
use crate::diagnostic::{
    CommandDiagnostic, CommandResult, DiagnosticKind, InterfaceProposalSurfaceComparison,
    InterfaceProposalSurfaceDiagnostic, InterfaceProposalSurfaceOutput,
    InterfaceProposalSurfaceTarget,
};
use crate::fs::{
    no_follow_directory::{open_absolute_directory, Directory, DirectoryChild},
    render_package_root,
};
use crate::package_build::fallback_imported_source_interface;
use crate::package_interface_proposals::{
    build_surface_core_source, validate_interface_proposal_surface,
};

const COMMAND: &str = "package check-interface-proposal-surface";
const DEFAULT_PROPOSAL_ROOT: &str = "interface-proposals";
const PROPOSAL_ROOT_PREFIX: &str = "Mathlib";
const MAX_PROPOSAL_BYTES: usize = 262_144;
const MAX_MANIFEST_BYTES: usize = 262_144;
const MAX_SOURCE_BYTES: usize = 16_777_216;
const MAX_CERTIFICATE_BYTES: usize = npa_cert::MAX_CERTIFICATE_BYTES;
const MAX_DIRECT_IMPORTS: usize = 4_096;
const MAX_DECLARATIONS: usize = 262_144;
const MAX_FAMILY_MEMBERS: usize = 262_144;
const MAX_SUPPORT_CLOSURE: usize = 262_144;
const MAX_DIAGNOSTICS: usize = 1_024;
const MAX_DIAGNOSTIC_VALUE_BYTES: usize = 256;
const MAX_PATH_BYTES: usize = 1_024;
const MAX_IDENTIFIER_BYTES: usize = 1_024;
const MAX_CORE_TERM_BYTES: usize = npa_cert::MAX_CERTIFICATE_BYTES;

#[derive(Clone, Copy)]
struct ReadReasons {
    missing: &'static str,
    symlink: &'static str,
    escape: &'static str,
    not_regular: &'static str,
    bytes_exceeded: &'static str,
}

#[derive(Clone, Debug)]
struct ReadFailure {
    reason: &'static str,
}

#[derive(Clone, Debug)]
struct CertificateArtifact {
    bytes: Vec<u8>,
    decoded: npa_cert::ModuleCert,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FamilyRecord {
    name: String,
    kind: String,
    surface: String,
    parent: String,
    ty: Option<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DeclarationRecord {
    name: String,
    kind: String,
    surface: String,
    universe_params: Vec<String>,
    universe_constraints: Vec<String>,
    ty: Option<Vec<u8>>,
    body: Option<Vec<u8>>,
    reducibility_or_opacity: String,
    parent: Option<String>,
    dependencies: Vec<String>,
    family_members: Vec<FamilyRecord>,
}

#[derive(Clone, Debug)]
struct SurfaceState {
    target: InterfaceProposalSurfaceTarget,
    comparison: InterfaceProposalSurfaceComparison,
    diagnostics: Vec<InterfaceProposalSurfaceDiagnostic>,
}

/// Run the frozen v1 adopted interface-proposal surface comparison.
pub fn run_package_check_interface_proposal_surface(
    options: PackageCheckInterfaceProposalSurfaceOptions,
) -> CommandResult {
    let proposal_path_display = display_path(&options.proposal_path);
    let proposal_sha256 = bounded_value(&options.proposal_sha256);
    let mut state = SurfaceState {
        target: empty_target(),
        comparison: not_checked_comparison(),
        diagnostics: Vec::new(),
    };

    if !is_mathlib_module(&options.target_module) {
        push_diagnostic(
            &mut state,
            "input",
            "target_module_invalid",
            None::<String>,
            Some("target-module"),
            Some("canonical Mathlib.* module"),
            Some(options.target_module.as_dotted()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let proposal_root = options
        .proposal_root
        .clone()
        .unwrap_or_else(|| PathBuf::from(DEFAULT_PROPOSAL_ROOT));
    if !is_normal_relative_path(&proposal_root) {
        push_diagnostic(
            &mut state,
            "input",
            "proposal_path_escape",
            None::<String>,
            Some("proposal-root"),
            Some("package-relative path without . or .. components"),
            Some(display_path(&proposal_root)),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    if let Err(reason) = validate_proposal_path(&options.proposal_path) {
        push_diagnostic(
            &mut state,
            "input",
            reason,
            Some(proposal_path_display.clone()),
            Some("proposal-path"),
            Some("Mathlib/**/*.toml relative path"),
            Some(proposal_path_display.clone()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let proposal_hash = match parse_package_hash(&options.proposal_sha256, "proposal-sha256") {
        Ok(hash) => hash,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "input",
                "proposal_hash_invalid",
                Some(proposal_path_display.clone()),
                Some("proposal-sha256"),
                Some("sha256:<64 lowercase hexadecimal characters>"),
                Some(options.proposal_sha256.clone()),
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };

    let package_root = match open_absolute_directory(&options.common.root, false) {
        Ok(root) => root,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "input",
                "proposal_path_escape",
                None::<String>,
                Some("root"),
                Some("existing non-symlink package directory"),
                Some(render_package_root(&options.common.root)),
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };

    let proposal_relative = proposal_root.join(&options.proposal_path);
    let proposal_bytes = match read_confined_file(
        &package_root,
        &proposal_relative,
        MAX_PROPOSAL_BYTES,
        ReadReasons {
            missing: "proposal_missing",
            symlink: "proposal_path_symlink",
            escape: "proposal_path_escape",
            not_regular: "proposal_missing",
            bytes_exceeded: "proposal_bytes_exceeded",
        },
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            push_diagnostic(
                &mut state,
                "input",
                error.reason,
                Some(proposal_path_display.clone()),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let actual_proposal_hash = package_file_hash(&proposal_bytes);
    if actual_proposal_hash != proposal_hash {
        push_diagnostic(
            &mut state,
            "input",
            "proposal_hash_mismatch",
            Some(proposal_path_display.clone()),
            Some("proposal-sha256"),
            Some(format_package_hash(&proposal_hash)),
            Some(format_package_hash(&actual_proposal_hash)),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let proposal = match parse_and_validate_interface_proposal(&proposal_bytes) {
        Ok(proposal) => proposal,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "input",
                "proposal_parse_invalid",
                Some(proposal_path_display.clone()),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    if proposal.interface_status != npa_package::InterfaceProposalStatus::Adopted {
        push_diagnostic(
            &mut state,
            "input",
            "proposal_status_not_adopted",
            Some(proposal_path_display.clone()),
            Some("interface_status"),
            Some("adopted"),
            Some(proposal.interface_status.as_str()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    if proposal.proof_evidence {
        push_diagnostic(
            &mut state,
            "input",
            "proposal_proof_evidence_not_false",
            Some(proposal_path_display.clone()),
            Some("proof_evidence"),
            Some("false"),
            Some("true"),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    if proposal.module != options.target_module.as_dotted() {
        push_diagnostic(
            &mut state,
            "input",
            "proposal_module_mismatch",
            Some(proposal_path_display.clone()),
            Some("module"),
            Some(options.target_module.as_dotted()),
            Some(proposal.module.clone()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let manifest_bytes = match read_confined_file(
        &package_root,
        Path::new("npa-package.toml"),
        MAX_MANIFEST_BYTES,
        ReadReasons {
            missing: "manifest_missing",
            symlink: "manifest_invalid",
            escape: "manifest_invalid",
            not_regular: "manifest_invalid",
            bytes_exceeded: "manifest_bytes_exceeded",
        },
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            push_diagnostic(
                &mut state,
                "target",
                error.reason,
                Some("npa-package.toml"),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let manifest_source = match std::str::from_utf8(&manifest_bytes) {
        Ok(source) => source,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "target",
                "manifest_invalid",
                Some("npa-package.toml"),
                None::<String>,
                Some("valid UTF-8"),
                Some("invalid UTF-8"),
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let validated = match parse_and_validate_manifest_str(manifest_source) {
        Ok(validated) => validated,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "target",
                "manifest_invalid",
                Some("npa-package.toml"),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let manifest = validated.manifest();
    let target_indices = manifest
        .modules
        .iter()
        .enumerate()
        .filter_map(|(index, module)| (module.module == options.target_module).then_some(index))
        .collect::<Vec<_>>();
    let target_index = match target_indices.as_slice() {
        [] => {
            push_diagnostic(
                &mut state,
                "input",
                "target_module_missing",
                None::<String>,
                Some("target-module"),
                Some(options.target_module.as_dotted()),
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
        [_] => target_indices[0],
        _ => {
            push_diagnostic(
                &mut state,
                "input",
                "target_module_ambiguous",
                None::<String>,
                Some("target-module"),
                Some("exactly one manifest module"),
                Some(target_indices.len().to_string()),
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let target_module = &manifest.modules[target_index];
    state.target.module = Some(target_module.module.as_dotted());
    state.target.source = Some(target_module.source.as_str().to_owned());
    state.target.certificate = Some(target_module.certificate.as_str().to_owned());
    let target_source_path = state.target.source.clone();
    let target_certificate_path = state.target.certificate.clone();

    let source_bytes = match read_confined_file(
        &package_root,
        Path::new(target_module.source.as_str()),
        MAX_SOURCE_BYTES,
        ReadReasons {
            missing: "target_source_missing",
            symlink: "target_source_symlink",
            escape: "target_source_path_escape",
            not_regular: "target_source_not_regular",
            bytes_exceeded: "source_bytes_exceeded",
        },
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            push_diagnostic(
                &mut state,
                "target",
                error.reason,
                target_source_path.clone(),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    if std::str::from_utf8(&source_bytes).is_err() {
        push_diagnostic(
            &mut state,
            "target",
            "target_source_invalid_utf8",
            target_source_path.clone(),
            None::<String>,
            Some("valid UTF-8"),
            Some("invalid UTF-8"),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let source_hash = package_file_hash(&source_bytes);
    state.target.source_file_sha256 = Some(format_package_hash(&source_hash));
    if source_hash != target_module.expected_source_hash {
        push_diagnostic(
            &mut state,
            "target",
            "target_source_hash_mismatch",
            target_source_path.clone(),
            Some("expected_source_hash"),
            Some(format_package_hash(&target_module.expected_source_hash)),
            Some(format_package_hash(&source_hash)),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let target_certificate_bytes = match read_confined_file(
        &package_root,
        Path::new(target_module.certificate.as_str()),
        MAX_CERTIFICATE_BYTES,
        ReadReasons {
            missing: "target_certificate_missing",
            symlink: "target_certificate_symlink",
            escape: "target_certificate_path_escape",
            not_regular: "target_certificate_not_regular",
            bytes_exceeded: "certificate_bytes_exceeded",
        },
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            push_diagnostic(
                &mut state,
                "target",
                error.reason,
                target_certificate_path.clone(),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let target_certificate_file_hash = package_file_hash(&target_certificate_bytes);
    state.target.certificate_file_sha256 = Some(format_package_hash(&target_certificate_file_hash));
    if target_certificate_file_hash != target_module.expected_certificate_file_hash {
        push_diagnostic(
            &mut state,
            "target",
            "target_certificate_file_hash_mismatch",
            target_certificate_path.clone(),
            Some("expected_certificate_file_hash"),
            Some(format_package_hash(
                &target_module.expected_certificate_file_hash,
            )),
            Some(format_package_hash(&target_certificate_file_hash)),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let target_decoded = match npa_cert::decode_module_cert(&target_certificate_bytes) {
        Ok(certificate) => certificate,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "target",
                "target_certificate_decode_failed",
                target_certificate_path.clone(),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    if target_decoded.header().module != target_module.module
        || PackageHash::from(target_decoded.hashes().certificate_hash)
            != target_module.expected_certificate_hash
        || PackageHash::from(target_decoded.hashes().export_hash)
            != target_module.expected_export_hash
    {
        push_diagnostic(
            &mut state,
            "target",
            "target_certificate_identity_mismatch",
            target_certificate_path.clone(),
            Some("module/export/certificate_hash"),
            Some(target_module.module.as_dotted()),
            Some(target_decoded.header().module.as_dotted()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    state.target.certificate_sha256 = Some(format_package_hash(
        &target_module.expected_certificate_hash,
    ));
    state.target.export_sha256 = Some(format_package_hash(&target_module.expected_export_hash));
    if PackageHash::from(target_decoded.hashes().axiom_report_hash)
        != target_module.expected_axiom_report_hash
    {
        push_diagnostic(
            &mut state,
            "target",
            "target_manifest_hash_mismatch",
            target_certificate_path.clone(),
            Some("expected_axiom_report_hash"),
            Some(format_package_hash(
                &target_module.expected_axiom_report_hash,
            )),
            Some(format_package_hash(&PackageHash::from(
                target_decoded.hashes().axiom_report_hash,
            ))),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    if target_decoded.imports().len() > MAX_DIRECT_IMPORTS {
        push_diagnostic(
            &mut state,
            "resource",
            "direct_import_count_exceeded",
            target_certificate_path.clone(),
            Some("direct_imports"),
            Some(MAX_DIRECT_IMPORTS.to_string()),
            Some(target_decoded.imports().len().to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    if !certificate_import_names_equal(&target_decoded, &target_module.imports) {
        push_diagnostic(
            &mut state,
            "target",
            "target_manifest_hash_mismatch",
            target_certificate_path.clone(),
            Some("imports"),
            Some(render_name_list(&target_module.imports)),
            Some(render_certificate_import_names(&target_decoded)),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let mut artifacts = BTreeMap::<Name, CertificateArtifact>::new();
    artifacts.insert(
        target_module.module.clone(),
        CertificateArtifact {
            bytes: target_certificate_bytes,
            decoded: target_decoded,
        },
    );
    if let Err(reason) =
        load_certificate_closure(&package_root, &validated, target_index, &mut artifacts)
    {
        push_diagnostic(
            &mut state,
            reason.0,
            reason.1,
            reason.2,
            None::<String>,
            None::<String>,
            None::<String>,
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let policy = package_axiom_policy(&validated);
    let verified =
        match verify_certificate_closure(&target_module.module, &artifacts, &policy, &mut state) {
            Ok(verified) => verified,
            Err(()) => {
                return finish(
                    options,
                    proposal_path_display,
                    proposal_sha256,
                    state,
                    "invalid",
                );
            }
        };
    let target_verified = match verified.get(&target_module.module) {
        Some(verified) => verified,
        None => {
            push_diagnostic(
                &mut state,
                "target",
                "target_certificate_verification_failed",
                target_certificate_path.clone(),
                None::<String>,
                Some(target_module.module.as_dotted()),
                Some("missing verified target"),
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let target_core = match npa_cert::verified_module_to_kernel_decls(target_verified) {
        Ok(declarations) => declarations,
        Err(_) => {
            push_diagnostic(
                &mut state,
                "elaboration",
                "target_core_normalization_failed",
                target_certificate_path.clone(),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    if target_core.len() > MAX_DECLARATIONS {
        push_diagnostic(
            &mut state,
            "resource",
            "declaration_count_exceeded",
            target_certificate_path.clone(),
            Some("declarations"),
            Some(MAX_DECLARATIONS.to_string()),
            Some(target_core.len().to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let target_records = match target_declaration_records(target_verified, &target_core) {
        Ok(records) => records,
        Err(reason) => {
            push_diagnostic(
                &mut state,
                "elaboration",
                reason,
                target_certificate_path.clone(),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    let target_family_count = family_records(&target_records).len();
    if target_family_count > MAX_FAMILY_MEMBERS {
        push_diagnostic(
            &mut state,
            "resource",
            "family_member_count_exceeded",
            target_certificate_path.clone(),
            Some("family_members"),
            Some(MAX_FAMILY_MEMBERS.to_string()),
            Some(target_family_count.to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    let all_verified_imports = verified
        .values()
        .map(|module| VerifiedImport::from(module.as_ref()))
        .collect::<Vec<_>>();
    let imported_interfaces = verified
        .values()
        .map(|module| fallback_imported_source_interface(module.as_ref()))
        .collect::<Vec<HumanImportedSourceInterface>>();
    if let Err(error) =
        validate_interface_proposal_surface(&proposal, &all_verified_imports, &imported_interfaces)
    {
        let body_error = error.path.contains(".body");
        push_diagnostic(
            &mut state,
            "elaboration",
            if body_error {
                "proposal_definition_parse_failed"
            } else {
                "proposal_signature_parse_failed"
            },
            Some(error.path),
            error.field.as_deref(),
            error.expected,
            error.actual,
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let proposal_source = build_surface_core_source(&proposal);
    let proposal_core = match compile_human_source_to_core_output_with_source_interfaces(
        FileId(0),
        Name::from_dotted(&proposal.module),
        &proposal_source,
        &all_verified_imports,
        &imported_interfaces,
        &HumanCompileOptions::default(),
    ) {
        Ok(output) => output.core_module,
        Err(_) => {
            let body_error = proposal.declarations.iter().any(|declaration| {
                declaration.kind == InterfaceProposalDeclarationKind::Definition
            });
            push_diagnostic(
                &mut state,
                "elaboration",
                if body_error {
                    "proposal_definition_elaboration_failed"
                } else {
                    "proposal_signature_elaboration_failed"
                },
                Some("declarations"),
                None::<String>,
                None::<String>,
                None::<String>,
            );
            return finish(
                options,
                proposal_path_display,
                proposal_sha256,
                state,
                "invalid",
            );
        }
    };
    if proposal_core.declarations.len() > MAX_DECLARATIONS {
        push_diagnostic(
            &mut state,
            "resource",
            "declaration_count_exceeded",
            Some(proposal_path_display.clone()),
            Some("declarations"),
            Some(MAX_DECLARATIONS.to_string()),
            Some(proposal_core.declarations.len().to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let proposal_records =
        match proposal_declaration_records(&proposal, &proposal_core.declarations) {
            Ok(records) => records,
            Err(reason) => {
                push_diagnostic(
                    &mut state,
                    "elaboration",
                    reason,
                    Some(proposal_path_display.clone()),
                    None::<String>,
                    None::<String>,
                    None::<String>,
                );
                return finish(
                    options,
                    proposal_path_display,
                    proposal_sha256,
                    state,
                    "invalid",
                );
            }
        };
    let proposal_family_count = family_records(&proposal_records).len();
    if proposal_family_count > MAX_FAMILY_MEMBERS {
        push_diagnostic(
            &mut state,
            "resource",
            "family_member_count_exceeded",
            Some(proposal_path_display.clone()),
            Some("family_members"),
            Some(MAX_FAMILY_MEMBERS.to_string()),
            Some(proposal_family_count.to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }

    compare_surface(
        &proposal,
        &target_module.imports,
        &artifacts[&target_module.module].decoded,
        &proposal_records,
        &target_records,
        &mut state,
    );
    let support_count = support_closure(&proposal_records)
        .len()
        .saturating_add(support_closure(&target_records).len());
    if support_count > MAX_SUPPORT_CLOSURE {
        push_diagnostic(
            &mut state,
            "resource",
            "support_closure_count_exceeded",
            Some(proposal_path_display.clone()),
            Some("support_closure"),
            Some(MAX_SUPPORT_CLOSURE.to_string()),
            Some(support_count.to_string()),
        );
        return finish(
            options,
            proposal_path_display,
            proposal_sha256,
            state,
            "invalid",
        );
    }
    let status = if state.diagnostics.is_empty() {
        "parity"
    } else {
        "drift"
    };
    finish(
        options,
        proposal_path_display,
        proposal_sha256,
        state,
        status,
    )
}

fn finish(
    options: PackageCheckInterfaceProposalSurfaceOptions,
    proposal_path: String,
    proposal_sha256: String,
    mut state: SurfaceState,
    status: &str,
) -> CommandResult {
    sort_and_bound_diagnostics(&mut state.diagnostics);
    let output = InterfaceProposalSurfaceOutput {
        status: status.to_owned(),
        proposal_path,
        proposal_sha256,
        target: state.target,
        comparison: state.comparison,
        diagnostics: state.diagnostics.clone(),
    };
    let command_diagnostics = state
        .diagnostics
        .iter()
        .map(surface_command_diagnostic)
        .collect::<Vec<_>>();
    let result = if status == "parity" {
        CommandResult::passed(COMMAND, render_package_root(&options.common.root))
    } else {
        CommandResult::failed(
            COMMAND,
            render_package_root(&options.common.root),
            command_diagnostics,
        )
    };
    result.with_interface_proposal_surface(output)
}

fn empty_target() -> InterfaceProposalSurfaceTarget {
    InterfaceProposalSurfaceTarget {
        module: None,
        source: None,
        source_file_sha256: None,
        certificate: None,
        certificate_file_sha256: None,
        certificate_sha256: None,
        export_sha256: None,
    }
}

fn not_checked_comparison() -> InterfaceProposalSurfaceComparison {
    InterfaceProposalSurfaceComparison {
        module_name: "not_checked".to_owned(),
        direct_imports: "not_checked".to_owned(),
        declaration_order: "not_checked".to_owned(),
        declaration_names: "not_checked".to_owned(),
        declaration_kinds: "not_checked".to_owned(),
        declaration_surfaces: "not_checked".to_owned(),
        signatures: "not_checked".to_owned(),
        definition_bodies: "not_checked".to_owned(),
        inductive_family_members: "not_checked".to_owned(),
        exported_support_closure: "not_checked".to_owned(),
    }
}

fn push_diagnostic(
    state: &mut SurfaceState,
    category: &str,
    reason: &str,
    path: Option<impl Into<String>>,
    field: Option<impl Into<String>>,
    expected: Option<impl Into<String>>,
    actual: Option<impl Into<String>>,
) {
    state.diagnostics.push(InterfaceProposalSurfaceDiagnostic {
        category: bounded_value(category),
        reason: bounded_value(reason),
        path: path.map(|value| bounded_path(&value.into())),
        field: field.map(|value| bounded_value(&value.into())),
        expected: expected.map(|value| bounded_value(&value.into())),
        actual: actual.map(|value| bounded_value(&value.into())),
    });
}

fn surface_command_diagnostic(
    diagnostic: &InterfaceProposalSurfaceDiagnostic,
) -> CommandDiagnostic {
    let mut result =
        CommandDiagnostic::error(DiagnosticKind::InterfaceProposal, &diagnostic.reason);
    if let Some(path) = &diagnostic.path {
        result = result.with_path(path.clone());
    }
    if let Some(field) = &diagnostic.field {
        result = result.with_field(field.clone());
    }
    if let Some(expected) = &diagnostic.expected {
        result = result.with_expected_value(expected.clone());
    }
    if let Some(actual) = &diagnostic.actual {
        result = result.with_actual_value(actual.clone());
    }
    result
}

fn sort_and_bound_diagnostics(diagnostics: &mut Vec<InterfaceProposalSurfaceDiagnostic>) {
    diagnostics.sort_by(|left, right| {
        left.category
            .cmp(&right.category)
            .then_with(|| left.reason.cmp(&right.reason))
            .then_with(|| option_order(&left.path, &right.path))
            .then_with(|| option_order(&left.field, &right.field))
            .then_with(|| option_order(&left.expected, &right.expected))
            .then_with(|| option_order(&left.actual, &right.actual))
    });
    if diagnostics.len() > MAX_DIAGNOSTICS {
        let actual = diagnostics.len().to_string();
        diagnostics.truncate(MAX_DIAGNOSTICS.saturating_sub(1));
        diagnostics.push(InterfaceProposalSurfaceDiagnostic {
            category: "resource".to_owned(),
            reason: "diagnostic_count_exceeded".to_owned(),
            path: Some("<diagnostics>".to_owned()),
            field: None,
            expected: Some(MAX_DIAGNOSTICS.to_string()),
            actual: Some(actual),
        });
    }
}

fn option_order(left: &Option<String>, right: &Option<String>) -> std::cmp::Ordering {
    left.is_some()
        .cmp(&right.is_some())
        .then_with(|| left.as_deref().cmp(&right.as_deref()))
}

fn bounded_value(value: &str) -> String {
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        return value.to_owned();
    }
    let mut end = MAX_DIAGNOSTIC_VALUE_BYTES;
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    value[..end].to_owned()
}

fn bounded_path(value: &str) -> String {
    if value.starts_with('/') || value.contains(':') && value.as_bytes().get(1) == Some(&b':') {
        return "<absolute-path>".to_owned();
    }
    bounded_value(value)
}

fn display_path(path: &Path) -> String {
    let value = path.to_string_lossy().replace('\\', "/");
    bounded_path(&value)
}

fn is_mathlib_module(module: &Name) -> bool {
    module.is_canonical()
        && module.as_dotted().len() <= MAX_IDENTIFIER_BYTES
        && module.0.first().map(String::as_str) == Some("Mathlib")
        && module.0.len() >= 2
}

fn is_normal_relative_path(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && path.is_relative()
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
        && path.to_str().is_some_and(|value| !value.contains('\\'))
}

fn validate_proposal_path(path: &Path) -> Result<(), &'static str> {
    if !is_normal_relative_path(path) {
        return Err(if path.is_absolute() {
            "proposal_path_escape"
        } else {
            "invalid_proposal_path"
        });
    }
    let components = path.components().collect::<Vec<_>>();
    if components
        .first()
        .and_then(|component| component.as_os_str().to_str())
        != Some(PROPOSAL_ROOT_PREFIX)
        || path.extension().and_then(|extension| extension.to_str()) != Some("toml")
        || path.to_string_lossy().len() > MAX_PATH_BYTES
    {
        return Err("invalid_proposal_path");
    }
    Ok(())
}

fn read_confined_file(
    root: &Directory,
    relative: &Path,
    limit: usize,
    reasons: ReadReasons,
) -> Result<Vec<u8>, ReadFailure> {
    if !is_normal_relative_path(relative) {
        return Err(ReadFailure {
            reason: reasons.escape,
        });
    }
    let components = relative.components().collect::<Vec<_>>();
    let mut directory = root.try_clone().map_err(|_| ReadFailure {
        reason: reasons.missing,
    })?;
    for (index, component) in components.iter().enumerate() {
        let Component::Normal(component) = component else {
            return Err(ReadFailure {
                reason: reasons.escape,
            });
        };
        let child = directory
            .open_child(component)
            .map_err(|error| ReadFailure {
                reason: if error.raw_os_error() == Some(libc::ELOOP) {
                    reasons.symlink
                } else {
                    reasons.missing
                },
            })?;
        if index + 1 < components.len() {
            match child {
                DirectoryChild::Directory(child) => directory = child,
                DirectoryChild::Regular(_) => {
                    return Err(ReadFailure {
                        reason: reasons.escape,
                    });
                }
            }
        } else {
            let DirectoryChild::Regular(mut file) = child else {
                return Err(ReadFailure {
                    reason: reasons.not_regular,
                });
            };
            let metadata = file.metadata().map_err(|_| ReadFailure {
                reason: reasons.missing,
            })?;
            if metadata.len() > limit as u64 {
                return Err(ReadFailure {
                    reason: reasons.bytes_exceeded,
                });
            }
            let mut bytes = Vec::new();
            std::io::Read::by_ref(&mut file)
                .take(limit as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(|_| ReadFailure {
                    reason: reasons.missing,
                })?;
            if bytes.len() > limit {
                return Err(ReadFailure {
                    reason: reasons.bytes_exceeded,
                });
            }
            return Ok(bytes);
        }
    }
    Err(ReadFailure {
        reason: reasons.escape,
    })
}

fn package_axiom_policy(validated: &ValidatedPackageManifest) -> AxiomPolicy {
    let mut policy = AxiomPolicy::normal();
    if !validated.manifest().policy.allow_custom_axioms {
        policy.allowlisted_axioms = validated
            .manifest()
            .policy
            .allowed_axioms
            .iter()
            .cloned()
            .collect();
    }
    policy
}

fn load_certificate_closure(
    root: &Directory,
    validated: &ValidatedPackageManifest,
    target_index: usize,
    artifacts: &mut BTreeMap<Name, CertificateArtifact>,
) -> Result<(), (&'static str, &'static str, Option<String>)> {
    let manifest = validated.manifest();
    let local_by_name = manifest
        .modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let external_by_name = manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
        .map(|(index, import)| (import.module.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut pending = vec![manifest.modules[target_index].module.clone()];
    let mut queued = BTreeSet::new();
    while let Some(module_name) = pending.pop() {
        if !queued.insert(module_name.clone()) {
            continue;
        }
        if let Some(&index) = local_by_name.get(&module_name) {
            let module = &manifest.modules[index];
            if index != target_index {
                let bytes = read_confined_file(
                    root,
                    Path::new(module.certificate.as_str()),
                    MAX_CERTIFICATE_BYTES,
                    ReadReasons {
                        missing: "import_certificate_missing",
                        symlink: "import_certificate_missing",
                        escape: "import_certificate_missing",
                        not_regular: "import_certificate_missing",
                        bytes_exceeded: "certificate_bytes_exceeded",
                    },
                )
                .map_err(|error| {
                    (
                        "target",
                        error.reason,
                        Some(module.certificate.as_str().to_owned()),
                    )
                })?;
                let file_hash = package_file_hash(&bytes);
                if file_hash != module.expected_certificate_file_hash {
                    return Err((
                        "target",
                        "import_certificate_file_hash_mismatch",
                        Some(module.certificate.as_str().to_owned()),
                    ));
                }
                let decoded = npa_cert::decode_module_cert(&bytes).map_err(|_| {
                    (
                        "target",
                        "import_certificate_identity_mismatch",
                        Some(module.certificate.as_str().to_owned()),
                    )
                })?;
                if decoded.header().module != module.module
                    || PackageHash::from(decoded.hashes().export_hash)
                        != module.expected_export_hash
                    || PackageHash::from(decoded.hashes().certificate_hash)
                        != module.expected_certificate_hash
                    || PackageHash::from(decoded.hashes().axiom_report_hash)
                        != module.expected_axiom_report_hash
                {
                    return Err((
                        "target",
                        "import_certificate_identity_mismatch",
                        Some(module.certificate.as_str().to_owned()),
                    ));
                }
                if decoded.imports().len() > MAX_DIRECT_IMPORTS {
                    return Err((
                        "resource",
                        "direct_import_count_exceeded",
                        Some(module.certificate.as_str().to_owned()),
                    ));
                }
                if !certificate_import_names_equal(&decoded, &module.imports) {
                    return Err((
                        "target",
                        "import_hash_mismatch",
                        Some(module.certificate.as_str().to_owned()),
                    ));
                }
                artifacts.insert(
                    module.module.clone(),
                    CertificateArtifact { bytes, decoded },
                );
            }
            let artifact = artifacts.get(&module_name).ok_or((
                "target",
                "target_certificate_missing",
                Some(module.certificate.as_str().to_owned()),
            ))?;
            for import in artifact.decoded.imports() {
                pending.push(import.module.clone());
            }
        } else if let Some(&index) = external_by_name.get(&module_name) {
            let import = &manifest.imports.as_deref().unwrap_or(&[])[index];
            let bytes = read_confined_file(
                root,
                Path::new(import.certificate.as_str()),
                MAX_CERTIFICATE_BYTES,
                ReadReasons {
                    missing: "import_certificate_missing",
                    symlink: "import_certificate_missing",
                    escape: "import_certificate_missing",
                    not_regular: "import_certificate_missing",
                    bytes_exceeded: "certificate_bytes_exceeded",
                },
            )
            .map_err(|error| {
                (
                    "target",
                    error.reason,
                    Some(import.certificate.as_str().to_owned()),
                )
            })?;
            let decoded = npa_cert::decode_module_cert(&bytes).map_err(|_| {
                (
                    "target",
                    "import_certificate_identity_mismatch",
                    Some(import.certificate.as_str().to_owned()),
                )
            })?;
            if decoded.header().module != import.module
                || PackageHash::from(decoded.hashes().export_hash) != import.export_hash
                || PackageHash::from(decoded.hashes().certificate_hash) != import.certificate_hash
            {
                return Err((
                    "target",
                    "import_certificate_identity_mismatch",
                    Some(import.certificate.as_str().to_owned()),
                ));
            }
            if decoded.imports().len() > MAX_DIRECT_IMPORTS {
                return Err((
                    "resource",
                    "direct_import_count_exceeded",
                    Some(import.certificate.as_str().to_owned()),
                ));
            }
            for child in decoded.imports() {
                pending.push(child.module.clone());
            }
            artifacts.insert(
                import.module.clone(),
                CertificateArtifact { bytes, decoded },
            );
        } else {
            return Err(("target", "import_missing", Some(module_name.as_dotted())));
        }
    }
    if artifacts.len() > MAX_SUPPORT_CLOSURE {
        return Err(("resource", "support_closure_count_exceeded", None));
    }
    Ok(())
}

fn verify_certificate_closure(
    target_module: &Name,
    artifacts: &BTreeMap<Name, CertificateArtifact>,
    policy: &AxiomPolicy,
    state: &mut SurfaceState,
) -> Result<BTreeMap<Name, Arc<VerifiedModule>>, ()> {
    let mut verified = BTreeMap::<Name, Arc<VerifiedModule>>::new();
    let mut pending = artifacts.keys().cloned().collect::<BTreeSet<_>>();
    while !pending.is_empty() {
        let names = pending.iter().cloned().collect::<Vec<_>>();
        let mut progress = false;
        for name in names {
            let artifact = &artifacts[&name];
            if !artifact
                .decoded
                .imports()
                .iter()
                .all(|import| verified.contains_key(&import.module))
            {
                continue;
            }
            let refs = verified.values().map(Arc::as_ref).collect::<Vec<_>>();
            let checked =
                match npa_cert::verify_module_cert_with_import_refs(&artifact.bytes, &refs, policy)
                {
                    Ok(checked) => checked,
                    Err(_) => {
                        let is_target = &name == target_module;
                        push_diagnostic(
                            state,
                            "target",
                            if is_target {
                                "target_certificate_verification_failed"
                            } else {
                                "import_certificate_identity_mismatch"
                            },
                            Some(name.as_dotted()),
                            None::<String>,
                            None::<String>,
                            None::<String>,
                        );
                        return Err(());
                    }
                };
            if checked.module() != &name {
                push_diagnostic(
                    state,
                    "target",
                    "import_certificate_identity_mismatch",
                    Some(name.as_dotted()),
                    Some("module"),
                    Some(name.as_dotted()),
                    Some(checked.module().as_dotted()),
                );
                return Err(());
            }
            verified.insert(name.clone(), Arc::new(checked));
            pending.remove(&name);
            progress = true;
        }
        if !progress {
            let name = pending
                .iter()
                .next()
                .cloned()
                .unwrap_or_else(|| Name::from_dotted("<missing>"));
            push_diagnostic(
                state,
                "target",
                "import_certificate_identity_mismatch",
                Some(name.as_dotted()),
                None::<String>,
                Some("verified import closure"),
                Some("unresolved certificate import"),
            );
            return Err(());
        }
    }
    Ok(verified)
}

fn certificate_import_names_equal(
    certificate: &npa_cert::ModuleCert,
    manifest_imports: &[Name],
) -> bool {
    certificate
        .imports()
        .iter()
        .map(|import| &import.module)
        .eq(manifest_imports.iter())
}

fn render_certificate_import_names(certificate: &npa_cert::ModuleCert) -> String {
    certificate
        .imports()
        .iter()
        .map(|import| import.module.as_dotted())
        .collect::<Vec<_>>()
        .join(",")
}

fn render_name_list(names: &[Name]) -> String {
    names
        .iter()
        .map(Name::as_dotted)
        .collect::<Vec<_>>()
        .join(",")
}

fn target_declaration_records(
    verified: &VerifiedModule,
    core: &[Decl],
) -> Result<Vec<DeclarationRecord>, &'static str> {
    let exported = verified
        .export_block()
        .iter()
        .filter_map(|entry| verified.name_table().get(entry.name))
        .map(Name::as_dotted)
        .collect::<BTreeSet<_>>();
    let payload_kinds = verified
        .declarations()
        .iter()
        .map(|declaration| {
            (
                payload_name(verified, &declaration.decl),
                certificate_kind(&declaration.decl),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let export_kinds = verified
        .export_block()
        .iter()
        .filter_map(|entry| {
            verified
                .name_table()
                .get(entry.name)
                .map(|name| (name.as_dotted(), export_kind(entry.kind)))
        })
        .collect::<BTreeMap<_, _>>();
    let mut records = Vec::with_capacity(core.len());
    for decl in core {
        let ty = declaration_type(decl)?;
        let (body, reducibility_or_opacity) = declaration_body(decl)?;
        let parent = declaration_parent(decl);
        let kind = payload_kinds
            .get(decl.name())
            .cloned()
            .or_else(|| export_kinds.get(decl.name()).cloned())
            .unwrap_or_else(|| kernel_kind(decl).to_owned());
        let dependencies = verified
            .declarations()
            .iter()
            .find(|certificate_decl| payload_name(verified, &certificate_decl.decl) == decl.name())
            .map(|certificate_decl| {
                certificate_decl
                    .dependencies
                    .iter()
                    .filter_map(|dependency| match dependency.global_ref() {
                        GlobalRef::Local { decl_index } => verified
                            .declarations()
                            .get(*decl_index)
                            .map(|declaration| payload_name(verified, &declaration.decl)),
                        GlobalRef::LocalGenerated { name, .. } => {
                            verified.name_table().get(*name).map(Name::as_dotted)
                        }
                        GlobalRef::Imported { .. } | GlobalRef::Builtin { .. } => None,
                    })
                    .collect::<Vec<String>>()
            })
            .unwrap_or_default();
        let family_members = family_members_for_decl(decl, |name, default_kind| {
            (
                if exported.contains(name) {
                    "public".to_owned()
                } else {
                    "support".to_owned()
                },
                export_kinds
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| default_kind.to_owned()),
            )
        })?;
        records.push(DeclarationRecord {
            name: decl.name().to_owned(),
            kind,
            surface: if exported.contains(decl.name()) {
                "public".to_owned()
            } else {
                "support".to_owned()
            },
            universe_params: decl.universe_params().to_vec(),
            universe_constraints: decl
                .universe_constraints()
                .iter()
                .map(|constraint| format!("{constraint:?}"))
                .collect(),
            ty,
            body,
            reducibility_or_opacity,
            parent,
            dependencies,
            family_members,
        });
    }
    Ok(records)
}

fn payload_name(verified: &VerifiedModule, payload: &DeclPayload) -> String {
    let name_id = match payload {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    verified
        .name_table()
        .get(name_id)
        .map(Name::as_dotted)
        .unwrap_or_else(|| "<invalid-name>".to_owned())
}

fn export_kind(kind: ExportKind) -> String {
    match kind {
        ExportKind::Axiom => "axiom",
        ExportKind::Def => "definition",
        ExportKind::Theorem => "theorem",
        ExportKind::Inductive => "inductive",
        ExportKind::Constructor => "constructor",
        ExportKind::Recursor => "recursor",
    }
    .to_owned()
}

fn proposal_declaration_records(
    proposal: &InterfaceProposal,
    core: &[Decl],
) -> Result<Vec<DeclarationRecord>, &'static str> {
    let mut roots = BTreeMap::<String, (&str, &str, Vec<String>)>::new();
    let mut families = BTreeMap::<String, String>::new();
    for declaration in &proposal.declarations {
        let kind = match declaration.kind {
            InterfaceProposalDeclarationKind::Definition => "definition",
            InterfaceProposalDeclarationKind::Theorem => "theorem",
            InterfaceProposalDeclarationKind::Inductive => "inductive",
        };
        roots.insert(
            declaration.name.clone(),
            (
                kind,
                declaration.surface.as_str(),
                declaration.depends_on.clone(),
            ),
        );
        for member in &declaration.family_members {
            families.insert(member.clone(), declaration.name.clone());
        }
    }
    let mut records = Vec::with_capacity(core.len());
    for decl in core {
        let name = decl.name().to_owned();
        let core_kind = kernel_kind(decl);
        let kind = roots
            .get(&name)
            .map(|(kind, _, _)| (*kind).to_owned())
            .or_else(|| {
                if core_kind == "constructor" || core_kind == "recursor" {
                    Some(core_kind.to_owned())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| core_kind.to_owned());
        let surface = roots
            .get(&name)
            .map(|(_, surface, _)| (*surface).to_owned())
            .or_else(|| {
                families
                    .get(&name)
                    .and_then(|root| roots.get(root).map(|(_, surface, _)| (*surface).to_owned()))
            })
            .unwrap_or_else(|| "support".to_owned());
        let dependencies = roots
            .get(&name)
            .map(|(_, _, dependencies)| dependencies.clone())
            .or_else(|| {
                families.get(&name).and_then(|root| {
                    roots
                        .get(root)
                        .map(|(_, _, dependencies)| dependencies.clone())
                })
            })
            .unwrap_or_default();
        let family_members = family_members_for_decl(decl, |name, default_kind| {
            let root = families.get(name);
            let surface = root
                .and_then(|root| roots.get(root))
                .map(|(_, surface, _)| (*surface).to_owned())
                .unwrap_or_else(|| "support".to_owned());
            (surface, default_kind.to_owned())
        })?;
        let ty = declaration_type(decl)?;
        let (body, reducibility_or_opacity) = declaration_body(decl)?;
        records.push(DeclarationRecord {
            name,
            kind,
            surface,
            universe_params: decl.universe_params().to_vec(),
            universe_constraints: decl
                .universe_constraints()
                .iter()
                .map(|constraint| format!("{constraint:?}"))
                .collect(),
            ty,
            body,
            reducibility_or_opacity,
            parent: declaration_parent(decl),
            dependencies,
            family_members,
        });
    }
    Ok(records)
}

fn family_members_for_decl(
    decl: &Decl,
    mut metadata: impl FnMut(&str, &'static str) -> (String, String),
) -> Result<Vec<FamilyRecord>, &'static str> {
    let mut records = Vec::new();
    let mut append_family = |parent: &str, data: &npa_kernel::InductiveDecl| {
        for constructor in &data.constructors {
            let (surface, kind) = metadata(&constructor.name, "constructor");
            records.push(FamilyRecord {
                name: constructor.name.clone(),
                kind,
                surface,
                parent: parent.to_owned(),
                ty: Some(canonical_term(&constructor.ty)?),
            });
        }
        if let Some(recursor) = &data.recursor {
            let (surface, kind) = metadata(&recursor.name, "recursor");
            records.push(FamilyRecord {
                name: recursor.name.clone(),
                kind,
                surface,
                parent: parent.to_owned(),
                ty: Some(canonical_term(&recursor.ty)?),
            });
        }
        Ok::<(), &'static str>(())
    };
    match decl {
        Decl::Inductive { name, data, .. } => append_family(name, data)?,
        Decl::MutualInductiveBlock { data, .. } => {
            for inductive in &data.inductives {
                append_family(&inductive.name, inductive)?;
            }
        }
        _ => {}
    }
    Ok(records)
}

fn canonical_term(term: &npa_kernel::Expr) -> Result<Vec<u8>, &'static str> {
    let bytes = npa_cert::core_expr_canonical_bytes(term);
    if bytes.len() > MAX_CORE_TERM_BYTES {
        Err("target_core_normalization_failed")
    } else {
        Ok(bytes)
    }
}

fn declaration_type(decl: &Decl) -> Result<Option<Vec<u8>>, &'static str> {
    match decl {
        Decl::MutualInductiveBlock { .. } => Ok(None),
        _ => canonical_term(decl.ty()).map(Some),
    }
}

fn declaration_body(decl: &Decl) -> Result<(Option<Vec<u8>>, String), &'static str> {
    match decl {
        Decl::Def {
            value,
            reducibility,
            ..
        }
        | Decl::DefConstrained {
            value,
            reducibility,
            ..
        } => Ok((
            Some(canonical_term(value)?),
            match reducibility {
                Reducibility::Reducible => "reducible".to_owned(),
                Reducibility::Opaque => "opaque".to_owned(),
            },
        )),
        Decl::Theorem { .. } | Decl::TheoremConstrained { .. } => Ok((None, "opaque".to_owned())),
        Decl::Axiom { .. } | Decl::AxiomConstrained { .. } => Ok((None, "opaque".to_owned())),
        Decl::Inductive { .. } | Decl::Constructor { .. } | Decl::Recursor { .. } => {
            Ok((None, "opaque".to_owned()))
        }
        Decl::MutualInductiveBlock { .. } => Ok((None, "opaque".to_owned())),
    }
}

fn declaration_parent(decl: &Decl) -> Option<String> {
    match decl {
        Decl::Constructor { inductive, .. } | Decl::Recursor { inductive, .. } => {
            Some(inductive.clone())
        }
        _ => None,
    }
}

fn kernel_kind(decl: &Decl) -> &'static str {
    match decl {
        Decl::Axiom { .. } | Decl::AxiomConstrained { .. } => "axiom",
        Decl::Def { .. } | Decl::DefConstrained { .. } => "definition",
        Decl::Theorem { .. } | Decl::TheoremConstrained { .. } => "theorem",
        Decl::Inductive { .. } | Decl::MutualInductiveBlock { .. } => "inductive",
        Decl::Constructor { .. } => "constructor",
        Decl::Recursor { .. } => "recursor",
    }
}

fn certificate_kind(payload: &DeclPayload) -> String {
    match payload {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => "axiom",
        DeclPayload::Def { .. } | DeclPayload::DefConstrained { .. } => "definition",
        DeclPayload::Theorem { .. } | DeclPayload::TheoremConstrained { .. } => "theorem",
        DeclPayload::Inductive { .. }
        | DeclPayload::InductiveConstrained { .. }
        | DeclPayload::MutualInductiveBlock { .. } => "inductive",
    }
    .to_owned()
}

fn compare_surface(
    proposal: &InterfaceProposal,
    target_manifest_imports: &[Name],
    target_certificate: &npa_cert::ModuleCert,
    proposal_records: &[DeclarationRecord],
    target_records: &[DeclarationRecord],
    state: &mut SurfaceState,
) {
    set_axis(
        &mut state.comparison.module_name,
        proposal.module == state.target.module.as_deref().unwrap_or_default(),
    );
    if state.comparison.module_name == "drift" {
        push_diagnostic(
            state,
            "drift",
            "module_name_drift",
            None::<String>,
            Some("module"),
            Some(proposal.module.clone()),
            state.target.module.clone(),
        );
    }

    let target_imports = target_certificate
        .imports()
        .iter()
        .map(|import| import.module.as_dotted())
        .collect::<Vec<_>>();
    let proposal_imports = proposal.imports.clone();
    let imports_equal = proposal_imports == target_imports
        && target_manifest_imports
            .iter()
            .map(Name::as_dotted)
            .eq(target_imports.iter().cloned());
    set_axis(&mut state.comparison.direct_imports, imports_equal);
    if !imports_equal {
        push_diagnostic(
            state,
            "drift",
            "direct_imports_drift",
            Some("imports"),
            Some("imports"),
            Some(render_string_list(&proposal_imports)),
            Some(render_string_list(&target_imports)),
        );
    }

    let proposal_names = proposal_records
        .iter()
        .map(|record| record.name.clone())
        .collect::<Vec<_>>();
    let target_names = target_records
        .iter()
        .map(|record| record.name.clone())
        .collect::<Vec<_>>();
    let order_equal = proposal_names == target_names;
    set_axis(&mut state.comparison.declaration_order, order_equal);
    if !order_equal {
        push_diagnostic(
            state,
            "drift",
            "declaration_order_drift",
            Some("declarations"),
            Some("ordinal"),
            Some(render_string_list(&proposal_names)),
            Some(render_string_list(&target_names)),
        );
    }
    let names_equal = proposal_names == target_names;
    set_axis(&mut state.comparison.declaration_names, names_equal);
    if !names_equal {
        push_diagnostic(
            state,
            "drift",
            "declaration_name_drift",
            Some("declarations"),
            Some("name"),
            Some(render_string_list(&proposal_names)),
            Some(render_string_list(&target_names)),
        );
    }
    let kinds_equal = aligned_equal(proposal_records, target_records, |left, right| {
        left.kind == right.kind
    });
    set_axis(&mut state.comparison.declaration_kinds, kinds_equal);
    if !kinds_equal {
        push_diagnostic(
            state,
            "drift",
            "declaration_kind_drift",
            Some("declarations"),
            Some("kind"),
            Some(render_record_field(proposal_records, |record| &record.kind)),
            Some(render_record_field(target_records, |record| &record.kind)),
        );
    }
    let surfaces_equal = aligned_equal(proposal_records, target_records, |left, right| {
        left.surface == right.surface
    });
    set_axis(&mut state.comparison.declaration_surfaces, surfaces_equal);
    if !surfaces_equal {
        push_diagnostic(
            state,
            "drift",
            "declaration_surface_drift",
            Some("declarations"),
            Some("surface"),
            Some(render_record_field(proposal_records, |record| {
                &record.surface
            })),
            Some(render_record_field(target_records, |record| {
                &record.surface
            })),
        );
    }
    let signatures_equal = aligned_equal(proposal_records, target_records, |left, right| {
        left.universe_params == right.universe_params
            && left.universe_constraints == right.universe_constraints
            && left.ty == right.ty
    });
    set_axis(&mut state.comparison.signatures, signatures_equal);
    if !signatures_equal {
        push_diagnostic(
            state,
            "drift",
            "signature_drift",
            Some("declarations"),
            Some("signature"),
            Some(render_record_terms(proposal_records, false)),
            Some(render_record_terms(target_records, false)),
        );
    }
    let proposal_definitions = proposal_records
        .iter()
        .filter(|record| record.kind == "definition")
        .collect::<Vec<_>>();
    let target_definitions = target_records
        .iter()
        .filter(|record| record.kind == "definition")
        .collect::<Vec<_>>();
    let definition_bodies_equal = proposal_definitions.len() == target_definitions.len()
        && proposal_definitions
            .iter()
            .zip(target_definitions.iter())
            .all(|(left, right)| {
                left.name == right.name
                    && left.body == right.body
                    && left.reducibility_or_opacity == right.reducibility_or_opacity
            });
    set_axis(
        &mut state.comparison.definition_bodies,
        definition_bodies_equal,
    );
    if !definition_bodies_equal {
        push_diagnostic(
            state,
            "drift",
            "definition_body_drift",
            Some("declarations"),
            Some("body"),
            Some(render_record_terms(proposal_records, true)),
            Some(render_record_terms(target_records, true)),
        );
    }
    let proposal_family = family_records(proposal_records);
    let target_family = family_records(target_records);
    let family_equal = proposal_family == target_family;
    set_axis(&mut state.comparison.inductive_family_members, family_equal);
    if !family_equal {
        push_diagnostic(
            state,
            "drift",
            "inductive_family_drift",
            Some("family_members"),
            Some("family_members"),
            Some(render_family_list(&proposal_family)),
            Some(render_family_list(&target_family)),
        );
    }

    let proposal_support = support_closure(proposal_records);
    let target_support = support_closure(target_records);
    let support_equal = proposal_support == target_support;
    set_axis(
        &mut state.comparison.exported_support_closure,
        support_equal,
    );
    if !support_equal {
        let proposal_set = proposal_support
            .iter()
            .map(|record| record.name.clone())
            .collect::<BTreeSet<_>>();
        let target_set = target_support
            .iter()
            .map(|record| record.name.clone())
            .collect::<BTreeSet<_>>();
        if target_set.difference(&proposal_set).next().is_some() {
            push_diagnostic(
                state,
                "drift",
                "exported_support_added",
                Some("support_closure"),
                Some("name"),
                Some(render_support_names(&proposal_support)),
                Some(render_support_names(&target_support)),
            );
        }
        if proposal_set.difference(&target_set).next().is_some() {
            push_diagnostic(
                state,
                "drift",
                "exported_support_removed",
                Some("support_closure"),
                Some("name"),
                Some(render_support_names(&proposal_support)),
                Some(render_support_names(&target_support)),
            );
        }
        if proposal_set == target_set {
            push_diagnostic(
                state,
                "drift",
                "support_closure_drift",
                Some("support_closure"),
                Some("dependency_ordinals"),
                Some(render_support_records(&proposal_support)),
                Some(render_support_records(&target_support)),
            );
        }
    }
}

fn set_axis(axis: &mut String, equal: bool) {
    *axis = if equal { "equal" } else { "drift" }.to_owned();
}

fn aligned_equal(
    left: &[DeclarationRecord],
    right: &[DeclarationRecord],
    predicate: impl Fn(&DeclarationRecord, &DeclarationRecord) -> bool,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| predicate(left, right))
}

fn family_records(records: &[DeclarationRecord]) -> Vec<FamilyRecord> {
    let mut families = Vec::new();
    for record in records {
        families.extend(record.family_members.clone());
        if let Some(parent) = &record.parent {
            families.push(FamilyRecord {
                name: record.name.clone(),
                kind: record.kind.clone(),
                surface: record.surface.clone(),
                parent: parent.clone(),
                ty: record.ty.clone(),
            });
        }
    }
    families
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SupportClosureRecord {
    name: String,
    kind: String,
    surface: String,
    parent: Option<String>,
    dependencies: Vec<usize>,
}

fn support_closure(records: &[DeclarationRecord]) -> Vec<SupportClosureRecord> {
    let by_name = records
        .iter()
        .enumerate()
        .map(|(index, record)| (record.name.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let mut reachable = BTreeSet::new();
    let mut pending = records
        .iter()
        .filter(|record| record.surface == "public")
        .flat_map(|record| record.dependencies.iter())
        .filter_map(|name| by_name.get(name.as_str()).copied())
        .collect::<Vec<_>>();
    while let Some(index) = pending.pop() {
        if !reachable.insert(index) {
            continue;
        }
        for dependency in &records[index].dependencies {
            if let Some(&dependency_index) = by_name.get(dependency.as_str()) {
                pending.push(dependency_index);
            }
        }
    }
    let ordered_indices = records
        .iter()
        .enumerate()
        .filter_map(|(index, record)| {
            (record.surface == "support" && reachable.contains(&index)).then_some(index)
        })
        .collect::<Vec<_>>();
    let closure_ordinals = ordered_indices
        .iter()
        .enumerate()
        .map(|(ordinal, index)| (*index, ordinal))
        .collect::<BTreeMap<_, _>>();
    ordered_indices
        .iter()
        .copied()
        .map(|index| {
            let record = &records[index];
            SupportClosureRecord {
                name: record.name.clone(),
                kind: record.kind.clone(),
                surface: record.surface.clone(),
                parent: record.parent.clone(),
                dependencies: record
                    .dependencies
                    .iter()
                    .filter_map(|name| {
                        by_name
                            .get(name.as_str())
                            .and_then(|index| closure_ordinals.get(index).copied())
                    })
                    .collect(),
            }
        })
        .collect()
}

fn render_support_names(records: &[SupportClosureRecord]) -> String {
    render_string_list(
        &records
            .iter()
            .map(|record| record.name.clone())
            .collect::<Vec<_>>(),
    )
}

fn render_support_records(records: &[SupportClosureRecord]) -> String {
    let mut value = String::new();
    for record in records {
        if !value.is_empty() {
            value.push(',');
        }
        value.push_str(&record.name);
        value.push(':');
        value.push_str(&record.kind);
        value.push(':');
        value.push_str(record.parent.as_deref().unwrap_or(""));
        value.push(':');
        value.push_str(
            &record
                .dependencies
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("."),
        );
    }
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        value
    } else {
        format_package_hash(&package_file_hash(value.as_bytes()))
    }
}

fn render_string_list(values: &[String]) -> String {
    let value = values.join(",");
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        value
    } else {
        format_package_hash(&package_file_hash(value.as_bytes()))
    }
}

fn render_record_field(
    records: &[DeclarationRecord],
    field: impl Fn(&DeclarationRecord) -> &String,
) -> String {
    render_string_list(&records.iter().map(field).cloned().collect::<Vec<_>>())
}

fn render_record_terms(records: &[DeclarationRecord], bodies: bool) -> String {
    let mut bytes = Vec::new();
    for record in records {
        if bodies && record.kind != "definition" {
            continue;
        }
        if let Some(ty) = &record.ty {
            bytes.extend(ty.iter().copied());
        }
        if let Some(body) = &record.body {
            bytes.extend(body.iter().copied());
        }
    }
    format_package_hash(&package_file_hash(&bytes))
}

fn render_family_list(records: &[FamilyRecord]) -> String {
    let mut value = String::new();
    for record in records {
        if !value.is_empty() {
            value.push(',');
        }
        value.push_str(&record.name);
        value.push(':');
        value.push_str(&record.kind);
        value.push(':');
        value.push_str(&record.surface);
        value.push(':');
        value.push_str(&record.parent);
    }
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        value
    } else {
        format_package_hash(&package_file_hash(value.as_bytes()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    use std::os::unix::fs::symlink;

    fn record(name: &str, surface: &str, dependencies: &[&str]) -> DeclarationRecord {
        DeclarationRecord {
            name: name.to_owned(),
            kind: "theorem".to_owned(),
            surface: surface.to_owned(),
            universe_params: Vec::new(),
            universe_constraints: Vec::new(),
            ty: Some(Vec::new()),
            body: None,
            reducibility_or_opacity: "opaque".to_owned(),
            parent: None,
            dependencies: dependencies.iter().map(|name| (*name).to_owned()).collect(),
            family_members: Vec::new(),
        }
    }

    #[test]
    fn support_closure_follows_recursive_dependencies() {
        let records = vec![
            record("public_root", "public", &["support_a"]),
            record("support_a", "support", &["support_b"]),
            record("support_b", "support", &[]),
            record("unreachable", "support", &[]),
        ];
        let closure = support_closure(&records);
        assert_eq!(
            closure
                .iter()
                .map(|record| record.name.as_str())
                .collect::<Vec<_>>(),
            vec!["support_a", "support_b"]
        );
        assert_eq!(closure[0].dependencies, vec![1]);
        assert!(closure[1].dependencies.is_empty());
    }

    #[test]
    fn family_comparison_retains_member_identity_and_surface() {
        let mut root = record("Root", "public", &[]);
        root.family_members.push(FamilyRecord {
            name: "Root.mk".to_owned(),
            kind: "constructor".to_owned(),
            surface: "public".to_owned(),
            parent: "Root".to_owned(),
            ty: Some(vec![1, 2, 3]),
        });
        let family = family_records(&[root]);
        assert_eq!(family.len(), 1);
        assert_eq!(family[0].name, "Root.mk");
        assert_eq!(family[0].surface, "public");
        assert_eq!(family[0].ty, Some(vec![1, 2, 3]));
    }

    #[cfg(unix)]
    #[test]
    fn confined_reader_rejects_intermediate_symlinks_and_uses_retained_root() {
        let base = std::env::temp_dir().join(format!(
            "npa-interface-surface-reader-{}",
            std::process::id()
        ));
        let original = base.join("original");
        let replacement = base.join("replacement");
        let relocated = base.join("relocated");
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(original.join("real")).unwrap();
        std::fs::create_dir_all(replacement.join("real")).unwrap();
        std::fs::write(original.join("real/value"), b"original").unwrap();
        std::fs::write(replacement.join("real/value"), b"replacement").unwrap();
        symlink("real", original.join("linked")).unwrap();

        let retained = open_absolute_directory(&original, false).unwrap();
        let reasons = ReadReasons {
            missing: "missing",
            symlink: "symlink",
            escape: "escape",
            not_regular: "not_regular",
            bytes_exceeded: "too_large",
        };
        assert_eq!(
            read_confined_file(&retained, Path::new("real/value"), 8, reasons).unwrap(),
            b"original"
        );
        assert_eq!(
            read_confined_file(&retained, Path::new("linked/value"), 8, reasons)
                .unwrap_err()
                .reason,
            "symlink"
        );

        std::fs::rename(&original, &relocated).unwrap();
        std::fs::rename(&replacement, &original).unwrap();
        assert_eq!(
            read_confined_file(&retained, Path::new("real/value"), 8, reasons).unwrap(),
            b"original"
        );
        std::fs::remove_dir_all(base).unwrap();
    }
}
