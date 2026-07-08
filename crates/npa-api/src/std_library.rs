//! Phase 6 standard-library machine boundary.
//!
//! The Human profile owns source text, notation, pretty statements, and
//! human-facing attributes used to author the library. This module owns the
//! Machine/AI release boundary: fixed `.npcert` locators, release-wide
//! `Std.machine-*.json` artifacts, and identities derived from verified
//! certificates. Human source files, per-module debug JSON, and attribute
//! tables may exist beside a package as build/debug inputs, but they are not
//! read by the AI fast path and are never release hash inputs.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
};

use npa_cert::{
    build_module_cert, decode_module_cert, verify_module_cert, AxiomPolicy, AxiomRef, CertError,
    CoreModule, DeclCert, DeclPayload, ExportEntry, ExportKind, GlobalRef, Hash, ImportEntry,
    ModuleCert, Name, TermId, TermNode, TrustMode, VerifiedModule, VerifierSession,
};
use npa_kernel::{eq_inductive, level::normalize_level, nat_inductive, type0, Decl, Expr, Level};
use npa_tactic::{
    EqFamilyRef, MachineTacticEnv, MachineTacticOptions, NatFamilyRef, ResolvedSimpRule,
    RewriteDirection, SimpRuleRef, VerifiedImportRef,
};
use sha2::{Digest, Sha256};

use crate::{
    current::{
        encode_machine_axiom_ref_wire, MachineAxiomRefWire, MachineCheckedCurrentDeclContext,
    },
    json::{JsonDocument, JsonParseErrorKind, JsonValue, JsonValueKind},
    projection::{
        project_import_certificate_context, ImportProjectionError, MachineImportCertificateContext,
        VerifiedImportKey, VerifiedModuleCertificateInput,
    },
    search::MachineTheoremMode,
    session::{validate_machine_tactic_options_request_against_context, MachineSessionCreateError},
    types::{
        machine_api_name_canonical_bytes, parse_fully_qualified_name_wire, parse_hash_string,
        parse_machine_surface_renderable_name_wire, parse_machine_universe_param_name,
        parse_module_name_wire, KernelCheckProfileId, MachineTacticOptionsRequest,
        MachineWireGrammarError, KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC,
        KERNEL_CHECK_PROFILE_BUILTIN_NONE,
    },
    validation::{parse_strict_u64_token, StrictUnsignedIntegerError},
};

const STD_LOGIC_PATH: &str = "Std/Logic.npcert";
const STD_NAT_PATH: &str = "Std/Nat.npcert";
const STD_LIST_PATH: &str = "Std/List.npcert";
const STD_ALGEBRA_BASIC_PATH: &str = "Std/Algebra/Basic.npcert";
const STD_SOURCE_PACKAGE_ROOT: &str = "Std";
const STD_LOGIC_SOURCE_PATH: &str = "Std/Logic.npa";
const STD_NAT_SOURCE_PATH: &str = "Std/Nat.npa";
const STD_LIST_SOURCE_PATH: &str = "Std/List.npa";
const STD_ALGEBRA_BASIC_SOURCE_PATH: &str = "Std/Algebra/Basic.npa";
const STD_MACHINE_RELEASE_JSON_PATH: &str = "Std.machine-release.json";
const STD_MACHINE_IMPORT_BUNDLES_JSON_PATH: &str = "Std.machine-import-bundles.json";
const STD_MACHINE_THEOREM_INDEX_JSON_PATH: &str = "Std.machine-theorem-index.json";
const STD_MACHINE_REWRITE_PROFILES_JSON_PATH: &str = "Std.machine-rewrite-profiles.json";
const STD_MACHINE_SIMP_PROFILES_JSON_PATH: &str = "Std.machine-simp-profiles.json";
const STD_MACHINE_AXIOM_REPORT_JSON_PATH: &str = "Std.machine-axiom-report.json";
const STD_MACHINE_PROMPT_METADATA_JSON_PATH: &str = "Std.machine-prompt-metadata.json";
const STD_LIBRARY_PROTOCOL_VERSION: &str = "npa.stdlib-machine.v1";
const STD_LIBRARY_PROFILE_ID: &str = "npa.stdlib.mvp.v1";
const STD_PROMPT_METADATA_PROFILE_ID: &str = "npa.stdlib.prompt-metadata.mvp.v1";
const STD_CORE_SPEC_ID: &str = "core-spec-v0.1";
const STD_KERNEL_SEMANTICS_PROFILE_ID: &str = "npa-kernel.core.v0.1";
const STD_REDUCTION_PROFILE_ID: &str = "beta-delta-iota-zeta.v0.1";
const STD_UNIVERSE_PROFILE_ID: &str = "levels-imax-v0.1";
const STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE: &str = KERNEL_CHECK_PROFILE_BUILTIN_NONE;
const STD_KERNEL_BUILTIN_NONE_PROFILE_ID: &str = "builtin-none-v0.1";
const STD_KERNEL_BUILTIN_NAT_EQ_REC_PROFILE_ID: &str = "builtin-nat-eq-rec-v0.1";
const STD_CERTIFICATE_ENCODING: &str = "npa.certificate.canonical.v0.1.hex";
const STD_MODULE_ARTIFACT_TAG: &str = "npa.std-library.std-module-artifact.v1";
const STD_LIBRARY_RELEASE_TAG: &str = "npa.std-library.std-library-release.v1";
const STD_IMPORT_BUNDLE_TAG: &str = "npa.std-library.std-import-bundle.v1";
const STD_IMPORT_BUNDLE_SET_TAG: &str = "npa.std-library.std-import-bundle-set.v1";
const STD_TACTIC_OPTIONS_RECIPE_TAG: &str = "npa.std-library.std-tactic-options-recipe.v1";
const MACHINE_TACTIC_KERNEL_CHECK_PROFILE_TAG: &str = "npa.machine-tactic.kernel-check-profile.v1";
const STD_AXIOM_REPORT_TAG: &str = "npa.std-library.std-axiom-report.v1";
const STD_THEOREM_INDEX_TAG: &str = "npa.std-library.std-theorem-index.v1";
const STD_GLOBAL_REF_TAG: &str = "npa.std-library.std-global-ref.v1";
const STD_GLOBAL_REF_VIEW_TAG: &str = "npa.std-library.std-global-ref-view.v1";
const STD_HUMAN_THEOREM_SEARCH_VIEW_TAG: &str = "npa.std-library.human-theorem-search-view.v1";
const STD_HUMAN_THEOREM_SEARCH_ENTRY_TAG: &str = "npa.std-library.human-theorem-search-entry.v1";
const STD_HUMAN_MODULE_INDEX_DEBUG_TAG: &str = "npa.std-library.human-module-index-debug.v1";
const STD_HUMAN_MODULE_AXIOMS_DEBUG_TAG: &str = "npa.std-library.human-module-axioms-debug.v1";
const STD_HUMAN_MODULE_GRAPH_DEBUG_TAG: &str = "npa.std-library.human-module-graph-debug.v1";
const STD_HUMAN_MODULE_GRAPH_EDGE_TAG: &str = "npa.std-library.human-module-graph-edge.v1";
const STD_RULE_TELESCOPE_TAG: &str = "npa.std-library.std-rule-telescope.v1";
const STD_REWRITE_PROFILE_TAG: &str = "npa.std-library.std-rewrite-profile.v1";
const STD_REWRITE_PROFILE_SET_TAG: &str = "npa.std-library.std-rewrite-profile-set.v1";
const STD_SIMP_PROFILE_TAG: &str = "npa.std-library.std-simp-profile.v1";
const STD_SIMP_PROFILE_SET_TAG: &str = "npa.std-library.std-simp-profile-set.v1";
const STD_PROMPT_METADATA_SET_TAG: &str = "npa.std-library.std-prompt-metadata-set.v1";
const STD_PROMPT_METADATA_TAG: &str = "npa.std-library.std-prompt-metadata.v1";
const STD_PROMPT_EXAMPLE_TAG: &str = "npa.std-library.std-prompt-example.v1";
const STD_AUDIT_CHECK_TAG: &str = "npa.independent-checker.std-library-audit-check.v1";
const STD_AUDIT_REPORT_TAG: &str = "npa.independent-checker.std-library-audit-report.v1";
const MACHINE_API_AXIOM_REF_WIRE_TAG: &str = "npa.machine-api.axiom-ref-wire.v1";
/// Producer profile used by the legacy two-module `npa-std` package fixture.
///
/// The profile treats source files as source-package skeletons that fix import
/// intent. Package manifest module entries fix module membership. Certificate
/// contents are generated by the deterministic Rust core-module builders below.
pub const LEGACY_STD_PACKAGE_PRODUCER_PROFILE: &str = "std-library-legacy-core-builder";
const STD_THEOREM_INDEX_PROFILE_ID: &str = "npa.stdlib.theorem-index.mvp.v1";
const STD_AUDIT_PROFILE_ID: &str = "npa.independent-checker.stdlib-audit.mvp.v1";
const STD_LOGIC_BUNDLE_ID: &str = "std.logic.mvp";
const STD_NAT_BUNDLE_ID: &str = "std.nat.mvp";
const STD_LIST_BUNDLE_ID: &str = "std.list.mvp";
const STD_ALGEBRA_BASIC_BUNDLE_ID: &str = "std.algebra-basic.mvp";
const STD_ALL_BUNDLE_ID: &str = "std.all.mvp";
const STD_LOGIC_RECIPE_ID: &str = "std.logic-basic";
const STD_NAT_RECIPE_ID: &str = "std.nat-simp";
const STD_LIST_RECIPE_ID: &str = "std.list-simp";
const STD_ALL_RECIPE_ID: &str = "std.all-simp";
const STD_LOGIC_RW_PROFILE_ID: &str = "std.logic.rw";
const STD_NAT_RW_PROFILE_ID: &str = "std.nat.rw";
const STD_LIST_RW_PROFILE_ID: &str = "std.list.rw";
const STD_ALL_RW_PROFILE_ID: &str = "std.all.rw";
const STD_LOGIC_SIMP_PROFILE_ID: &str = "std.logic.simp";
const STD_NAT_SIMP_PROFILE_ID: &str = "std.nat.simp";
const STD_LIST_SIMP_PROFILE_ID: &str = "std.list.simp";
const STD_ALL_SIMP_PROFILE_ID: &str = "std.all.simp";
const STD_MAX_SIMP_REWRITE_STEPS: u64 = 100;
const STD_MAX_OPEN_GOALS: u64 = 32;
const STD_MAX_METAS: u64 = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdModuleLocator {
    pub module: Name,
    pub relative_path: String,
}

impl MachineStdModuleLocator {
    pub fn new(module: Name, relative_path: impl Into<String>) -> Self {
        Self {
            module,
            relative_path: relative_path.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdSourcePackageEntry {
    pub module: Name,
    pub source_relative_path: String,
    pub certificate_relative_path: String,
}

impl MachineStdSourcePackageEntry {
    pub fn new(
        module: Name,
        source_relative_path: impl Into<String>,
        certificate_relative_path: impl Into<String>,
    ) -> Self {
        Self {
            module,
            source_relative_path: source_relative_path.into(),
            certificate_relative_path: certificate_relative_path.into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MachineStdLoadedRelease {
    modules: Vec<MachineStdLoadedModule>,
    module_index: BTreeMap<Name, usize>,
    verification_order: Vec<Name>,
}

impl MachineStdLoadedRelease {
    pub fn modules(&self) -> &[MachineStdLoadedModule] {
        &self.modules
    }

    pub fn module(&self, module: &Name) -> Option<&MachineStdLoadedModule> {
        self.module_index
            .get(module)
            .map(|index| &self.modules[*index])
    }

    pub fn verification_order(&self) -> &[Name] {
        &self.verification_order
    }
}

#[derive(Clone, Debug)]
pub struct MachineStdLoadedModule {
    pub module: Name,
    pub locator_path: String,
    pub resolved_path: PathBuf,
    pub certificate_bytes: Vec<u8>,
    pub certificate_bytes_hash: Hash,
    pub expected_export_hash: Hash,
    pub expected_certificate_hash: Hash,
    pub axiom_report_hash: Hash,
    pub imports: Vec<ImportEntry>,
    pub verified_module: VerifiedModule,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdLibraryRelease {
    pub protocol_version: String,
    pub library_profile_id: String,
    pub core_spec_id: String,
    pub kernel_semantics_profile_id: String,
    pub modules: Vec<MachineStdModuleArtifact>,
    pub import_bundles_hash: Hash,
    pub theorem_index_hash: Hash,
    pub simp_profiles_hash: Hash,
    pub rewrite_profiles_hash: Hash,
    pub axiom_report_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdModuleArtifact {
    pub module: Name,
    pub expected_export_hash: Hash,
    pub expected_certificate_hash: Hash,
    pub certificate_encoding: String,
    pub certificate_bytes_hash: Hash,
    pub axiom_report_hash: Hash,
    pub public_export_count: u64,
    pub theorem_index_entry_count: u64,
    pub simp_rule_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdAxiomReport {
    pub library_profile_id: String,
    pub modules: Vec<MachineStdModuleAxiomReport>,
    pub axiom_report_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdModuleAxiomReport {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub module_axioms: Vec<MachineStdAxiomRef>,
    pub transitive_axioms: Vec<MachineStdAxiomRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdAxiomRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdTheoremIndex {
    pub index_profile_id: String,
    pub library_profile_id: String,
    pub entries: Vec<MachineStdTheoremEntry>,
    pub index_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdTheoremEntry {
    pub global_ref: MachineStdGlobalRef,
    pub kind: MachineStdTheoremKind,
    pub universe_params: Vec<String>,
    pub statement_core_hash: Hash,
    pub statement_head: Option<MachineStdGlobalRefView>,
    pub constants: Vec<MachineStdGlobalRefView>,
    pub modes: Vec<MachineTheoremMode>,
    pub attributes: Vec<MachineStdAttribute>,
    pub rewrite_descriptors: Vec<MachineStdRewriteDescriptor>,
    pub axiom_dependencies: Vec<MachineStdAxiomRef>,
    pub proof_term_size: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdTheoremSearchView {
    pub library_profile_id: String,
    pub entries: Vec<HumanStdTheoremSearchEntry>,
    pub debug_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdTheoremSearchEntry {
    pub global_ref: MachineStdGlobalRef,
    pub kind: MachineStdTheoremKind,
    pub categories: Vec<HumanStdTheoremCategory>,
    pub display_attributes: Vec<HumanStdTheoremDisplayAttribute>,
    pub statement_core_hash: Hash,
    pub statement_head: Option<MachineStdGlobalRefView>,
    pub constants: Vec<MachineStdGlobalRefView>,
    pub axiom_dependencies: Vec<MachineStdAxiomRef>,
    pub proof_term_size: Option<u64>,
    pub suggested_tactics: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HumanStdTheoremCategory {
    Exact,
    Apply,
    Rw,
    Simp,
    Intro,
    Elim,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum HumanStdTheoremDisplayAttribute {
    Simp,
    Rw,
    Apply,
    Intro,
    Elim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdModuleDebugViews {
    pub module: Name,
    pub index: HumanStdModuleIndexDebugView,
    pub axioms: HumanStdModuleAxiomsDebugView,
    pub graph: HumanStdModuleGraphDebugView,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdModuleIndexDebugView {
    pub module: Name,
    pub entries: Vec<HumanStdTheoremSearchEntry>,
    pub debug_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdModuleAxiomsDebugView {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub module_axioms: Vec<MachineStdAxiomRef>,
    pub transitive_axioms: Vec<MachineStdAxiomRef>,
    pub debug_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdModuleGraphDebugView {
    pub module: Name,
    pub edges: Vec<HumanStdDependencyEdge>,
    pub debug_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HumanStdDependencyEdge {
    pub source: MachineStdGlobalRef,
    pub kind: HumanStdDependencyKind,
    pub target: HumanStdDependencyTarget,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HumanStdDependencyKind {
    StatementHead,
    StatementConstant,
    AxiomDependency,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HumanStdDependencyTarget {
    GlobalRef(MachineStdGlobalRefView),
    Axiom(MachineStdAxiomRef),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MachineStdGlobalRef {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub certificate_hash: Hash,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineStdTheoremKind {
    Theorem,
    Axiom,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineStdAttribute {
    Simp,
    Rw,
    Intro,
    Elim,
    Apply,
    Refl,
    Trans,
    Congr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdRewriteDescriptor {
    pub source: MachineStdGlobalRef,
    pub direction: RewriteDirection,
    pub safety: MachineStdRewriteSafety,
    pub lhs_core_hash: Hash,
    pub rhs_core_hash: Hash,
    pub rule_telescope_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineStdRewriteSafety {
    SimpSafe,
    RwOnly,
    UnsafeForAutomation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdRewriteProfile {
    pub profile_id: String,
    pub required_import_bundle_id: String,
    pub kernel_check_profile: String,
    pub eq_family: Option<EqFamilyRef>,
    pub descriptors: Vec<MachineStdRewriteDescriptor>,
    pub profile_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdRewriteProfileSet {
    pub library_profile_id: String,
    pub profiles: Vec<MachineStdRewriteProfile>,
    pub rewrite_profiles_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdSimpProfile {
    pub profile_id: String,
    pub required_import_bundle_id: String,
    pub kernel_check_profile: String,
    pub eq_family: Option<EqFamilyRef>,
    pub rules: Vec<SimpRuleRef>,
    pub profile_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdSimpProfileSet {
    pub library_profile_id: String,
    pub profiles: Vec<MachineStdSimpProfile>,
    pub simp_profiles_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdPromptMetadataSet {
    pub metadata_profile_id: String,
    pub library_profile_id: String,
    pub entries: Vec<MachineStdPromptMetadata>,
    pub prompt_metadata_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdPromptMetadata {
    pub global_ref: MachineStdGlobalRef,
    pub short_doc: Option<String>,
    pub examples: Vec<MachineStdPromptExample>,
    pub tags: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdPromptExample {
    pub goal_core_hash: Hash,
    pub imports_bundle_id: String,
    pub candidate_kind: String,
    pub display: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineStdGlobalRefView {
    Decl {
        module: Name,
        name: Name,
        export_hash: Hash,
        certificate_hash: Hash,
        decl_interface_hash: Hash,
        public_export: bool,
    },
    Generated {
        module: Name,
        parent_name: Name,
        name: Name,
        export_hash: Hash,
        certificate_hash: Hash,
        parent_decl_interface_hash: Hash,
        decl_interface_hash: Hash,
        public_export: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdImportBundleSet {
    pub library_profile_id: String,
    pub bundles: Vec<MachineStdImportBundle>,
    pub import_bundles_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdImportBundle {
    pub bundle_id: String,
    pub root_imports: Vec<VerifiedImportKey>,
    pub import_closure: Vec<MachineStdImportCertificate>,
    pub allow_axioms: Vec<MachineAxiomRefWire>,
    pub recommended_tactic_options: MachineStdTacticOptionsRecipe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdImportCertificate {
    pub module: Name,
    pub expected_export_hash: Hash,
    pub expected_certificate_hash: Hash,
    pub certificate_encoding: String,
    pub certificate_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdTacticOptionsRecipe {
    pub recipe_id: String,
    pub kernel_check_profile: String,
    pub simp_rules: Vec<SimpRuleRef>,
    pub eq_family: Option<EqFamilyRef>,
    pub nat_family: Option<NatFamilyRef>,
    pub max_simp_rewrite_steps: u64,
    pub max_open_goals: u64,
    pub max_metas: u64,
}

#[derive(Clone, Debug)]
pub struct MachineStdValidatedRelease {
    pub manifest: MachineStdLibraryRelease,
    pub loaded: MachineStdLoadedRelease,
    pub axiom_report: MachineStdAxiomReport,
    pub import_bundles: MachineStdImportBundleSet,
    pub std_library_release_hash: Hash,
}

#[derive(Clone, Copy, Debug)]
pub struct MachineStdReleaseSidecarJson<'a> {
    pub import_bundles_json: &'a str,
    pub theorem_index_json: &'a str,
    pub rewrite_profiles_json: &'a str,
    pub simp_profiles_json: &'a str,
    pub axiom_report_json: &'a str,
    pub prompt_metadata_json: Option<&'a str>,
}

#[derive(Clone, Copy, Debug)]
pub struct MachineStdAuditArtifacts<'a> {
    pub import_bundles: &'a MachineStdImportBundleSet,
    pub theorem_index: &'a MachineStdTheoremIndex,
    pub rewrite_profiles: &'a MachineStdRewriteProfileSet,
    pub simp_profiles: &'a MachineStdSimpProfileSet,
    pub axiom_report: &'a MachineStdAxiomReport,
    pub prompt_metadata: Option<&'a MachineStdPromptMetadataSet>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdAuditReport {
    pub audit_profile_id: String,
    pub library_profile_id: String,
    pub std_library_release_hash: Hash,
    pub manifest_hash: Hash,
    pub prompt_metadata_hash: Option<Hash>,
    pub prompt_metadata_excluded_from_release_hash: bool,
    pub checks: Vec<MachineStdAuditCheck>,
    pub audit_report_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdAuditCheck {
    pub check_id: String,
    pub subject: String,
    pub passed: bool,
    pub evidence_hash: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineStdArtifactKind {
    LibraryRelease,
    ImportBundles,
    TheoremIndex,
    RewriteProfiles,
    SimpProfiles,
    AxiomReport,
    PromptMetadata,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineStdArtifactShapeError {
    pub artifact: MachineStdArtifactKind,
    pub path: String,
    pub reason: MachineStdArtifactShapeErrorReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineStdArtifactShapeErrorReason {
    JsonParse {
        offset: usize,
        kind: JsonParseErrorKind,
    },
    ExpectedObject {
        actual: JsonValueKind,
    },
    ExpectedArray {
        actual: JsonValueKind,
    },
    DuplicateKey {
        key: String,
    },
    UnknownField {
        field: String,
    },
    MissingField {
        field: &'static str,
    },
    NullField {
        field: &'static str,
    },
    TypeMismatch {
        field: &'static str,
        expected: &'static str,
        actual: JsonValueKind,
    },
    InvalidUnsignedInteger {
        field: &'static str,
        raw: String,
        error: StrictUnsignedIntegerError,
    },
    InvalidHashString {
        field: &'static str,
    },
    InvalidName {
        field: &'static str,
    },
    InvalidHexString {
        field: &'static str,
    },
    InvalidEnumString {
        field: &'static str,
    },
}

#[derive(Debug)]
pub enum MachineStdReleaseArtifactError {
    ReadArtifact {
        artifact: MachineStdArtifactKind,
        path: PathBuf,
        source: io::Error,
    },
    InvalidStdArtifactShape(MachineStdArtifactShapeError),
    InvalidStdLibraryRelease(MachineStdLibraryReleaseError),
    InvalidStdAxiomPolicy(MachineStdAxiomPolicyError),
    InvalidStdImportBundle(MachineStdImportBundleError),
    InvalidStdRewriteProfile(MachineStdRewriteProfileError),
    InvalidStdSimpProfile(MachineStdSimpProfileError),
    InvalidStdTheoremIndex(MachineStdTheoremIndexError),
    InvalidStdPromptMetadata(MachineStdPromptMetadataError),
}

#[derive(Debug)]
pub enum MachineStdAuditError {
    InvalidStdReleaseArtifact(MachineStdReleaseArtifactError),
    InvalidStdLibraryRelease(MachineStdLibraryReleaseError),
    InvalidStdAxiomPolicy(MachineStdAxiomPolicyError),
    InvalidStdImportBundle(MachineStdImportBundleError),
    InvalidStdRewriteProfile(MachineStdRewriteProfileError),
    InvalidStdSimpProfile(MachineStdSimpProfileError),
    InvalidStdTheoremIndex(MachineStdTheoremIndexError),
    InvalidStdPromptMetadata(MachineStdPromptMetadataError),
    ReleaseHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    SidecarHashMismatch {
        field: &'static str,
        expected: Hash,
        actual: Hash,
    },
    ProfileTargetMismatch {
        profile_id: String,
        name: Name,
    },
    CustomAllowAxiom {
        bundle_id: String,
        axiom: Box<MachineAxiomRefWire>,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdLibraryReleaseError {
    ScalarMismatch {
        field: &'static str,
        expected: &'static str,
        actual: String,
    },
    InvalidModuleMembership {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    DuplicateModule {
        module: Name,
    },
    NonCanonicalModuleOrder {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    CertificateEncodingMismatch {
        module: Name,
        actual: String,
    },
    CertificateLoader {
        source: Box<MachineStdReleaseLoaderError>,
    },
    ModuleArtifactHashMismatch {
        module: Name,
        field: &'static str,
        expected: Hash,
        actual: Hash,
    },
    ModuleArtifactCountMismatch {
        module: Name,
        field: &'static str,
        expected: u64,
        actual: u64,
    },
    SidecarHashMismatch {
        field: &'static str,
        expected: Hash,
        actual: Hash,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdAxiomPolicyError {
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    AxiomReportHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    InvalidModuleMembership {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    DuplicateModule {
        module: Name,
    },
    NonCanonicalModuleOrder {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    ModuleHashMismatch {
        module: Name,
        field: &'static str,
        expected: Hash,
        actual: Hash,
    },
    NonCanonicalAxiomOrder {
        module: Name,
        field: &'static str,
    },
    NonEmptyMvpAxiomList {
        module: Name,
        field: &'static str,
    },
    ModuleAxiomsMismatch {
        module: Name,
    },
    TransitiveAxiomsMismatch {
        module: Name,
    },
    AxiomRefProjectionFailed {
        module: Name,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdImportBundleError {
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    ImportBundlesHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    InvalidBundleMembership {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    DuplicateBundle {
        bundle_id: String,
    },
    NonCanonicalBundleOrder {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    DuplicateRootImport {
        bundle_id: String,
        key: Box<VerifiedImportKey>,
    },
    DuplicateImportClosure {
        bundle_id: String,
        key: Box<VerifiedImportKey>,
    },
    NonCanonicalRootImportOrder {
        bundle_id: String,
    },
    NonCanonicalImportClosureOrder {
        bundle_id: String,
    },
    RootImportsMismatch {
        bundle_id: String,
        expected: Vec<VerifiedImportKey>,
        actual: Vec<VerifiedImportKey>,
    },
    ImportClosureMismatch {
        bundle_id: String,
        expected: Vec<VerifiedImportKey>,
        actual: Vec<VerifiedImportKey>,
    },
    CertificateEncodingMismatch {
        bundle_id: String,
        module: Name,
        actual: String,
    },
    CertificateBytesMismatch {
        bundle_id: String,
        module: Name,
    },
    CertificateBytesHashMismatch {
        bundle_id: String,
        module: Name,
        expected: Hash,
        actual: Hash,
    },
    ImportKeyHashMismatch {
        bundle_id: String,
        module: Name,
    },
    MissingDependency {
        bundle_id: String,
        owner: Name,
        missing: Name,
    },
    NonEmptyMvpAllowAxioms {
        bundle_id: String,
    },
    DuplicateAllowAxiom {
        bundle_id: String,
        axiom: Box<MachineAxiomRefWire>,
    },
    NonCanonicalAllowAxiomOrder {
        bundle_id: String,
    },
    AllowAxiomsMismatch {
        bundle_id: String,
        expected: Vec<MachineAxiomRefWire>,
        actual: Vec<MachineAxiomRefWire>,
    },
    InvalidRecipeIdMapping {
        bundle_id: String,
        expected: &'static str,
        actual: String,
    },
    MissingRecipeSimpProfile {
        bundle_id: String,
        profile_id: &'static str,
    },
    MissingEqFamily {
        bundle_id: String,
    },
    MissingNatFamily {
        bundle_id: String,
    },
    RecipeFieldMismatch {
        bundle_id: String,
        field: &'static str,
    },
    RecipeSimpRulesMismatch {
        bundle_id: String,
        profile_id: String,
    },
    RecipeImportProjectionFailed {
        bundle_id: String,
        source: Box<ImportProjectionError>,
    },
    RecipeMachineApiValidationFailed {
        bundle_id: String,
        source: Box<MachineSessionCreateError>,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdRewriteProfileError {
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    RewriteProfilesHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    ProfileHashMismatch {
        profile_id: String,
        expected: Hash,
        actual: Hash,
    },
    InvalidProfileMembership {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    DuplicateProfile {
        profile_id: String,
    },
    NonCanonicalProfileOrder {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    ProfileFieldMismatch {
        profile_id: String,
        field: &'static str,
    },
    DuplicateDescriptor {
        profile_id: String,
    },
    NonCanonicalDescriptorOrder {
        profile_id: String,
    },
    DescriptorsMismatch {
        profile_id: String,
    },
    MissingEqFamily {
        profile_id: String,
    },
    RuleResolutionFailed {
        profile_id: String,
        name: Name,
    },
    RuleValidationFailed {
        profile_id: String,
        name: Name,
    },
    SimpSafeLintFailed {
        profile_id: String,
        name: Name,
    },
    NonEmptyMvpAxiomDependencies {
        profile_id: String,
        name: Name,
    },
    InvalidUniverseParam {
        profile_id: String,
        name: Name,
        param: String,
    },
    InvalidRuleTelescope {
        profile_id: String,
        name: Name,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdSimpProfileError {
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    SimpProfilesHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    ProfileHashMismatch {
        profile_id: String,
        expected: Hash,
        actual: Hash,
    },
    InvalidProfileMembership {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    DuplicateProfile {
        profile_id: String,
    },
    NonCanonicalProfileOrder {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    ProfileFieldMismatch {
        profile_id: String,
        field: &'static str,
    },
    DuplicateRule {
        profile_id: String,
    },
    NonCanonicalRuleOrder {
        profile_id: String,
    },
    RulesMismatch {
        profile_id: String,
    },
    MissingEqFamily {
        profile_id: String,
    },
    RuleResolutionFailed {
        profile_id: String,
        name: Name,
    },
    MissingSimpSafeDescriptor {
        profile_id: String,
        name: Name,
    },
    NonEmptyMvpAxiomDependencies {
        profile_id: String,
        name: Name,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdTheoremIndexError {
    IndexProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    TheoremIndexHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    InvalidEntryMembership {
        expected: Vec<MachineStdGlobalRef>,
        actual: Vec<MachineStdGlobalRef>,
    },
    DuplicateEntry {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalEntryOrder {
        expected: Vec<MachineStdGlobalRef>,
        actual: Vec<MachineStdGlobalRef>,
    },
    KindMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    UniverseParamsMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    StatementCoreHashMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    StatementHeadMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    ConstantsMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    ModesMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    AttributesMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    RewriteDescriptorsMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    AxiomDependenciesMismatch {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonNullProofTermSize {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalModes {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalAttributes {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalConstants {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalAxiomDependencies {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalRewriteDescriptors {
        global_ref: Box<MachineStdGlobalRef>,
    },
    InvalidRenderableName {
        module: Name,
        name: Name,
    },
    InvalidUniverseParam {
        module: Name,
        name: Name,
    },
    DuplicateUniverseParam {
        module: Name,
        name: Name,
        param: String,
    },
    InvalidGlobalRef {
        module: Name,
    },
    InvalidTermRef {
        module: Name,
    },
    InvalidExportKind {
        module: Name,
        name: Name,
    },
    AxiomRefProjectionFailed {
        module: Name,
    },
    ProfileMetadataMismatch {
        profile_id: String,
        name: Name,
    },
    ProfileSourceMissing {
        global_ref: Box<MachineStdGlobalRef>,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Debug)]
pub enum MachineStdPromptMetadataError {
    MetadataProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    LibraryProfileMismatch {
        expected: &'static str,
        actual: String,
    },
    PromptMetadataHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    DuplicateEntry {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalEntryOrder {
        expected: Vec<MachineStdGlobalRef>,
        actual: Vec<MachineStdGlobalRef>,
    },
    StaleGlobalRef {
        global_ref: Box<MachineStdGlobalRef>,
    },
    NonCanonicalTagOrder {
        global_ref: Box<MachineStdGlobalRef>,
    },
    DuplicateTag {
        global_ref: Box<MachineStdGlobalRef>,
        tag: String,
    },
    UnknownTag {
        global_ref: Box<MachineStdGlobalRef>,
        tag: String,
    },
    InvalidCandidateKind {
        global_ref: Box<MachineStdGlobalRef>,
        candidate_kind: String,
    },
    UnknownImportBundle {
        global_ref: Box<MachineStdGlobalRef>,
        imports_bundle_id: String,
    },
    CanonicalBytes {
        source: MachineStdCanonicalBytesError,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineStdCanonicalBytesError {
    InvalidName {
        name: Name,
        source: Box<MachineWireGrammarError>,
    },
    InvalidCoreGlobalRef {
        module: Name,
        name: Name,
    },
}

#[derive(Debug)]
pub enum MachineStdReleaseLoaderError {
    InvalidModuleMembership {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    DuplicateModule {
        module: Name,
    },
    NonCanonicalModuleOrder {
        expected: Vec<Name>,
        actual: Vec<Name>,
    },
    FixedPathMismatch {
        module: Name,
        expected: String,
        actual: String,
    },
    InvalidLocatorPath {
        path: String,
        reason: MachineStdLocatorPathError,
    },
    InvalidPackageRoot {
        path: PathBuf,
        source: io::Error,
    },
    MissingCertificateFile {
        module: Name,
        path: PathBuf,
        source: io::Error,
    },
    ReadCertificateFile {
        module: Name,
        path: PathBuf,
        source: io::Error,
    },
    SymlinkEscape {
        module: Name,
        path: PathBuf,
        resolved: PathBuf,
        package_root: PathBuf,
    },
    DecodeFailed {
        module: Name,
        source: Box<CertError>,
    },
    ModuleNameMismatch {
        expected: Name,
        actual: Name,
    },
    MissingImportCertificateHash {
        owner: Name,
        imported_module: Name,
    },
    UnresolvedImport {
        owner: Name,
        imported_module: Name,
    },
    ImportHashMismatch {
        owner: Name,
        imported_module: Name,
    },
    ImportCycle {
        module: Name,
    },
    InvalidCanonicalModuleName {
        module: Name,
        source: Box<MachineWireGrammarError>,
    },
    VerifyFailed {
        module: Name,
        source: Box<CertError>,
    },
    InvalidStdAxiomPolicy(MachineStdAxiomPolicyError),
    VerifiedIdentityMismatch {
        module: Name,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineStdLocatorPathError {
    Empty,
    Absolute,
    Backslash,
    TrailingSlash,
    DuplicateSlash,
    DotComponent,
    ParentComponent,
}

#[derive(Clone, Debug)]
struct DecodedStdModule {
    locator: MachineStdModuleLocator,
    resolved_path: PathBuf,
    certificate_bytes: Vec<u8>,
    certificate_bytes_hash: Hash,
    cert: ModuleCert,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CertificateKey {
    module: Name,
    export_hash: Hash,
    certificate_hash: Hash,
}

pub fn machine_std_mvp_module_locators() -> Vec<MachineStdModuleLocator> {
    vec![
        MachineStdModuleLocator::new(Name::from_dotted("Std.Nat"), STD_NAT_PATH),
        MachineStdModuleLocator::new(Name::from_dotted("Std.List"), STD_LIST_PATH),
        MachineStdModuleLocator::new(Name::from_dotted("Std.Logic"), STD_LOGIC_PATH),
        MachineStdModuleLocator::new(
            Name::from_dotted("Std.Algebra.Basic"),
            STD_ALGEBRA_BASIC_PATH,
        ),
    ]
}

pub fn machine_std_mvp_source_package_root() -> &'static str {
    STD_SOURCE_PACKAGE_ROOT
}

pub fn machine_std_mvp_source_package_layout() -> Vec<MachineStdSourcePackageEntry> {
    vec![
        MachineStdSourcePackageEntry::new(
            Name::from_dotted("Std.Logic"),
            STD_LOGIC_SOURCE_PATH,
            STD_LOGIC_PATH,
        ),
        MachineStdSourcePackageEntry::new(
            Name::from_dotted("Std.Nat"),
            STD_NAT_SOURCE_PATH,
            STD_NAT_PATH,
        ),
        MachineStdSourcePackageEntry::new(
            Name::from_dotted("Std.List"),
            STD_LIST_SOURCE_PATH,
            STD_LIST_PATH,
        ),
        MachineStdSourcePackageEntry::new(
            Name::from_dotted("Std.Algebra.Basic"),
            STD_ALGEBRA_BASIC_SOURCE_PATH,
            STD_ALGEBRA_BASIC_PATH,
        ),
    ]
}

/// Build the deterministic core certificate for a legacy `npa-std` fixture module.
///
/// SRA-02 uses the legacy Human/frontend compatibility modules
/// `Std.Logic.Eq` and `Std.Nat.Basic` as a two-module package fixture while the
/// Phase 6 MVP release shape remains `Std.Logic`, `Std.Nat`, `Std.List`, and
/// `Std.Algebra.Basic`. This helper exposes only the legacy fixture builders;
/// it does not read package manifests, source files, registries, or network
/// state.
pub fn build_legacy_std_package_module_cert(
    module: &Name,
    imports: &[VerifiedModule],
) -> Option<Result<ModuleCert, CertError>> {
    let core = match module.as_dotted().as_str() {
        "Std.Logic.Eq" => legacy_std_logic_eq_core_module(),
        "Std.Nat.Basic" => legacy_std_nat_basic_core_module(),
        _ => return None,
    };
    Some(build_module_cert(core, imports))
}

fn legacy_std_logic_eq_core_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Logic.Eq"),
        declarations: vec![Decl::Inductive {
            name: "Eq".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(Level::param("u")),
                Expr::pi(
                    "lhs",
                    Expr::bvar(0),
                    Expr::pi("rhs", Expr::bvar(1), Expr::sort(Level::zero())),
                ),
            ),
            data: Box::new(eq_inductive()),
        }],
    }
}

fn legacy_std_nat_basic_core_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Nat.Basic"),
        declarations: vec![Decl::Inductive {
            name: "Nat".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::sort(type0()),
            data: Box::new(nat_inductive()),
        }],
    }
}

pub fn load_machine_std_mvp_certificates(
    package_root: impl AsRef<Path>,
) -> Result<MachineStdLoadedRelease, MachineStdReleaseLoaderError> {
    load_machine_std_certificates_from_locators(package_root, &machine_std_mvp_module_locators())
}

pub fn load_machine_std_certificates_from_locators(
    package_root: impl AsRef<Path>,
    locators: &[MachineStdModuleLocator],
) -> Result<MachineStdLoadedRelease, MachineStdReleaseLoaderError> {
    validate_machine_std_mvp_locators(locators)?;
    let package_root = canonical_package_root(package_root.as_ref())?;
    let decoded = read_and_decode_std_modules(&package_root, locators)?;
    validate_import_graph(&decoded)?;
    let verification_order = topological_verification_order(&decoded)?;
    verify_decoded_modules(
        decoded,
        verification_order,
        high_trust_policy_allowing_std_mvp_axioms(),
    )
    .and_then(|loaded| {
        validate_loaded_mvp_axiom_policy(&loaded)?;
        Ok(loaded)
    })
}

pub fn load_machine_std_mvp_release(
    package_root: impl AsRef<Path>,
) -> Result<MachineStdValidatedRelease, MachineStdReleaseArtifactError> {
    let root = package_root.as_ref();
    let release_json = read_std_artifact_json(
        root,
        STD_MACHINE_RELEASE_JSON_PATH,
        MachineStdArtifactKind::LibraryRelease,
    )?;
    let import_bundles_json = read_std_artifact_json(
        root,
        STD_MACHINE_IMPORT_BUNDLES_JSON_PATH,
        MachineStdArtifactKind::ImportBundles,
    )?;
    let theorem_index_json = read_std_artifact_json(
        root,
        STD_MACHINE_THEOREM_INDEX_JSON_PATH,
        MachineStdArtifactKind::TheoremIndex,
    )?;
    let rewrite_profiles_json = read_std_artifact_json(
        root,
        STD_MACHINE_REWRITE_PROFILES_JSON_PATH,
        MachineStdArtifactKind::RewriteProfiles,
    )?;
    let simp_profiles_json = read_std_artifact_json(
        root,
        STD_MACHINE_SIMP_PROFILES_JSON_PATH,
        MachineStdArtifactKind::SimpProfiles,
    )?;
    let axiom_report_json = read_std_artifact_json(
        root,
        STD_MACHINE_AXIOM_REPORT_JSON_PATH,
        MachineStdArtifactKind::AxiomReport,
    )?;
    let prompt_metadata_json = read_optional_std_artifact_json(
        root,
        STD_MACHINE_PROMPT_METADATA_JSON_PATH,
        MachineStdArtifactKind::PromptMetadata,
    )?;
    let (validated, _) = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
        root,
        &release_json,
        MachineStdReleaseSidecarJson {
            import_bundles_json: &import_bundles_json,
            theorem_index_json: &theorem_index_json,
            rewrite_profiles_json: &rewrite_profiles_json,
            simp_profiles_json: &simp_profiles_json,
            axiom_report_json: &axiom_report_json,
            prompt_metadata_json: prompt_metadata_json.as_deref(),
        },
    )?;
    Ok(validated)
}

#[cfg(test)]
fn load_machine_std_mvp_release_from_json(
    package_root: impl AsRef<Path>,
    release_json: &str,
    axiom_report_json: &str,
) -> Result<MachineStdValidatedRelease, MachineStdReleaseArtifactError> {
    let (manifest, loaded, axiom_report) =
        load_machine_std_mvp_release_core(package_root, release_json, axiom_report_json)?;
    let import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    compare_release_sidecar_hash(
        "import_bundles_hash",
        manifest.import_bundles_hash,
        import_bundles.import_bundles_hash,
    )?;
    finish_machine_std_mvp_release(manifest, loaded, axiom_report, import_bundles)
}

#[cfg(test)]
fn load_machine_std_mvp_release_with_import_bundles_from_json(
    package_root: impl AsRef<Path>,
    release_json: &str,
    import_bundles_json: &str,
    axiom_report_json: &str,
) -> Result<MachineStdValidatedRelease, MachineStdReleaseArtifactError> {
    let import_bundles = parse_machine_std_import_bundle_set_json(import_bundles_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let (manifest, loaded, axiom_report) =
        load_machine_std_mvp_release_core(package_root, release_json, axiom_report_json)?;
    let expected_import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    validate_machine_std_mvp_import_bundle_set(&import_bundles, &expected_import_bundles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    compare_release_sidecar_hash(
        "import_bundles_hash",
        manifest.import_bundles_hash,
        import_bundles.import_bundles_hash,
    )?;
    finish_machine_std_mvp_release(manifest, loaded, axiom_report, import_bundles)
}

pub fn load_machine_std_mvp_release_with_sidecars_from_json(
    package_root: impl AsRef<Path>,
    release_json: &str,
    import_bundles_json: &str,
    theorem_index_json: &str,
    rewrite_profiles_json: &str,
    simp_profiles_json: &str,
    axiom_report_json: &str,
) -> Result<MachineStdValidatedRelease, MachineStdReleaseArtifactError> {
    load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
        package_root,
        release_json,
        MachineStdReleaseSidecarJson {
            import_bundles_json,
            theorem_index_json,
            rewrite_profiles_json,
            simp_profiles_json,
            axiom_report_json,
            prompt_metadata_json: None,
        },
    )
    .map(|(validated, _)| validated)
}

pub fn load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
    package_root: impl AsRef<Path>,
    release_json: &str,
    sidecars: MachineStdReleaseSidecarJson<'_>,
) -> Result<
    (
        MachineStdValidatedRelease,
        Option<MachineStdPromptMetadataSet>,
    ),
    MachineStdReleaseArtifactError,
> {
    let import_bundles = parse_machine_std_import_bundle_set_json(sidecars.import_bundles_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let theorem_index = parse_machine_std_theorem_index_json(sidecars.theorem_index_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let rewrite_profiles =
        parse_machine_std_rewrite_profile_set_json(sidecars.rewrite_profiles_json)
            .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let simp_profiles = parse_machine_std_simp_profile_set_json(sidecars.simp_profiles_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let prompt_metadata = sidecars
        .prompt_metadata_json
        .map(parse_machine_std_prompt_metadata_json)
        .transpose()
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let preflight_manifest = parse_machine_std_library_release_json(release_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    validate_machine_std_library_release_prepass(&preflight_manifest)
        .map_err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease)?;
    validate_machine_std_release_sidecar_self_hashes(
        &import_bundles,
        &theorem_index,
        &rewrite_profiles,
        &simp_profiles,
    )?;

    let (manifest, loaded, axiom_report) =
        load_machine_std_mvp_release_core(package_root, release_json, sidecars.axiom_report_json)?;

    let expected_rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded)
        .map_err(MachineStdReleaseArtifactError::InvalidStdRewriteProfile)?;
    validate_machine_std_mvp_rewrite_profile_set(&rewrite_profiles, &expected_rewrite_profiles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdRewriteProfile)?;

    let expected_simp_profiles =
        generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles)
            .map_err(MachineStdReleaseArtifactError::InvalidStdSimpProfile)?;
    validate_machine_std_mvp_simp_profile_set(
        &simp_profiles,
        &expected_simp_profiles,
        &rewrite_profiles,
    )
    .map_err(MachineStdReleaseArtifactError::InvalidStdSimpProfile)?;

    let expected_import_bundles =
        generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles)
            .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    validate_machine_std_mvp_import_bundle_set_shape(&import_bundles, &expected_import_bundles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    validate_machine_std_mvp_import_bundle_recipes(&loaded, &import_bundles, &simp_profiles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;
    validate_import_bundle_set_expected_hash(&import_bundles, &expected_import_bundles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdImportBundle)?;

    let expected_theorem_index =
        generate_machine_std_mvp_final_theorem_index(&loaded, &rewrite_profiles, &simp_profiles)
            .map_err(MachineStdReleaseArtifactError::InvalidStdTheoremIndex)?;
    validate_machine_std_mvp_final_theorem_index(&theorem_index, &expected_theorem_index)
        .map_err(MachineStdReleaseArtifactError::InvalidStdTheoremIndex)?;

    compare_release_sidecar_hash(
        "import_bundles_hash",
        manifest.import_bundles_hash,
        import_bundles.import_bundles_hash,
    )?;
    compare_release_sidecar_hash(
        "rewrite_profiles_hash",
        manifest.rewrite_profiles_hash,
        rewrite_profiles.rewrite_profiles_hash,
    )?;
    compare_release_sidecar_hash(
        "simp_profiles_hash",
        manifest.simp_profiles_hash,
        simp_profiles.simp_profiles_hash,
    )?;
    compare_release_sidecar_hash(
        "theorem_index_hash",
        manifest.theorem_index_hash,
        theorem_index.index_hash,
    )?;
    validate_machine_std_mvp_release_final_sidecar_counts(
        &manifest,
        &theorem_index,
        &simp_profiles,
        &rewrite_profiles,
    )?;
    validate_machine_std_mvp_optional_prompt_metadata(
        prompt_metadata.as_ref(),
        &theorem_index,
        &import_bundles,
    )
    .map_err(MachineStdReleaseArtifactError::InvalidStdPromptMetadata)?;

    let validated = finish_machine_std_mvp_release(manifest, loaded, axiom_report, import_bundles)?;
    Ok((validated, prompt_metadata))
}

fn validate_machine_std_release_sidecar_self_hashes(
    import_bundles: &MachineStdImportBundleSet,
    theorem_index: &MachineStdTheoremIndex,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<(), MachineStdReleaseArtifactError> {
    let import_bundles_hash =
        machine_std_import_bundle_set_hash(import_bundles).map_err(|source| {
            MachineStdReleaseArtifactError::InvalidStdImportBundle(
                MachineStdImportBundleError::CanonicalBytes { source },
            )
        })?;
    if import_bundles_hash != import_bundles.import_bundles_hash {
        return Err(MachineStdReleaseArtifactError::InvalidStdImportBundle(
            MachineStdImportBundleError::ImportBundlesHashMismatch {
                expected: import_bundles.import_bundles_hash,
                actual: import_bundles_hash,
            },
        ));
    }

    validate_rewrite_profile_hashes(rewrite_profiles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdRewriteProfile)?;
    let rewrite_profiles_hash =
        machine_std_rewrite_profile_set_hash(rewrite_profiles).map_err(|source| {
            MachineStdReleaseArtifactError::InvalidStdRewriteProfile(
                MachineStdRewriteProfileError::CanonicalBytes { source },
            )
        })?;
    if rewrite_profiles_hash != rewrite_profiles.rewrite_profiles_hash {
        return Err(MachineStdReleaseArtifactError::InvalidStdRewriteProfile(
            MachineStdRewriteProfileError::RewriteProfilesHashMismatch {
                expected: rewrite_profiles.rewrite_profiles_hash,
                actual: rewrite_profiles_hash,
            },
        ));
    }

    validate_simp_profile_hashes(simp_profiles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdSimpProfile)?;
    let simp_profiles_hash =
        machine_std_simp_profile_set_hash(simp_profiles).map_err(|source| {
            MachineStdReleaseArtifactError::InvalidStdSimpProfile(
                MachineStdSimpProfileError::CanonicalBytes { source },
            )
        })?;
    if simp_profiles_hash != simp_profiles.simp_profiles_hash {
        return Err(MachineStdReleaseArtifactError::InvalidStdSimpProfile(
            MachineStdSimpProfileError::SimpProfilesHashMismatch {
                expected: simp_profiles.simp_profiles_hash,
                actual: simp_profiles_hash,
            },
        ));
    }

    let theorem_index_hash = machine_std_theorem_index_hash(theorem_index).map_err(|source| {
        MachineStdReleaseArtifactError::InvalidStdTheoremIndex(
            MachineStdTheoremIndexError::CanonicalBytes { source },
        )
    })?;
    if theorem_index_hash != theorem_index.index_hash {
        return Err(MachineStdReleaseArtifactError::InvalidStdTheoremIndex(
            MachineStdTheoremIndexError::TheoremIndexHashMismatch {
                expected: theorem_index.index_hash,
                actual: theorem_index_hash,
            },
        ));
    }

    Ok(())
}

fn load_machine_std_mvp_release_core(
    package_root: impl AsRef<Path>,
    release_json: &str,
    axiom_report_json: &str,
) -> Result<
    (
        MachineStdLibraryRelease,
        MachineStdLoadedRelease,
        MachineStdAxiomReport,
    ),
    MachineStdReleaseArtifactError,
> {
    let manifest = parse_machine_std_library_release_json(release_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;
    let axiom_report = parse_machine_std_axiom_report_json(axiom_report_json)
        .map_err(MachineStdReleaseArtifactError::InvalidStdArtifactShape)?;

    validate_machine_std_library_release_prepass(&manifest)
        .map_err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease)?;

    let loaded = load_machine_std_mvp_certificates_for_manifest_validation(package_root.as_ref())
        .map_err(|source| {
        MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
            MachineStdLibraryReleaseError::CertificateLoader {
                source: Box::new(source),
            },
        )
    })?;
    validate_machine_std_library_release_against_certificates(&manifest, &loaded)
        .map_err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease)?;

    let actual_axiom_report_hash =
        machine_std_axiom_report_hash(&axiom_report).map_err(|source| {
            MachineStdReleaseArtifactError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::CanonicalBytes { source },
            )
        })?;
    if actual_axiom_report_hash != axiom_report.axiom_report_hash {
        return Err(MachineStdReleaseArtifactError::InvalidStdAxiomPolicy(
            MachineStdAxiomPolicyError::AxiomReportHashMismatch {
                expected: axiom_report.axiom_report_hash,
                actual: actual_axiom_report_hash,
            },
        ));
    }

    validate_machine_std_axiom_report(&manifest, &loaded, &axiom_report)
        .map_err(MachineStdReleaseArtifactError::InvalidStdAxiomPolicy)?;
    if manifest.axiom_report_hash != axiom_report.axiom_report_hash {
        compare_release_sidecar_hash(
            "axiom_report_hash",
            manifest.axiom_report_hash,
            axiom_report.axiom_report_hash,
        )?;
    }

    Ok((manifest, loaded, axiom_report))
}

fn finish_machine_std_mvp_release(
    manifest: MachineStdLibraryRelease,
    loaded: MachineStdLoadedRelease,
    axiom_report: MachineStdAxiomReport,
    import_bundles: MachineStdImportBundleSet,
) -> Result<MachineStdValidatedRelease, MachineStdReleaseArtifactError> {
    let std_library_release_hash =
        machine_std_library_release_hash(&manifest).map_err(|source| {
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::CanonicalBytes { source },
            )
        })?;

    Ok(MachineStdValidatedRelease {
        manifest,
        loaded,
        axiom_report,
        import_bundles,
        std_library_release_hash,
    })
}

fn compare_release_sidecar_hash(
    field: &'static str,
    expected: Hash,
    actual: Hash,
) -> Result<(), MachineStdReleaseArtifactError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
            MachineStdLibraryReleaseError::SidecarHashMismatch {
                field,
                expected,
                actual,
            },
        ))
    }
}

pub fn audit_machine_std_mvp_validated_release(
    validated: &MachineStdValidatedRelease,
    theorem_index: &MachineStdTheoremIndex,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    simp_profiles: &MachineStdSimpProfileSet,
    prompt_metadata: Option<&MachineStdPromptMetadataSet>,
) -> Result<MachineStdAuditReport, MachineStdAuditError> {
    let actual_release_hash = machine_std_library_release_hash(&validated.manifest)
        .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
    if actual_release_hash != validated.std_library_release_hash {
        return Err(MachineStdAuditError::ReleaseHashMismatch {
            expected: actual_release_hash,
            actual: validated.std_library_release_hash,
        });
    }

    audit_machine_std_mvp_release_artifacts(
        &validated.manifest,
        &validated.loaded,
        MachineStdAuditArtifacts {
            import_bundles: &validated.import_bundles,
            theorem_index,
            rewrite_profiles,
            simp_profiles,
            axiom_report: &validated.axiom_report,
            prompt_metadata,
        },
    )
}

pub fn audit_machine_std_mvp_release_artifacts(
    manifest: &MachineStdLibraryRelease,
    loaded: &MachineStdLoadedRelease,
    artifacts: MachineStdAuditArtifacts<'_>,
) -> Result<MachineStdAuditReport, MachineStdAuditError> {
    let mut checks = Vec::new();
    validate_machine_std_library_release_prepass(manifest)
        .map_err(MachineStdAuditError::InvalidStdLibraryRelease)?;
    validate_machine_std_library_release_against_certificates(manifest, loaded)
        .map_err(MachineStdAuditError::InvalidStdLibraryRelease)?;
    let std_library_release_hash = machine_std_library_release_hash(manifest)
        .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
    let loaded_hash = machine_std_loaded_release_audit_hash(loaded)
        .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
    checks.push(machine_std_audit_check(
        "manifest.verifier-output",
        "release manifest module hashes and counts match verifier output",
        audit_evidence_hash(
            "manifest.verifier-output",
            &[std_library_release_hash, loaded_hash],
            &[manifest.modules.len() as u64],
        ),
    ));
    checks.push(machine_std_audit_check(
        "manifest.release-hash",
        "std_library_release_hash is recomputed from canonical release bytes",
        audit_evidence_hash("manifest.release-hash", &[std_library_release_hash], &[]),
    ));

    let axiom_report_hash = machine_std_axiom_report_hash(artifacts.axiom_report)
        .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
    if axiom_report_hash != artifacts.axiom_report.axiom_report_hash {
        return Err(MachineStdAuditError::InvalidStdAxiomPolicy(
            MachineStdAxiomPolicyError::AxiomReportHashMismatch {
                expected: artifacts.axiom_report.axiom_report_hash,
                actual: axiom_report_hash,
            },
        ));
    }
    validate_machine_std_axiom_report(manifest, loaded, artifacts.axiom_report)
        .map_err(MachineStdAuditError::InvalidStdAxiomPolicy)?;
    audit_compare_sidecar_hash(
        "axiom_report_hash",
        manifest.axiom_report_hash,
        artifacts.axiom_report.axiom_report_hash,
    )?;
    checks.push(machine_std_audit_check(
        "sidecar.axiom-report.hash",
        "axiom report self-hash and manifest-bound hash match verifier output",
        audit_evidence_hash(
            "sidecar.axiom-report.hash",
            &[manifest.axiom_report_hash, axiom_report_hash],
            &[artifacts.axiom_report.modules.len() as u64],
        ),
    ));

    let expected_rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(loaded)
        .map_err(MachineStdAuditError::InvalidStdRewriteProfile)?;
    validate_machine_std_mvp_rewrite_profile_set(
        artifacts.rewrite_profiles,
        &expected_rewrite_profiles,
    )
    .map_err(MachineStdAuditError::InvalidStdRewriteProfile)?;
    audit_compare_sidecar_hash(
        "rewrite_profiles_hash",
        manifest.rewrite_profiles_hash,
        artifacts.rewrite_profiles.rewrite_profiles_hash,
    )?;
    checks.push(machine_std_audit_check(
        "sidecar.rewrite-profiles.hash",
        "rewrite profiles self-hash and manifest-bound hash match verifier-derived profiles",
        audit_evidence_hash(
            "sidecar.rewrite-profiles.hash",
            &[
                manifest.rewrite_profiles_hash,
                artifacts.rewrite_profiles.rewrite_profiles_hash,
                expected_rewrite_profiles.rewrite_profiles_hash,
            ],
            &[artifacts.rewrite_profiles.profiles.len() as u64],
        ),
    ));

    let expected_simp_profiles =
        generate_machine_std_mvp_simp_profile_set(loaded, artifacts.rewrite_profiles)
            .map_err(MachineStdAuditError::InvalidStdSimpProfile)?;
    validate_machine_std_mvp_simp_profile_set(
        artifacts.simp_profiles,
        &expected_simp_profiles,
        artifacts.rewrite_profiles,
    )
    .map_err(MachineStdAuditError::InvalidStdSimpProfile)?;
    audit_compare_sidecar_hash(
        "simp_profiles_hash",
        manifest.simp_profiles_hash,
        artifacts.simp_profiles.simp_profiles_hash,
    )?;
    checks.push(machine_std_audit_check(
        "sidecar.simp-profiles.hash",
        "simp profiles self-hash and manifest-bound hash match verifier-derived profiles",
        audit_evidence_hash(
            "sidecar.simp-profiles.hash",
            &[
                manifest.simp_profiles_hash,
                artifacts.simp_profiles.simp_profiles_hash,
                expected_simp_profiles.simp_profiles_hash,
            ],
            &[artifacts.simp_profiles.profiles.len() as u64],
        ),
    ));

    validate_audit_bundle_allow_axioms(loaded, artifacts.import_bundles)?;
    let expected_import_bundles =
        generate_machine_std_mvp_final_import_bundle_set(loaded, artifacts.simp_profiles)
            .map_err(MachineStdAuditError::InvalidStdImportBundle)?;
    validate_machine_std_mvp_import_bundle_set_shape(
        artifacts.import_bundles,
        &expected_import_bundles,
    )
    .map_err(MachineStdAuditError::InvalidStdImportBundle)?;
    validate_machine_std_mvp_import_bundle_recipes(
        loaded,
        artifacts.import_bundles,
        artifacts.simp_profiles,
    )
    .map_err(MachineStdAuditError::InvalidStdImportBundle)?;
    validate_import_bundle_set_expected_hash(artifacts.import_bundles, &expected_import_bundles)
        .map_err(MachineStdAuditError::InvalidStdImportBundle)?;
    audit_compare_sidecar_hash(
        "import_bundles_hash",
        manifest.import_bundles_hash,
        artifacts.import_bundles.import_bundles_hash,
    )?;
    checks.push(machine_std_audit_check(
        "sidecar.import-bundles.hash",
        "import bundles self-hash and manifest-bound hash match minimal verifier closure",
        audit_evidence_hash(
            "sidecar.import-bundles.hash",
            &[
                manifest.import_bundles_hash,
                artifacts.import_bundles.import_bundles_hash,
                expected_import_bundles.import_bundles_hash,
            ],
            &[artifacts.import_bundles.bundles.len() as u64],
        ),
    ));

    let expected_theorem_index = generate_machine_std_mvp_final_theorem_index(
        loaded,
        artifacts.rewrite_profiles,
        artifacts.simp_profiles,
    )
    .map_err(MachineStdAuditError::InvalidStdTheoremIndex)?;
    validate_machine_std_mvp_final_theorem_index(artifacts.theorem_index, &expected_theorem_index)
        .map_err(MachineStdAuditError::InvalidStdTheoremIndex)?;
    audit_compare_sidecar_hash(
        "theorem_index_hash",
        manifest.theorem_index_hash,
        artifacts.theorem_index.index_hash,
    )?;
    validate_machine_std_mvp_release_final_sidecar_counts(
        manifest,
        artifacts.theorem_index,
        artifacts.simp_profiles,
        artifacts.rewrite_profiles,
    )
    .map_err(|source| match source {
        MachineStdReleaseArtifactError::InvalidStdLibraryRelease(source) => {
            MachineStdAuditError::InvalidStdLibraryRelease(source)
        }
        MachineStdReleaseArtifactError::InvalidStdTheoremIndex(source) => {
            MachineStdAuditError::InvalidStdTheoremIndex(source)
        }
        source => MachineStdAuditError::InvalidStdReleaseArtifact(source),
    })?;
    checks.push(machine_std_audit_check(
        "sidecar.theorem-index.hash",
        "theorem index self-hash and manifest-bound hash match verifier-derived entries",
        audit_evidence_hash(
            "sidecar.theorem-index.hash",
            &[
                manifest.theorem_index_hash,
                artifacts.theorem_index.index_hash,
                expected_theorem_index.index_hash,
            ],
            &[artifacts.theorem_index.entries.len() as u64],
        ),
    ));

    validate_audit_profile_targets(
        artifacts.theorem_index,
        artifacts.rewrite_profiles,
        artifacts.simp_profiles,
    )?;
    checks.push(machine_std_audit_check(
        "profiles.target-decl-interface-hash",
        "rewrite and simp profile targets resolve to matching theorem-index decl_interface_hash",
        audit_evidence_hash(
            "profiles.target-decl-interface-hash",
            &[
                artifacts.theorem_index.index_hash,
                artifacts.rewrite_profiles.rewrite_profiles_hash,
                artifacts.simp_profiles.simp_profiles_hash,
            ],
            &[
                rewrite_descriptor_count(artifacts.rewrite_profiles),
                simp_rule_count(artifacts.simp_profiles),
            ],
        ),
    ));

    validate_audit_bundle_allow_axioms(loaded, artifacts.import_bundles)?;
    checks.push(machine_std_audit_check(
        "import-bundles.minimal-closure-and-axioms",
        "import bundles are minimal transitive closures and contain no custom allow_axioms",
        audit_evidence_hash(
            "import-bundles.minimal-closure-and-axioms",
            &[
                artifacts.import_bundles.import_bundles_hash,
                expected_import_bundles.import_bundles_hash,
            ],
            &[import_bundle_allow_axiom_count(artifacts.import_bundles)],
        ),
    ));

    validate_machine_std_mvp_optional_prompt_metadata(
        artifacts.prompt_metadata,
        artifacts.theorem_index,
        artifacts.import_bundles,
    )
    .map_err(MachineStdAuditError::InvalidStdPromptMetadata)?;
    let prompt_metadata_hash = artifacts
        .prompt_metadata
        .map(machine_std_prompt_metadata_hash)
        .transpose()
        .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
    checks.push(machine_std_audit_check(
        "optional.prompt-metadata.excluded-from-release-hash",
        "optional prompt metadata validates but is excluded from std_library_release_hash",
        audit_optional_prompt_metadata_evidence_hash(
            std_library_release_hash,
            prompt_metadata_hash,
        ),
    ));

    let mut report = MachineStdAuditReport {
        audit_profile_id: STD_AUDIT_PROFILE_ID.to_owned(),
        library_profile_id: manifest.library_profile_id.clone(),
        std_library_release_hash,
        manifest_hash: std_library_release_hash,
        prompt_metadata_hash,
        prompt_metadata_excluded_from_release_hash: true,
        checks,
        audit_report_hash: [0; 32],
    };
    report.audit_report_hash = machine_std_audit_report_hash(&report);
    Ok(report)
}

fn audit_compare_sidecar_hash(
    field: &'static str,
    expected: Hash,
    actual: Hash,
) -> Result<(), MachineStdAuditError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MachineStdAuditError::SidecarHashMismatch {
            field,
            expected,
            actual,
        })
    }
}

pub fn parse_machine_std_library_release_json(
    source: &str,
) -> Result<MachineStdLibraryRelease, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::LibraryRelease)?;
    parse_library_release_value(doc.root(), "$")
}

pub fn parse_machine_std_axiom_report_json(
    source: &str,
) -> Result<MachineStdAxiomReport, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::AxiomReport)?;
    parse_axiom_report_value(doc.root(), "$")
}

pub fn parse_machine_std_import_bundle_set_json(
    source: &str,
) -> Result<MachineStdImportBundleSet, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::ImportBundles)?;
    parse_import_bundle_set_value(doc.root(), "$")
}

pub fn parse_machine_std_theorem_index_json(
    source: &str,
) -> Result<MachineStdTheoremIndex, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::TheoremIndex)?;
    parse_theorem_index_value(doc.root(), "$")
}

pub fn parse_machine_std_rewrite_profile_set_json(
    source: &str,
) -> Result<MachineStdRewriteProfileSet, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::RewriteProfiles)?;
    parse_rewrite_profile_set_value(doc.root(), "$")
}

pub fn parse_machine_std_simp_profile_set_json(
    source: &str,
) -> Result<MachineStdSimpProfileSet, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::SimpProfiles)?;
    parse_simp_profile_set_value(doc.root(), "$")
}

pub fn parse_machine_std_prompt_metadata_json(
    source: &str,
) -> Result<MachineStdPromptMetadataSet, MachineStdArtifactShapeError> {
    let doc = parse_std_json(source, MachineStdArtifactKind::PromptMetadata)?;
    parse_prompt_metadata_set_value(doc.root(), "$")
}

pub fn machine_std_module_artifact_canonical_bytes(
    artifact: &MachineStdModuleArtifact,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_MODULE_ARTIFACT_TAG);
    encode_name(&mut out, &artifact.module)?;
    encode_hash(&mut out, &artifact.expected_export_hash);
    encode_hash(&mut out, &artifact.expected_certificate_hash);
    encode_string(&mut out, &artifact.certificate_encoding);
    encode_hash(&mut out, &artifact.certificate_bytes_hash);
    encode_hash(&mut out, &artifact.axiom_report_hash);
    encode_uvar(&mut out, artifact.public_export_count);
    encode_uvar(&mut out, artifact.theorem_index_entry_count);
    encode_uvar(&mut out, artifact.simp_rule_count);
    Ok(out)
}

pub fn machine_std_library_release_canonical_bytes(
    release: &MachineStdLibraryRelease,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_LIBRARY_RELEASE_TAG);
    encode_string(&mut out, &release.protocol_version);
    encode_string(&mut out, &release.library_profile_id);
    encode_string(&mut out, &release.core_spec_id);
    encode_string(&mut out, &release.kernel_semantics_profile_id);
    encode_uvar(&mut out, release.modules.len() as u64);
    for module in &release.modules {
        out.extend(machine_std_module_artifact_canonical_bytes(module)?);
    }
    encode_hash(&mut out, &release.import_bundles_hash);
    encode_hash(&mut out, &release.theorem_index_hash);
    encode_hash(&mut out, &release.simp_profiles_hash);
    encode_hash(&mut out, &release.rewrite_profiles_hash);
    encode_hash(&mut out, &release.axiom_report_hash);
    Ok(out)
}

pub fn machine_std_library_release_hash(
    release: &MachineStdLibraryRelease,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_library_release_canonical_bytes(
        release,
    )?))
}

pub fn machine_std_tactic_options_recipe_canonical_bytes(
    recipe: &MachineStdTacticOptionsRecipe,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_TACTIC_OPTIONS_RECIPE_TAG);
    encode_string(&mut out, &recipe.recipe_id);
    out.extend(machine_std_kernel_check_profile_canonical_bytes(
        &recipe.kernel_check_profile,
    ));
    encode_uvar(&mut out, recipe.simp_rules.len() as u64);
    for rule in &recipe.simp_rules {
        encode_simp_rule_ref(&mut out, rule)?;
    }
    encode_option_eq_family(&mut out, recipe.eq_family.as_ref())?;
    encode_option_nat_family(&mut out, recipe.nat_family.as_ref())?;
    encode_uvar(&mut out, recipe.max_simp_rewrite_steps);
    encode_uvar(&mut out, recipe.max_open_goals);
    encode_uvar(&mut out, recipe.max_metas);
    Ok(out)
}

pub fn machine_std_import_bundle_canonical_bytes(
    bundle: &MachineStdImportBundle,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_IMPORT_BUNDLE_TAG);
    encode_string(&mut out, &bundle.bundle_id);
    encode_uvar(&mut out, bundle.root_imports.len() as u64);
    for key in &bundle.root_imports {
        encode_verified_import_key(&mut out, key)?;
    }
    encode_uvar(&mut out, bundle.import_closure.len() as u64);
    for certificate in &bundle.import_closure {
        encode_import_certificate_key(&mut out, certificate)?;
        encode_hash(&mut out, &sha256(&certificate.certificate_bytes));
    }
    encode_uvar(&mut out, bundle.allow_axioms.len() as u64);
    for axiom in &bundle.allow_axioms {
        out.extend(encode_machine_axiom_ref_wire(axiom));
    }
    out.extend(machine_std_tactic_options_recipe_canonical_bytes(
        &bundle.recommended_tactic_options,
    )?);
    Ok(out)
}

pub fn machine_std_import_bundle_hash(
    bundle: &MachineStdImportBundle,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_import_bundle_canonical_bytes(bundle)?))
}

pub fn machine_std_import_bundle_set_canonical_bytes(
    bundle_set: &MachineStdImportBundleSet,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_IMPORT_BUNDLE_SET_TAG);
    encode_string(&mut out, &bundle_set.library_profile_id);
    encode_uvar(&mut out, bundle_set.bundles.len() as u64);
    for bundle in &bundle_set.bundles {
        encode_hash(&mut out, &machine_std_import_bundle_hash(bundle)?);
    }
    Ok(out)
}

pub fn machine_std_import_bundle_set_hash(
    bundle_set: &MachineStdImportBundleSet,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_import_bundle_set_canonical_bytes(
        bundle_set,
    )?))
}

pub fn machine_std_global_ref_canonical_bytes(
    global_ref: &MachineStdGlobalRef,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_GLOBAL_REF_TAG);
    encode_name(&mut out, &global_ref.module)?;
    encode_name(&mut out, &global_ref.name)?;
    encode_hash(&mut out, &global_ref.export_hash);
    encode_hash(&mut out, &global_ref.certificate_hash);
    encode_hash(&mut out, &global_ref.decl_interface_hash);
    Ok(out)
}

pub fn machine_std_global_ref_view_canonical_bytes(
    view: &MachineStdGlobalRefView,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_GLOBAL_REF_VIEW_TAG);
    match view {
        MachineStdGlobalRefView::Decl {
            module,
            name,
            export_hash,
            certificate_hash,
            decl_interface_hash,
            public_export,
        } => {
            out.push(0x00);
            encode_name(&mut out, module)?;
            encode_name(&mut out, name)?;
            encode_hash(&mut out, export_hash);
            encode_hash(&mut out, certificate_hash);
            encode_hash(&mut out, decl_interface_hash);
            encode_bool(&mut out, *public_export);
        }
        MachineStdGlobalRefView::Generated {
            module,
            parent_name,
            name,
            export_hash,
            certificate_hash,
            parent_decl_interface_hash,
            decl_interface_hash,
            public_export,
        } => {
            out.push(0x01);
            encode_name(&mut out, module)?;
            encode_name(&mut out, parent_name)?;
            encode_name(&mut out, name)?;
            encode_hash(&mut out, export_hash);
            encode_hash(&mut out, certificate_hash);
            encode_hash(&mut out, parent_decl_interface_hash);
            encode_hash(&mut out, decl_interface_hash);
            encode_bool(&mut out, *public_export);
        }
    }
    Ok(out)
}

pub fn machine_std_rule_telescope_canonical_bytes(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    rule: &ResolvedSimpRule,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_RULE_TELESCOPE_TAG);
    encode_uvar(&mut out, rule.universe_params.len() as u64);
    for param in &rule.universe_params {
        encode_string(&mut out, param);
    }
    encode_uvar(&mut out, rule.rule_telescope.len() as u64);
    for (index, param) in rule.rule_telescope.iter().enumerate() {
        encode_uvar(&mut out, index as u64);
        encode_hash(
            &mut out,
            &std_library_core_expr_hash(loaded, owner, &param.ty)?,
        );
    }
    Ok(out)
}

pub fn machine_std_rule_telescope_hash(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    rule: &ResolvedSimpRule,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_rule_telescope_canonical_bytes(
        loaded, owner, rule,
    )?))
}

pub fn machine_std_rewrite_descriptor_canonical_bytes(
    descriptor: &MachineStdRewriteDescriptor,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    out.extend(machine_std_global_ref_canonical_bytes(&descriptor.source)?);
    encode_rewrite_direction(&mut out, descriptor.direction);
    out.push(rewrite_safety_byte(descriptor.safety));
    encode_hash(&mut out, &descriptor.lhs_core_hash);
    encode_hash(&mut out, &descriptor.rhs_core_hash);
    encode_hash(&mut out, &descriptor.rule_telescope_hash);
    Ok(out)
}

pub fn machine_std_rewrite_profile_canonical_bytes(
    profile: &MachineStdRewriteProfile,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_REWRITE_PROFILE_TAG);
    encode_string(&mut out, &profile.profile_id);
    encode_string(&mut out, &profile.required_import_bundle_id);
    out.extend(machine_std_kernel_check_profile_canonical_bytes(
        &profile.kernel_check_profile,
    ));
    encode_option_eq_family(&mut out, profile.eq_family.as_ref())?;
    encode_uvar(&mut out, profile.descriptors.len() as u64);
    for descriptor in &profile.descriptors {
        out.extend(machine_std_rewrite_descriptor_canonical_bytes(descriptor)?);
    }
    Ok(out)
}

pub fn machine_std_rewrite_profile_hash(
    profile: &MachineStdRewriteProfile,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_rewrite_profile_canonical_bytes(
        profile,
    )?))
}

pub fn machine_std_rewrite_profile_set_canonical_bytes(
    profile_set: &MachineStdRewriteProfileSet,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_REWRITE_PROFILE_SET_TAG);
    encode_string(&mut out, &profile_set.library_profile_id);
    encode_uvar(&mut out, profile_set.profiles.len() as u64);
    for profile in &profile_set.profiles {
        encode_hash(&mut out, &machine_std_rewrite_profile_hash(profile)?);
    }
    Ok(out)
}

pub fn machine_std_rewrite_profile_set_hash(
    profile_set: &MachineStdRewriteProfileSet,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_rewrite_profile_set_canonical_bytes(
        profile_set,
    )?))
}

pub fn machine_std_simp_profile_canonical_bytes(
    profile: &MachineStdSimpProfile,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_SIMP_PROFILE_TAG);
    encode_string(&mut out, &profile.profile_id);
    encode_string(&mut out, &profile.required_import_bundle_id);
    out.extend(machine_std_kernel_check_profile_canonical_bytes(
        &profile.kernel_check_profile,
    ));
    encode_option_eq_family(&mut out, profile.eq_family.as_ref())?;
    encode_uvar(&mut out, profile.rules.len() as u64);
    for rule in &profile.rules {
        encode_simp_rule_ref(&mut out, rule)?;
    }
    Ok(out)
}

pub fn machine_std_simp_profile_hash(
    profile: &MachineStdSimpProfile,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_simp_profile_canonical_bytes(profile)?))
}

pub fn machine_std_simp_profile_set_canonical_bytes(
    profile_set: &MachineStdSimpProfileSet,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_SIMP_PROFILE_SET_TAG);
    encode_string(&mut out, &profile_set.library_profile_id);
    encode_uvar(&mut out, profile_set.profiles.len() as u64);
    for profile in &profile_set.profiles {
        encode_hash(&mut out, &machine_std_simp_profile_hash(profile)?);
    }
    Ok(out)
}

pub fn machine_std_simp_profile_set_hash(
    profile_set: &MachineStdSimpProfileSet,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_simp_profile_set_canonical_bytes(
        profile_set,
    )?))
}

pub fn machine_std_prompt_example_canonical_bytes(example: &MachineStdPromptExample) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_PROMPT_EXAMPLE_TAG);
    encode_hash(&mut out, &example.goal_core_hash);
    encode_string(&mut out, &example.imports_bundle_id);
    encode_string(&mut out, &example.candidate_kind);
    encode_string(&mut out, &example.display);
    out
}

pub fn machine_std_prompt_metadata_canonical_bytes(
    metadata: &MachineStdPromptMetadata,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_PROMPT_METADATA_TAG);
    out.extend(machine_std_global_ref_canonical_bytes(
        &metadata.global_ref,
    )?);
    encode_option_string(&mut out, metadata.short_doc.as_deref());
    encode_uvar(&mut out, metadata.examples.len() as u64);
    for example in &metadata.examples {
        out.extend(machine_std_prompt_example_canonical_bytes(example));
    }
    encode_uvar(&mut out, metadata.tags.len() as u64);
    for tag in &metadata.tags {
        encode_string(&mut out, tag);
    }
    Ok(out)
}

pub fn machine_std_prompt_metadata_set_canonical_bytes(
    metadata_set: &MachineStdPromptMetadataSet,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_PROMPT_METADATA_SET_TAG);
    encode_string(&mut out, &metadata_set.metadata_profile_id);
    encode_string(&mut out, &metadata_set.library_profile_id);
    encode_uvar(&mut out, metadata_set.entries.len() as u64);
    for metadata in &metadata_set.entries {
        out.extend(machine_std_prompt_metadata_canonical_bytes(metadata)?);
    }
    Ok(out)
}

pub fn machine_std_prompt_metadata_hash(
    metadata_set: &MachineStdPromptMetadataSet,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_prompt_metadata_set_canonical_bytes(
        metadata_set,
    )?))
}

pub fn machine_std_theorem_entry_canonical_bytes(
    entry: &MachineStdTheoremEntry,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    out.extend(machine_std_global_ref_canonical_bytes(&entry.global_ref)?);
    out.push(theorem_kind_byte(entry.kind));
    encode_uvar(&mut out, entry.universe_params.len() as u64);
    for param in &entry.universe_params {
        encode_string(&mut out, param);
    }
    encode_hash(&mut out, &entry.statement_core_hash);
    encode_option_global_ref_view(&mut out, entry.statement_head.as_ref())?;
    encode_uvar(&mut out, entry.constants.len() as u64);
    for constant in &entry.constants {
        out.extend(machine_std_global_ref_view_canonical_bytes(constant)?);
    }
    encode_uvar(&mut out, entry.modes.len() as u64);
    for mode in &entry.modes {
        out.push(theorem_mode_byte(*mode));
    }
    encode_uvar(&mut out, entry.attributes.len() as u64);
    for attribute in &entry.attributes {
        out.push(theorem_attribute_byte(*attribute));
    }
    encode_uvar(&mut out, entry.rewrite_descriptors.len() as u64);
    for descriptor in &entry.rewrite_descriptors {
        out.extend(machine_std_rewrite_descriptor_canonical_bytes(descriptor)?);
    }
    encode_uvar(&mut out, entry.axiom_dependencies.len() as u64);
    for axiom in &entry.axiom_dependencies {
        out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
    }
    encode_option_u64(&mut out, entry.proof_term_size);
    Ok(out)
}

pub fn machine_std_theorem_index_canonical_bytes(
    theorem_index: &MachineStdTheoremIndex,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_THEOREM_INDEX_TAG);
    encode_string(&mut out, &theorem_index.index_profile_id);
    encode_string(&mut out, &theorem_index.library_profile_id);
    encode_uvar(&mut out, theorem_index.entries.len() as u64);
    for entry in &theorem_index.entries {
        out.extend(machine_std_theorem_entry_canonical_bytes(entry)?);
    }
    Ok(out)
}

pub fn machine_std_theorem_index_hash(
    theorem_index: &MachineStdTheoremIndex,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_theorem_index_canonical_bytes(
        theorem_index,
    )?))
}

pub fn machine_std_axiom_ref_canonical_bytes(
    axiom: &MachineStdAxiomRef,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, MACHINE_API_AXIOM_REF_WIRE_TAG);
    out.push(0x00);
    encode_name(&mut out, &axiom.module)?;
    encode_name(&mut out, &axiom.name)?;
    encode_hash(&mut out, &axiom.export_hash);
    encode_hash(&mut out, &axiom.decl_interface_hash);
    Ok(out)
}

pub fn machine_std_axiom_report_canonical_bytes(
    report: &MachineStdAxiomReport,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_AXIOM_REPORT_TAG);
    encode_string(&mut out, &report.library_profile_id);
    encode_uvar(&mut out, report.modules.len() as u64);
    for module in &report.modules {
        encode_name(&mut out, &module.module)?;
        encode_hash(&mut out, &module.export_hash);
        encode_hash(&mut out, &module.certificate_hash);
        encode_uvar(&mut out, module.module_axioms.len() as u64);
        for axiom in &module.module_axioms {
            out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
        }
        encode_uvar(&mut out, module.transitive_axioms.len() as u64);
        for axiom in &module.transitive_axioms {
            out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
        }
    }
    Ok(out)
}

pub fn machine_std_axiom_report_hash(
    report: &MachineStdAxiomReport,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&machine_std_axiom_report_canonical_bytes(report)?))
}

pub fn machine_std_audit_check_canonical_bytes(check: &MachineStdAuditCheck) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_AUDIT_CHECK_TAG);
    encode_string(&mut out, &check.check_id);
    encode_string(&mut out, &check.subject);
    encode_bool(&mut out, check.passed);
    encode_hash(&mut out, &check.evidence_hash);
    out
}

pub fn machine_std_audit_report_canonical_bytes(report: &MachineStdAuditReport) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_AUDIT_REPORT_TAG);
    encode_string(&mut out, &report.audit_profile_id);
    encode_string(&mut out, &report.library_profile_id);
    encode_hash(&mut out, &report.std_library_release_hash);
    encode_hash(&mut out, &report.manifest_hash);
    encode_option_hash(&mut out, report.prompt_metadata_hash.as_ref());
    encode_bool(&mut out, report.prompt_metadata_excluded_from_release_hash);
    encode_uvar(&mut out, report.checks.len() as u64);
    for check in &report.checks {
        out.extend(machine_std_audit_check_canonical_bytes(check));
    }
    out
}

pub fn machine_std_audit_report_hash(report: &MachineStdAuditReport) -> Hash {
    sha256(&machine_std_audit_report_canonical_bytes(report))
}

fn machine_std_audit_check(
    check_id: &'static str,
    subject: &'static str,
    evidence_hash: Hash,
) -> MachineStdAuditCheck {
    MachineStdAuditCheck {
        check_id: check_id.to_owned(),
        subject: subject.to_owned(),
        passed: true,
        evidence_hash,
    }
}

fn audit_evidence_hash(tag: &str, hashes: &[Hash], counts: &[u64]) -> Hash {
    let mut out = Vec::new();
    encode_string(&mut out, tag);
    encode_uvar(&mut out, hashes.len() as u64);
    for hash in hashes {
        encode_hash(&mut out, hash);
    }
    encode_uvar(&mut out, counts.len() as u64);
    for count in counts {
        encode_uvar(&mut out, *count);
    }
    sha256(&out)
}

fn audit_optional_prompt_metadata_evidence_hash(
    std_library_release_hash: Hash,
    prompt_metadata_hash: Option<Hash>,
) -> Hash {
    let mut out = Vec::new();
    encode_string(
        &mut out,
        "optional.prompt-metadata.excluded-from-release-hash",
    );
    encode_hash(&mut out, &std_library_release_hash);
    encode_option_hash(&mut out, prompt_metadata_hash.as_ref());
    sha256(&out)
}

fn machine_std_loaded_release_audit_hash(
    loaded: &MachineStdLoadedRelease,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(
        &mut out,
        "npa.independent-checker.std-library-loaded-release.v1",
    );
    encode_uvar(&mut out, loaded.modules().len() as u64);
    for module in loaded.modules() {
        encode_name(&mut out, &module.module)?;
        encode_string(&mut out, &module.locator_path);
        encode_hash(&mut out, &module.certificate_bytes_hash);
        encode_hash(&mut out, &module.expected_export_hash);
        encode_hash(&mut out, &module.expected_certificate_hash);
        encode_hash(&mut out, &module.axiom_report_hash);
        encode_uvar(&mut out, module.verified_module.export_block().len() as u64);
        encode_uvar(
            &mut out,
            module
                .verified_module
                .export_block()
                .iter()
                .filter(|entry| matches!(entry.kind, ExportKind::Theorem | ExportKind::Axiom))
                .count() as u64,
        );
        encode_uvar(&mut out, module.imports.len() as u64);
        for import in &module.imports {
            encode_name(&mut out, &import.module)?;
            encode_hash(&mut out, &import.export_hash);
            encode_option_hash(&mut out, import.certificate_hash.as_ref());
        }
    }
    Ok(sha256(&out))
}

fn validate_audit_profile_targets(
    theorem_index: &MachineStdTheoremIndex,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<(), MachineStdAuditError> {
    let mut theorem_by_ref = BTreeMap::new();
    let mut theorem_by_rule_target = BTreeSet::new();
    for entry in &theorem_index.entries {
        let key = machine_std_global_ref_canonical_bytes(&entry.global_ref)
            .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
        theorem_by_ref.insert(key, entry);
        theorem_by_rule_target.insert((
            entry.global_ref.name.clone(),
            entry.global_ref.decl_interface_hash,
        ));
    }

    for profile in &rewrite_profiles.profiles {
        for descriptor in &profile.descriptors {
            let key = machine_std_global_ref_canonical_bytes(&descriptor.source)
                .map_err(|source| MachineStdAuditError::CanonicalBytes { source })?;
            if !theorem_by_ref.contains_key(&key) {
                return Err(MachineStdAuditError::ProfileTargetMismatch {
                    profile_id: profile.profile_id.clone(),
                    name: descriptor.source.name.clone(),
                });
            }
        }
    }

    for profile in &simp_profiles.profiles {
        for rule in &profile.rules {
            if !theorem_by_rule_target.contains(&(rule.name.clone(), rule.decl_interface_hash)) {
                return Err(MachineStdAuditError::ProfileTargetMismatch {
                    profile_id: profile.profile_id.clone(),
                    name: rule.name.clone(),
                });
            }
        }
    }

    Ok(())
}

fn validate_audit_bundle_allow_axioms(
    loaded: &MachineStdLoadedRelease,
    import_bundles: &MachineStdImportBundleSet,
) -> Result<(), MachineStdAuditError> {
    let allowed_eq_rec =
        std_logic_eq_rec_axiom_ref(loaded).map(|axiom| machine_std_axiom_ref_to_wire(&axiom));
    for bundle in &import_bundles.bundles {
        for axiom in &bundle.allow_axioms {
            if allowed_eq_rec.as_ref() != Some(axiom) {
                return Err(MachineStdAuditError::CustomAllowAxiom {
                    bundle_id: bundle.bundle_id.clone(),
                    axiom: Box::new(axiom.clone()),
                });
            }
        }
    }
    Ok(())
}

fn rewrite_descriptor_count(rewrite_profiles: &MachineStdRewriteProfileSet) -> u64 {
    rewrite_profiles
        .profiles
        .iter()
        .map(|profile| profile.descriptors.len() as u64)
        .sum()
}

fn simp_rule_count(simp_profiles: &MachineStdSimpProfileSet) -> u64 {
    simp_profiles
        .profiles
        .iter()
        .map(|profile| profile.rules.len() as u64)
        .sum()
}

fn import_bundle_allow_axiom_count(import_bundles: &MachineStdImportBundleSet) -> u64 {
    import_bundles
        .bundles
        .iter()
        .map(|bundle| bundle.allow_axioms.len() as u64)
        .sum()
}

pub fn validate_machine_std_mvp_locators(
    locators: &[MachineStdModuleLocator],
) -> Result<(), MachineStdReleaseLoaderError> {
    let expected = machine_std_mvp_module_locators();
    let expected_modules = expected
        .iter()
        .map(|locator| locator.module.clone())
        .collect::<Vec<_>>();
    let actual_modules = locators
        .iter()
        .map(|locator| locator.module.clone())
        .collect::<Vec<_>>();

    let mut seen = BTreeSet::new();
    for module in &actual_modules {
        if !seen.insert(module.clone()) {
            return Err(MachineStdReleaseLoaderError::DuplicateModule {
                module: module.clone(),
            });
        }
    }

    let expected_set = expected_modules.iter().cloned().collect::<BTreeSet<_>>();
    let actual_set = actual_modules.iter().cloned().collect::<BTreeSet<_>>();
    if actual_set != expected_set {
        return Err(MachineStdReleaseLoaderError::InvalidModuleMembership {
            expected: expected_modules,
            actual: actual_modules,
        });
    }
    if actual_modules != expected_modules {
        return Err(MachineStdReleaseLoaderError::NonCanonicalModuleOrder {
            expected: expected_modules,
            actual: actual_modules,
        });
    }

    for (locator, expected_locator) in locators.iter().zip(expected.iter()) {
        validate_machine_std_locator_path(&locator.relative_path).map_err(|reason| {
            MachineStdReleaseLoaderError::InvalidLocatorPath {
                path: locator.relative_path.clone(),
                reason,
            }
        })?;
        if locator.relative_path != expected_locator.relative_path {
            return Err(MachineStdReleaseLoaderError::FixedPathMismatch {
                module: locator.module.clone(),
                expected: expected_locator.relative_path.clone(),
                actual: locator.relative_path.clone(),
            });
        }
    }

    Ok(())
}

pub fn validate_machine_std_locator_path(path: &str) -> Result<(), MachineStdLocatorPathError> {
    if path.is_empty() {
        return Err(MachineStdLocatorPathError::Empty);
    }
    if path.starts_with('/') {
        return Err(MachineStdLocatorPathError::Absolute);
    }
    if path.contains('\\') {
        return Err(MachineStdLocatorPathError::Backslash);
    }
    if path.ends_with('/') {
        return Err(MachineStdLocatorPathError::TrailingSlash);
    }
    if path.contains("//") {
        return Err(MachineStdLocatorPathError::DuplicateSlash);
    }
    for component in path.split('/') {
        match component {
            "" => return Err(MachineStdLocatorPathError::Empty),
            "." => return Err(MachineStdLocatorPathError::DotComponent),
            ".." => return Err(MachineStdLocatorPathError::ParentComponent),
            _ => {}
        }
    }
    Ok(())
}

fn read_std_artifact_json(
    root: &Path,
    relative_path: &str,
    artifact: MachineStdArtifactKind,
) -> Result<String, MachineStdReleaseArtifactError> {
    let path = join_posix_relative_path(root, relative_path);
    fs::read_to_string(&path).map_err(|source| MachineStdReleaseArtifactError::ReadArtifact {
        artifact,
        path,
        source,
    })
}

fn read_optional_std_artifact_json(
    root: &Path,
    relative_path: &str,
    artifact: MachineStdArtifactKind,
) -> Result<Option<String>, MachineStdReleaseArtifactError> {
    let path = join_posix_relative_path(root, relative_path);
    match fs::read_to_string(&path) {
        Ok(source) => Ok(Some(source)),
        Err(source) if source.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(source) => Err(MachineStdReleaseArtifactError::ReadArtifact {
            artifact,
            path,
            source,
        }),
    }
}

fn load_machine_std_mvp_certificates_for_manifest_validation(
    package_root: &Path,
) -> Result<MachineStdLoadedRelease, MachineStdReleaseLoaderError> {
    let locators = machine_std_mvp_module_locators();
    validate_machine_std_mvp_locators(&locators)?;
    let package_root = canonical_package_root(package_root)?;
    let decoded = read_and_decode_std_modules(&package_root, &locators)?;
    validate_import_graph(&decoded)?;
    let verification_order = topological_verification_order(&decoded)?;
    let policy = high_trust_policy_allowing_decoded_axioms(&decoded);
    verify_decoded_modules(decoded, verification_order, policy)
}

fn high_trust_policy_allowing_decoded_axioms(
    decoded: &BTreeMap<Name, DecodedStdModule>,
) -> AxiomPolicy {
    let mut allowlisted_axioms = BTreeSet::new();
    for module in decoded.values() {
        allowlisted_axioms.extend(
            module
                .cert
                .name_table
                .iter()
                .filter(|name| name.is_canonical())
                .cloned(),
        );
    }
    AxiomPolicy {
        mode: TrustMode::HighTrust,
        allowlisted_axioms,
        deny_sorry: false,
        supported_core_features: BTreeSet::new(),
    }
}

fn high_trust_policy_allowing_std_mvp_axioms() -> AxiomPolicy {
    let mut allowlisted_axioms = BTreeSet::new();
    allowlisted_axioms.insert(Name::from_dotted("Eq.rec"));
    AxiomPolicy {
        mode: TrustMode::HighTrust,
        allowlisted_axioms,
        deny_sorry: true,
        supported_core_features: BTreeSet::new(),
    }
}

fn validate_machine_std_library_release_prepass(
    manifest: &MachineStdLibraryRelease,
) -> Result<(), MachineStdLibraryReleaseError> {
    validate_fixed_scalar(
        "protocol_version",
        STD_LIBRARY_PROTOCOL_VERSION,
        &manifest.protocol_version,
    )?;
    validate_fixed_scalar(
        "library_profile_id",
        STD_LIBRARY_PROFILE_ID,
        &manifest.library_profile_id,
    )?;
    validate_fixed_scalar("core_spec_id", STD_CORE_SPEC_ID, &manifest.core_spec_id)?;
    validate_fixed_scalar(
        "kernel_semantics_profile_id",
        STD_KERNEL_SEMANTICS_PROFILE_ID,
        &manifest.kernel_semantics_profile_id,
    )?;
    validate_manifest_module_membership(&manifest.modules)?;
    for module in &manifest.modules {
        if module.certificate_encoding != STD_CERTIFICATE_ENCODING {
            return Err(MachineStdLibraryReleaseError::CertificateEncodingMismatch {
                module: module.module.clone(),
                actual: module.certificate_encoding.clone(),
            });
        }
    }
    Ok(())
}

fn validate_fixed_scalar(
    field: &'static str,
    expected: &'static str,
    actual: &str,
) -> Result<(), MachineStdLibraryReleaseError> {
    if actual == expected {
        Ok(())
    } else {
        Err(MachineStdLibraryReleaseError::ScalarMismatch {
            field,
            expected,
            actual: actual.to_owned(),
        })
    }
}

fn validate_manifest_module_membership(
    modules: &[MachineStdModuleArtifact],
) -> Result<(), MachineStdLibraryReleaseError> {
    let expected = expected_mvp_modules();
    let actual = modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for module in &actual {
        if !seen.insert(module.clone()) {
            return Err(MachineStdLibraryReleaseError::DuplicateModule {
                module: module.clone(),
            });
        }
    }
    let expected_set = expected.iter().cloned().collect::<BTreeSet<_>>();
    let actual_set = actual.iter().cloned().collect::<BTreeSet<_>>();
    if expected_set != actual_set {
        return Err(MachineStdLibraryReleaseError::InvalidModuleMembership { expected, actual });
    }
    if expected != actual {
        return Err(MachineStdLibraryReleaseError::NonCanonicalModuleOrder { expected, actual });
    }
    Ok(())
}

fn validate_machine_std_library_release_against_certificates(
    manifest: &MachineStdLibraryRelease,
    loaded: &MachineStdLoadedRelease,
) -> Result<(), MachineStdLibraryReleaseError> {
    for artifact in &manifest.modules {
        let module = loaded
            .module(&artifact.module)
            .expect("manifest prepass checked MVP module membership");
        compare_module_hash(
            &artifact.module,
            "expected_export_hash",
            artifact.expected_export_hash,
            module.expected_export_hash,
        )?;
        compare_module_hash(
            &artifact.module,
            "expected_certificate_hash",
            artifact.expected_certificate_hash,
            module.expected_certificate_hash,
        )?;
        compare_module_hash(
            &artifact.module,
            "certificate_bytes_hash",
            artifact.certificate_bytes_hash,
            module.certificate_bytes_hash,
        )?;
        compare_module_hash(
            &artifact.module,
            "axiom_report_hash",
            artifact.axiom_report_hash,
            module.axiom_report_hash,
        )?;
        compare_module_count(
            &artifact.module,
            "public_export_count",
            artifact.public_export_count,
            module.verified_module.export_block().len() as u64,
        )?;
        compare_module_count(
            &artifact.module,
            "theorem_index_entry_count",
            artifact.theorem_index_entry_count,
            module
                .verified_module
                .export_block()
                .iter()
                .filter(|entry| matches!(entry.kind, ExportKind::Theorem | ExportKind::Axiom))
                .count() as u64,
        )?;
    }
    Ok(())
}

fn compare_module_hash(
    module: &Name,
    field: &'static str,
    expected: Hash,
    actual: Hash,
) -> Result<(), MachineStdLibraryReleaseError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MachineStdLibraryReleaseError::ModuleArtifactHashMismatch {
            module: module.clone(),
            field,
            expected,
            actual,
        })
    }
}

fn compare_module_count(
    module: &Name,
    field: &'static str,
    expected: u64,
    actual: u64,
) -> Result<(), MachineStdLibraryReleaseError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MachineStdLibraryReleaseError::ModuleArtifactCountMismatch {
            module: module.clone(),
            field,
            expected,
            actual,
        })
    }
}

pub fn generate_machine_std_mvp_theorem_index(
    loaded: &MachineStdLoadedRelease,
) -> Result<MachineStdTheoremIndex, MachineStdTheoremIndexError> {
    let mut entries = Vec::new();
    for module in loaded.modules() {
        for export in module.verified_module.export_block() {
            if matches!(export.kind, ExportKind::Theorem | ExportKind::Axiom) {
                entries.push(generate_machine_std_theorem_entry(loaded, module, export)?);
            }
        }
    }
    let mut keyed_entries = entries
        .into_iter()
        .map(|entry| {
            Ok((
                machine_std_global_ref_canonical_bytes(&entry.global_ref)
                    .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?,
                entry,
            ))
        })
        .collect::<Result<Vec<_>, MachineStdTheoremIndexError>>()?;
    keyed_entries.sort_by_cached_key(|(key, _)| key.clone());

    Ok(MachineStdTheoremIndex {
        index_profile_id: STD_THEOREM_INDEX_PROFILE_ID.to_owned(),
        library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
        entries: keyed_entries.into_iter().map(|(_, entry)| entry).collect(),
        index_hash: [0; 32],
    })
}

pub fn validate_machine_std_mvp_theorem_index(
    actual: &MachineStdTheoremIndex,
    expected: &MachineStdTheoremIndex,
) -> Result<(), MachineStdTheoremIndexError> {
    if actual.index_profile_id != STD_THEOREM_INDEX_PROFILE_ID {
        return Err(MachineStdTheoremIndexError::IndexProfileMismatch {
            expected: STD_THEOREM_INDEX_PROFILE_ID,
            actual: actual.index_profile_id.clone(),
        });
    }
    if actual.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdTheoremIndexError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: actual.library_profile_id.clone(),
        });
    }

    validate_theorem_entry_membership(&actual.entries, &expected.entries)?;
    let expected_by_key = expected_theorem_entries_by_key(expected)?;
    for actual_entry in &actual.entries {
        let key = machine_std_global_ref_canonical_bytes(&actual_entry.global_ref)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        let expected_entry = expected_by_key
            .get(&key)
            .expect("membership validation checked entry key");
        validate_theorem_entry_order(actual_entry)?;
        validate_theorem_entry_contents(actual_entry, expected_entry)?;
    }
    Ok(())
}

pub fn finalize_machine_std_mvp_theorem_index(
    base: &MachineStdTheoremIndex,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<MachineStdTheoremIndex, MachineStdTheoremIndexError> {
    let mut finalized = base.clone();
    let mut rewrite_metadata = rewrite_metadata_by_source(rewrite_profiles)?;
    let mut simp_metadata = simp_metadata_by_source(simp_profiles, rewrite_profiles)?;

    for entry in &mut finalized.entries {
        let source_key = machine_std_global_ref_canonical_bytes(&entry.global_ref)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        let rewrite_descriptors: Vec<MachineStdRewriteDescriptor> = rewrite_metadata
            .remove(&source_key)
            .map(|(_, descriptors)| descriptors.into_values().collect())
            .unwrap_or_default();
        let has_rw = !rewrite_descriptors.is_empty();
        let has_simp = simp_metadata.remove(&source_key).is_some();
        entry.modes = finalized_theorem_modes(&entry.modes, has_rw, has_simp);
        entry.attributes = finalized_theorem_attributes(&entry.modes);
        entry.rewrite_descriptors = rewrite_descriptors;
    }

    if let Some((_, (global_ref, _))) = rewrite_metadata.into_iter().next() {
        return Err(MachineStdTheoremIndexError::ProfileSourceMissing {
            global_ref: Box::new(global_ref),
        });
    }
    if let Some((_, global_ref)) = simp_metadata.into_iter().next() {
        return Err(MachineStdTheoremIndexError::ProfileSourceMissing {
            global_ref: Box::new(global_ref),
        });
    }

    finalized.index_hash = machine_std_theorem_index_hash(&finalized)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    Ok(finalized)
}

pub fn generate_machine_std_mvp_final_theorem_index(
    loaded: &MachineStdLoadedRelease,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<MachineStdTheoremIndex, MachineStdTheoremIndexError> {
    let base = generate_machine_std_mvp_theorem_index(loaded)?;
    finalize_machine_std_mvp_theorem_index(&base, rewrite_profiles, simp_profiles)
}

pub fn generate_human_std_theorem_search_view(
    loaded: &MachineStdLoadedRelease,
    theorem_index: &MachineStdTheoremIndex,
) -> Result<HumanStdTheoremSearchView, MachineStdTheoremIndexError> {
    let mut entries = Vec::with_capacity(theorem_index.entries.len());
    for entry in &theorem_index.entries {
        if entry.proof_term_size.is_some() {
            return Err(MachineStdTheoremIndexError::NonNullProofTermSize {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        let categories = human_std_theorem_categories(entry);
        let display_attributes = human_std_display_attributes(&categories);
        let suggested_tactics = human_std_suggested_tactics(entry, &categories);
        entries.push(HumanStdTheoremSearchEntry {
            global_ref: entry.global_ref.clone(),
            kind: entry.kind,
            categories,
            display_attributes,
            statement_core_hash: entry.statement_core_hash,
            statement_head: entry.statement_head.clone(),
            constants: entry.constants.clone(),
            axiom_dependencies: entry.axiom_dependencies.clone(),
            proof_term_size: human_std_proof_term_size(loaded, entry)?,
            suggested_tactics,
        });
    }

    let mut view = HumanStdTheoremSearchView {
        library_profile_id: theorem_index.library_profile_id.clone(),
        entries,
        debug_hash: [0; 32],
    };
    view.debug_hash = human_std_theorem_search_view_hash(&view)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    Ok(view)
}

pub fn generate_human_std_module_debug_views(
    loaded: &MachineStdLoadedRelease,
    theorem_view: &HumanStdTheoremSearchView,
    axiom_report: &MachineStdAxiomReport,
) -> Result<Vec<HumanStdModuleDebugViews>, MachineStdTheoremIndexError> {
    loaded
        .verification_order()
        .iter()
        .map(|module| {
            let module_axioms = axiom_report
                .modules
                .iter()
                .find(|entry| &entry.module == module)
                .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
                    module: module.clone(),
                })?;
            let entries = theorem_view
                .entries
                .iter()
                .filter(|entry| &entry.global_ref.module == module)
                .cloned()
                .collect::<Vec<_>>();
            let index = human_std_module_index_debug_view(module.clone(), entries)?;
            let axioms = human_std_module_axioms_debug_view(module_axioms)?;
            let graph = human_std_module_graph_debug_view(module.clone(), &index.entries)?;
            Ok(HumanStdModuleDebugViews {
                module: module.clone(),
                index,
                axioms,
                graph,
            })
        })
        .collect()
}

pub fn validate_machine_std_mvp_final_theorem_index(
    actual: &MachineStdTheoremIndex,
    expected: &MachineStdTheoremIndex,
) -> Result<(), MachineStdTheoremIndexError> {
    if actual.index_profile_id != STD_THEOREM_INDEX_PROFILE_ID {
        return Err(MachineStdTheoremIndexError::IndexProfileMismatch {
            expected: STD_THEOREM_INDEX_PROFILE_ID,
            actual: actual.index_profile_id.clone(),
        });
    }
    if actual.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdTheoremIndexError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: actual.library_profile_id.clone(),
        });
    }

    validate_theorem_entry_membership(&actual.entries, &expected.entries)?;
    let expected_by_key = expected_theorem_entries_by_key(expected)?;
    for actual_entry in &actual.entries {
        let key = machine_std_global_ref_canonical_bytes(&actual_entry.global_ref)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        let expected_entry = expected_by_key
            .get(&key)
            .expect("membership validation checked entry key");
        validate_theorem_entry_order(actual_entry)?;
        validate_final_theorem_entry_contents(actual_entry, expected_entry)?;
    }

    let actual_hash = machine_std_theorem_index_hash(actual)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    if actual_hash != actual.index_hash {
        return Err(MachineStdTheoremIndexError::TheoremIndexHashMismatch {
            expected: actual.index_hash,
            actual: actual_hash,
        });
    }
    if actual.index_hash != expected.index_hash {
        return Err(MachineStdTheoremIndexError::TheoremIndexHashMismatch {
            expected: expected.index_hash,
            actual: actual.index_hash,
        });
    }
    Ok(())
}

pub fn validate_machine_std_mvp_release_final_sidecar_counts(
    manifest: &MachineStdLibraryRelease,
    theorem_index: &MachineStdTheoremIndex,
    simp_profiles: &MachineStdSimpProfileSet,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<(), MachineStdReleaseArtifactError> {
    let mut theorem_counts = BTreeMap::<Name, u64>::new();
    for entry in &theorem_index.entries {
        *theorem_counts
            .entry(entry.global_ref.module.clone())
            .or_default() += 1;
    }
    let simp_counts = simp_rule_counts_by_module(simp_profiles, rewrite_profiles)
        .map_err(MachineStdReleaseArtifactError::InvalidStdTheoremIndex)?;

    for artifact in &manifest.modules {
        compare_module_count(
            &artifact.module,
            "theorem_index_entry_count",
            artifact.theorem_index_entry_count,
            *theorem_counts.get(&artifact.module).unwrap_or(&0),
        )
        .map_err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease)?;
        compare_module_count(
            &artifact.module,
            "simp_rule_count",
            artifact.simp_rule_count,
            *simp_counts.get(&artifact.module).unwrap_or(&0),
        )
        .map_err(MachineStdReleaseArtifactError::InvalidStdLibraryRelease)?;
    }
    Ok(())
}

pub fn human_std_theorem_search_view_canonical_bytes(
    view: &HumanStdTheoremSearchView,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_THEOREM_SEARCH_VIEW_TAG);
    encode_string(&mut out, &view.library_profile_id);
    encode_uvar(&mut out, view.entries.len() as u64);
    for entry in &view.entries {
        out.extend(human_std_theorem_search_entry_canonical_bytes(entry)?);
    }
    Ok(out)
}

pub fn human_std_theorem_search_view_hash(
    view: &HumanStdTheoremSearchView,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    Ok(sha256(&human_std_theorem_search_view_canonical_bytes(
        view,
    )?))
}

fn human_std_theorem_search_entry_canonical_bytes(
    entry: &HumanStdTheoremSearchEntry,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_THEOREM_SEARCH_ENTRY_TAG);
    out.extend(machine_std_global_ref_canonical_bytes(&entry.global_ref)?);
    out.push(theorem_kind_byte(entry.kind));
    encode_uvar(&mut out, entry.categories.len() as u64);
    for category in &entry.categories {
        out.push(human_std_theorem_category_byte(*category));
    }
    encode_uvar(&mut out, entry.display_attributes.len() as u64);
    for attribute in &entry.display_attributes {
        out.push(human_std_display_attribute_byte(*attribute));
    }
    encode_hash(&mut out, &entry.statement_core_hash);
    encode_option_global_ref_view(&mut out, entry.statement_head.as_ref())?;
    encode_uvar(&mut out, entry.constants.len() as u64);
    for constant in &entry.constants {
        out.extend(machine_std_global_ref_view_canonical_bytes(constant)?);
    }
    encode_uvar(&mut out, entry.axiom_dependencies.len() as u64);
    for axiom in &entry.axiom_dependencies {
        out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
    }
    encode_option_u64(&mut out, entry.proof_term_size);
    encode_uvar(&mut out, entry.suggested_tactics.len() as u64);
    for tactic in &entry.suggested_tactics {
        encode_string(&mut out, tactic);
    }
    Ok(out)
}

fn human_std_module_index_debug_view(
    module: Name,
    entries: Vec<HumanStdTheoremSearchEntry>,
) -> Result<HumanStdModuleIndexDebugView, MachineStdTheoremIndexError> {
    let mut view = HumanStdModuleIndexDebugView {
        module,
        entries,
        debug_hash: [0; 32],
    };
    view.debug_hash = human_std_module_index_debug_hash(&view)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    Ok(view)
}

fn human_std_module_axioms_debug_view(
    module_axioms: &MachineStdModuleAxiomReport,
) -> Result<HumanStdModuleAxiomsDebugView, MachineStdTheoremIndexError> {
    let mut view = HumanStdModuleAxiomsDebugView {
        module: module_axioms.module.clone(),
        export_hash: module_axioms.export_hash,
        certificate_hash: module_axioms.certificate_hash,
        module_axioms: module_axioms.module_axioms.clone(),
        transitive_axioms: module_axioms.transitive_axioms.clone(),
        debug_hash: [0; 32],
    };
    view.debug_hash = human_std_module_axioms_debug_hash(&view)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    Ok(view)
}

fn human_std_module_graph_debug_view(
    module: Name,
    entries: &[HumanStdTheoremSearchEntry],
) -> Result<HumanStdModuleGraphDebugView, MachineStdTheoremIndexError> {
    let mut edges = Vec::new();
    for entry in entries {
        if let Some(head) = &entry.statement_head {
            edges.push(HumanStdDependencyEdge {
                source: entry.global_ref.clone(),
                kind: HumanStdDependencyKind::StatementHead,
                target: HumanStdDependencyTarget::GlobalRef(head.clone()),
            });
        }
        for constant in &entry.constants {
            edges.push(HumanStdDependencyEdge {
                source: entry.global_ref.clone(),
                kind: HumanStdDependencyKind::StatementConstant,
                target: HumanStdDependencyTarget::GlobalRef(constant.clone()),
            });
        }
        for axiom in &entry.axiom_dependencies {
            edges.push(HumanStdDependencyEdge {
                source: entry.global_ref.clone(),
                kind: HumanStdDependencyKind::AxiomDependency,
                target: HumanStdDependencyTarget::Axiom(axiom.clone()),
            });
        }
    }
    let mut keyed_edges = edges
        .into_iter()
        .map(|edge| {
            Ok((
                human_std_dependency_edge_canonical_bytes(&edge)
                    .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?,
                edge,
            ))
        })
        .collect::<Result<Vec<_>, MachineStdTheoremIndexError>>()?;
    keyed_edges.sort_by_cached_key(|(key, _)| key.clone());
    keyed_edges.dedup_by(|left, right| left.0 == right.0);

    let mut view = HumanStdModuleGraphDebugView {
        module,
        edges: keyed_edges.into_iter().map(|(_, edge)| edge).collect(),
        debug_hash: [0; 32],
    };
    view.debug_hash = human_std_module_graph_debug_hash(&view)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    Ok(view)
}

fn human_std_module_index_debug_hash(
    view: &HumanStdModuleIndexDebugView,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_MODULE_INDEX_DEBUG_TAG);
    encode_name(&mut out, &view.module)?;
    encode_uvar(&mut out, view.entries.len() as u64);
    for entry in &view.entries {
        out.extend(human_std_theorem_search_entry_canonical_bytes(entry)?);
    }
    Ok(sha256(&out))
}

fn human_std_module_axioms_debug_hash(
    view: &HumanStdModuleAxiomsDebugView,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_MODULE_AXIOMS_DEBUG_TAG);
    encode_name(&mut out, &view.module)?;
    encode_hash(&mut out, &view.export_hash);
    encode_hash(&mut out, &view.certificate_hash);
    encode_uvar(&mut out, view.module_axioms.len() as u64);
    for axiom in &view.module_axioms {
        out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
    }
    encode_uvar(&mut out, view.transitive_axioms.len() as u64);
    for axiom in &view.transitive_axioms {
        out.extend(machine_std_axiom_ref_canonical_bytes(axiom)?);
    }
    Ok(sha256(&out))
}

fn human_std_module_graph_debug_hash(
    view: &HumanStdModuleGraphDebugView,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_MODULE_GRAPH_DEBUG_TAG);
    encode_name(&mut out, &view.module)?;
    encode_uvar(&mut out, view.edges.len() as u64);
    for edge in &view.edges {
        out.extend(human_std_dependency_edge_canonical_bytes(edge)?);
    }
    Ok(sha256(&out))
}

fn human_std_dependency_edge_canonical_bytes(
    edge: &HumanStdDependencyEdge,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_string(&mut out, STD_HUMAN_MODULE_GRAPH_EDGE_TAG);
    out.extend(machine_std_global_ref_canonical_bytes(&edge.source)?);
    out.push(human_std_dependency_kind_byte(edge.kind));
    match &edge.target {
        HumanStdDependencyTarget::GlobalRef(target) => {
            out.push(0x00);
            out.extend(machine_std_global_ref_view_canonical_bytes(target)?);
        }
        HumanStdDependencyTarget::Axiom(target) => {
            out.push(0x01);
            out.extend(machine_std_axiom_ref_canonical_bytes(target)?);
        }
    }
    Ok(out)
}

pub fn validate_machine_std_mvp_optional_prompt_metadata(
    metadata: Option<&MachineStdPromptMetadataSet>,
    theorem_index: &MachineStdTheoremIndex,
    import_bundles: &MachineStdImportBundleSet,
) -> Result<(), MachineStdPromptMetadataError> {
    let Some(metadata) = metadata else {
        return Ok(());
    };
    validate_machine_std_mvp_prompt_metadata(metadata, theorem_index, import_bundles)
}

pub fn validate_machine_std_mvp_prompt_metadata(
    metadata: &MachineStdPromptMetadataSet,
    theorem_index: &MachineStdTheoremIndex,
    import_bundles: &MachineStdImportBundleSet,
) -> Result<(), MachineStdPromptMetadataError> {
    if metadata.metadata_profile_id != STD_PROMPT_METADATA_PROFILE_ID {
        return Err(MachineStdPromptMetadataError::MetadataProfileMismatch {
            expected: STD_PROMPT_METADATA_PROFILE_ID,
            actual: metadata.metadata_profile_id.clone(),
        });
    }
    if metadata.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdPromptMetadataError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: metadata.library_profile_id.clone(),
        });
    }

    validate_prompt_metadata_entries(metadata, theorem_index)?;
    validate_prompt_metadata_examples(metadata, import_bundles)?;

    let actual_hash = machine_std_prompt_metadata_hash(metadata)
        .map_err(|source| MachineStdPromptMetadataError::CanonicalBytes { source })?;
    if actual_hash != metadata.prompt_metadata_hash {
        return Err(MachineStdPromptMetadataError::PromptMetadataHashMismatch {
            expected: metadata.prompt_metadata_hash,
            actual: actual_hash,
        });
    }
    Ok(())
}

fn validate_prompt_metadata_entries(
    metadata: &MachineStdPromptMetadataSet,
    theorem_index: &MachineStdTheoremIndex,
) -> Result<(), MachineStdPromptMetadataError> {
    let theorem_refs = theorem_index
        .entries
        .iter()
        .map(|entry| {
            Ok((
                machine_std_global_ref_canonical_bytes(&entry.global_ref)
                    .map_err(|source| MachineStdPromptMetadataError::CanonicalBytes { source })?,
                entry.global_ref.clone(),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, MachineStdPromptMetadataError>>()?;

    let mut actual_pairs = Vec::with_capacity(metadata.entries.len());
    let mut seen = BTreeSet::new();
    for entry in &metadata.entries {
        validate_prompt_metadata_tags(entry)?;
        let key = machine_std_global_ref_canonical_bytes(&entry.global_ref)
            .map_err(|source| MachineStdPromptMetadataError::CanonicalBytes { source })?;
        if !seen.insert(key.clone()) {
            return Err(MachineStdPromptMetadataError::DuplicateEntry {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        if !theorem_refs.contains_key(&key) {
            return Err(MachineStdPromptMetadataError::StaleGlobalRef {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        actual_pairs.push((key, entry.global_ref.clone()));
    }

    let mut expected_pairs = actual_pairs.clone();
    expected_pairs.sort_by_cached_key(|(key, _)| key.clone());
    let actual_refs = actual_pairs
        .iter()
        .map(|(_, global_ref)| global_ref.clone())
        .collect::<Vec<_>>();
    let expected_refs = expected_pairs
        .iter()
        .map(|(_, global_ref)| global_ref.clone())
        .collect::<Vec<_>>();
    if actual_refs != expected_refs {
        return Err(MachineStdPromptMetadataError::NonCanonicalEntryOrder {
            expected: expected_refs,
            actual: actual_refs,
        });
    }
    Ok(())
}

fn validate_prompt_metadata_tags(
    metadata: &MachineStdPromptMetadata,
) -> Result<(), MachineStdPromptMetadataError> {
    let mut previous: Option<&str> = None;
    let mut seen = BTreeSet::new();
    for tag in &metadata.tags {
        if !seen.insert(tag.as_str()) {
            return Err(MachineStdPromptMetadataError::DuplicateTag {
                global_ref: Box::new(metadata.global_ref.clone()),
                tag: tag.clone(),
            });
        }
        if previous.is_some_and(|previous| previous.as_bytes() > tag.as_bytes()) {
            return Err(MachineStdPromptMetadataError::NonCanonicalTagOrder {
                global_ref: Box::new(metadata.global_ref.clone()),
            });
        }
        previous = Some(tag);
        if !is_mvp_prompt_tag(tag) {
            return Err(MachineStdPromptMetadataError::UnknownTag {
                global_ref: Box::new(metadata.global_ref.clone()),
                tag: tag.clone(),
            });
        }
    }
    Ok(())
}

fn validate_prompt_metadata_examples(
    metadata: &MachineStdPromptMetadataSet,
    import_bundles: &MachineStdImportBundleSet,
) -> Result<(), MachineStdPromptMetadataError> {
    let bundle_ids = import_bundles
        .bundles
        .iter()
        .map(|bundle| bundle.bundle_id.as_str())
        .collect::<BTreeSet<_>>();
    for entry in &metadata.entries {
        for example in &entry.examples {
            if !is_mvp_prompt_candidate_kind(&example.candidate_kind) {
                return Err(MachineStdPromptMetadataError::InvalidCandidateKind {
                    global_ref: Box::new(entry.global_ref.clone()),
                    candidate_kind: example.candidate_kind.clone(),
                });
            }
            if !bundle_ids.contains(example.imports_bundle_id.as_str()) {
                return Err(MachineStdPromptMetadataError::UnknownImportBundle {
                    global_ref: Box::new(entry.global_ref.clone()),
                    imports_bundle_id: example.imports_bundle_id.clone(),
                });
            }
        }
    }
    Ok(())
}

fn is_mvp_prompt_tag(tag: &str) -> bool {
    matches!(
        tag,
        "eq" | "logic"
            | "nat"
            | "list"
            | "algebra"
            | "simp"
            | "rw"
            | "apply"
            | "intro"
            | "elim"
            | "induction"
    )
}

fn is_mvp_prompt_candidate_kind(candidate_kind: &str) -> bool {
    matches!(candidate_kind, "exact" | "apply" | "rw" | "simp" | "note")
}

type RewriteMetadataBySource = BTreeMap<
    Vec<u8>,
    (
        MachineStdGlobalRef,
        BTreeMap<Vec<u8>, MachineStdRewriteDescriptor>,
    ),
>;

fn rewrite_metadata_by_source(
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<RewriteMetadataBySource, MachineStdTheoremIndexError> {
    let mut out = RewriteMetadataBySource::new();
    for profile in &rewrite_profiles.profiles {
        for descriptor in &profile.descriptors {
            let source_key = machine_std_global_ref_canonical_bytes(&descriptor.source)
                .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
            let descriptor_key = machine_std_rewrite_descriptor_canonical_bytes(descriptor)
                .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
            out.entry(source_key)
                .or_insert_with(|| (descriptor.source.clone(), BTreeMap::new()))
                .1
                .insert(descriptor_key, descriptor.clone());
        }
    }
    Ok(out)
}

fn simp_metadata_by_source(
    simp_profiles: &MachineStdSimpProfileSet,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<BTreeMap<Vec<u8>, MachineStdGlobalRef>, MachineStdTheoremIndexError> {
    let mut out = BTreeMap::new();
    for (_, (source, _)) in resolved_simp_rule_targets(simp_profiles, rewrite_profiles)? {
        let source_key = machine_std_global_ref_canonical_bytes(&source)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        out.entry(source_key).or_insert(source);
    }
    Ok(out)
}

fn simp_rule_counts_by_module(
    simp_profiles: &MachineStdSimpProfileSet,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<BTreeMap<Name, u64>, MachineStdTheoremIndexError> {
    let mut targets_by_module = BTreeMap::<Name, BTreeSet<Vec<u8>>>::new();
    for (target_key, (source, _)) in resolved_simp_rule_targets(simp_profiles, rewrite_profiles)? {
        targets_by_module
            .entry(source.module)
            .or_default()
            .insert(target_key);
    }
    Ok(targets_by_module
        .into_iter()
        .map(|(module, targets)| (module, targets.len() as u64))
        .collect())
}

fn resolved_simp_rule_targets(
    simp_profiles: &MachineStdSimpProfileSet,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<BTreeMap<Vec<u8>, (MachineStdGlobalRef, RewriteDirection)>, MachineStdTheoremIndexError>
{
    let mut out = BTreeMap::new();
    for profile in &simp_profiles.profiles {
        let paired_id = paired_rewrite_profile_id(&profile.profile_id).ok_or_else(|| {
            MachineStdTheoremIndexError::ProfileMetadataMismatch {
                profile_id: profile.profile_id.clone(),
                name: Name::from_dotted(&profile.profile_id),
            }
        })?;
        let paired = rewrite_profiles
            .profiles
            .iter()
            .find(|rewrite| rewrite.profile_id == paired_id)
            .ok_or_else(|| MachineStdTheoremIndexError::ProfileMetadataMismatch {
                profile_id: profile.profile_id.clone(),
                name: Name::from_dotted(paired_id),
            })?;
        for rule in &profile.rules {
            let descriptor = unique_paired_simp_descriptor(&profile.profile_id, paired, rule)?;
            let target_key = simp_rule_target_key(&descriptor.source, descriptor.direction)?;
            out.entry(target_key)
                .or_insert((descriptor.source.clone(), descriptor.direction));
        }
    }
    Ok(out)
}

fn unique_paired_simp_descriptor<'a>(
    profile_id: &str,
    paired: &'a MachineStdRewriteProfile,
    rule: &SimpRuleRef,
) -> Result<&'a MachineStdRewriteDescriptor, MachineStdTheoremIndexError> {
    let mut matches = paired.descriptors.iter().filter(|descriptor| {
        descriptor.safety == MachineStdRewriteSafety::SimpSafe
            && descriptor.direction == rule.direction
            && descriptor.source.name == rule.name
            && descriptor.source.decl_interface_hash == rule.decl_interface_hash
    });
    let first =
        matches
            .next()
            .ok_or_else(|| MachineStdTheoremIndexError::ProfileMetadataMismatch {
                profile_id: profile_id.to_owned(),
                name: rule.name.clone(),
            })?;
    if matches.next().is_some() {
        return Err(MachineStdTheoremIndexError::ProfileMetadataMismatch {
            profile_id: profile_id.to_owned(),
            name: rule.name.clone(),
        });
    }
    Ok(first)
}

fn simp_rule_target_key(
    source: &MachineStdGlobalRef,
    direction: RewriteDirection,
) -> Result<Vec<u8>, MachineStdTheoremIndexError> {
    let mut out = machine_std_global_ref_canonical_bytes(source)
        .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
    encode_rewrite_direction(&mut out, direction);
    Ok(out)
}

fn finalized_theorem_modes(
    base_modes: &[MachineTheoremMode],
    has_rw: bool,
    has_simp: bool,
) -> Vec<MachineTheoremMode> {
    let mut modes = Vec::new();
    if base_modes.contains(&MachineTheoremMode::Exact) {
        modes.push(MachineTheoremMode::Exact);
    }
    if base_modes.contains(&MachineTheoremMode::Apply) {
        modes.push(MachineTheoremMode::Apply);
    }
    if has_rw {
        modes.push(MachineTheoremMode::Rw);
    }
    if has_simp {
        modes.push(MachineTheoremMode::Simp);
    }
    modes
}

fn finalized_theorem_attributes(modes: &[MachineTheoremMode]) -> Vec<MachineStdAttribute> {
    let mut attributes = Vec::new();
    if modes.contains(&MachineTheoremMode::Simp) {
        attributes.push(MachineStdAttribute::Simp);
    }
    if modes.contains(&MachineTheoremMode::Rw) {
        attributes.push(MachineStdAttribute::Rw);
    }
    if modes.contains(&MachineTheoremMode::Apply) {
        attributes.push(MachineStdAttribute::Apply);
    }
    attributes
}

fn human_std_theorem_categories(entry: &MachineStdTheoremEntry) -> Vec<HumanStdTheoremCategory> {
    let mut categories = Vec::new();
    if entry.modes.contains(&MachineTheoremMode::Exact) {
        categories.push(HumanStdTheoremCategory::Exact);
    }
    if entry.modes.contains(&MachineTheoremMode::Apply) {
        categories.push(HumanStdTheoremCategory::Apply);
    }
    if entry.modes.contains(&MachineTheoremMode::Rw) {
        categories.push(HumanStdTheoremCategory::Rw);
    }
    if entry.modes.contains(&MachineTheoremMode::Simp) {
        categories.push(HumanStdTheoremCategory::Simp);
    }
    let name = entry.global_ref.name.as_dotted();
    if human_std_intro_theorem_name(&name) {
        categories.push(HumanStdTheoremCategory::Intro);
    }
    if human_std_elim_theorem_name(&name) {
        categories.push(HumanStdTheoremCategory::Elim);
    }
    categories.sort();
    categories.dedup();
    categories
}

fn human_std_intro_theorem_name(name: &str) -> bool {
    name.ends_with(".intro")
}

fn human_std_elim_theorem_name(name: &str) -> bool {
    name.ends_with(".elim") || name == "absurd"
}

fn human_std_display_attributes(
    categories: &[HumanStdTheoremCategory],
) -> Vec<HumanStdTheoremDisplayAttribute> {
    let mut attributes = Vec::new();
    if categories.contains(&HumanStdTheoremCategory::Simp) {
        attributes.push(HumanStdTheoremDisplayAttribute::Simp);
    }
    if categories.contains(&HumanStdTheoremCategory::Rw) {
        attributes.push(HumanStdTheoremDisplayAttribute::Rw);
    }
    if categories.contains(&HumanStdTheoremCategory::Apply) {
        attributes.push(HumanStdTheoremDisplayAttribute::Apply);
    }
    if categories.contains(&HumanStdTheoremCategory::Intro) {
        attributes.push(HumanStdTheoremDisplayAttribute::Intro);
    }
    if categories.contains(&HumanStdTheoremCategory::Elim) {
        attributes.push(HumanStdTheoremDisplayAttribute::Elim);
    }
    attributes
}

fn human_std_suggested_tactics(
    entry: &MachineStdTheoremEntry,
    categories: &[HumanStdTheoremCategory],
) -> Vec<String> {
    let name = entry.global_ref.name.as_dotted();
    let mut tactics = Vec::new();
    for category in categories {
        match category {
            HumanStdTheoremCategory::Exact => {}
            HumanStdTheoremCategory::Apply
            | HumanStdTheoremCategory::Intro
            | HumanStdTheoremCategory::Elim => tactics.push(format!("apply {name}")),
            HumanStdTheoremCategory::Rw => tactics.push(format!("rw [{name}]")),
            HumanStdTheoremCategory::Simp => tactics.push("simp-lite".to_owned()),
        }
    }
    tactics.sort();
    tactics.dedup();
    tactics
}

fn human_std_proof_term_size(
    loaded: &MachineStdLoadedRelease,
    entry: &MachineStdTheoremEntry,
) -> Result<Option<u64>, MachineStdTheoremIndexError> {
    let Some(module) = loaded.module(&entry.global_ref.module) else {
        return Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: entry.global_ref.module.clone(),
        });
    };
    let Some(decl) = module.verified_module.declarations().iter().find(|decl| {
        decl.hashes.decl_interface_hash == entry.global_ref.decl_interface_hash
            && std_library_decl_name(module, decl).as_ref() == Some(&entry.global_ref.name)
    }) else {
        return Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: entry.global_ref.module.clone(),
        });
    };
    let DeclPayload::Theorem { proof, .. } = &decl.decl else {
        return Ok(None);
    };
    human_std_reachable_term_size(module, *proof).map(Some)
}

fn human_std_reachable_term_size(
    module: &MachineStdLoadedModule,
    root: TermId,
) -> Result<u64, MachineStdTheoremIndexError> {
    fn visit(
        module: &MachineStdLoadedModule,
        term: TermId,
        seen: &mut BTreeSet<TermId>,
    ) -> Result<(), MachineStdTheoremIndexError> {
        if !seen.insert(term) {
            return Ok(());
        }
        let node = module
            .verified_module
            .term_table()
            .get(term)
            .ok_or_else(|| MachineStdTheoremIndexError::InvalidTermRef {
                module: module.module.clone(),
            })?;
        match node {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(fun, arg) => {
                visit(module, *fun, seen)?;
                visit(module, *arg, seen)?;
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                visit(module, *ty, seen)?;
                visit(module, *body, seen)?;
            }
            TermNode::Let { ty, value, body } => {
                visit(module, *ty, seen)?;
                visit(module, *value, seen)?;
                visit(module, *body, seen)?;
            }
        }
        Ok(())
    }

    let mut seen = BTreeSet::new();
    visit(module, root, &mut seen)?;
    Ok(seen.len() as u64)
}

fn generate_machine_std_theorem_entry(
    loaded: &MachineStdLoadedRelease,
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> Result<MachineStdTheoremEntry, MachineStdTheoremIndexError> {
    let name = theorem_export_name(module, export)?;
    ensure_renderable_theorem_name(module, &name)?;
    let kind = match export.kind {
        ExportKind::Theorem => MachineStdTheoremKind::Theorem,
        ExportKind::Axiom => MachineStdTheoremKind::Axiom,
        _ => {
            return Err(MachineStdTheoremIndexError::InvalidExportKind {
                module: module.module.clone(),
                name,
            });
        }
    };
    let universe_params = theorem_export_universe_params(module, export)?;
    let statement_head = theorem_statement_head(loaded, module, export.ty)?;
    let constants = theorem_statement_constants(loaded, module, export.ty)?;
    let axiom_dependencies = project_export_axiom_dependencies(loaded, module, export)?;
    let mut modes = vec![MachineTheoremMode::Exact];
    if has_leading_pi_term(module, export.ty)? {
        modes.push(MachineTheoremMode::Apply);
    }

    Ok(MachineStdTheoremEntry {
        global_ref: MachineStdGlobalRef {
            module: module.module.clone(),
            name,
            export_hash: module.expected_export_hash,
            certificate_hash: module.expected_certificate_hash,
            decl_interface_hash: export.decl_interface_hash,
        },
        kind,
        universe_params,
        statement_core_hash: export.type_hash,
        statement_head,
        constants,
        modes,
        attributes: Vec::new(),
        rewrite_descriptors: Vec::new(),
        axiom_dependencies,
        proof_term_size: None,
    })
}

fn validate_theorem_entry_membership(
    actual: &[MachineStdTheoremEntry],
    expected: &[MachineStdTheoremEntry],
) -> Result<(), MachineStdTheoremIndexError> {
    let mut actual_pairs = theorem_entry_global_ref_pairs(actual)?;
    let mut seen = BTreeSet::new();
    for (key, global_ref) in &actual_pairs {
        if !seen.insert(key.clone()) {
            return Err(MachineStdTheoremIndexError::DuplicateEntry {
                global_ref: Box::new(global_ref.clone()),
            });
        }
    }
    let mut expected_pairs = theorem_entry_global_ref_pairs(expected)?;
    actual_pairs.sort_by_cached_key(|(key, _)| key.clone());
    expected_pairs.sort_by_cached_key(|(key, _)| key.clone());
    let actual_sorted_refs = actual_pairs
        .iter()
        .map(|(_, global_ref)| global_ref.clone())
        .collect::<Vec<_>>();
    let expected_sorted_refs = expected_pairs
        .iter()
        .map(|(_, global_ref)| global_ref.clone())
        .collect::<Vec<_>>();
    if actual_sorted_refs != expected_sorted_refs {
        return Err(MachineStdTheoremIndexError::InvalidEntryMembership {
            expected: expected_sorted_refs,
            actual: actual_sorted_refs,
        });
    }
    let actual_refs = actual
        .iter()
        .map(|entry| entry.global_ref.clone())
        .collect::<Vec<_>>();
    if actual_refs != expected_sorted_refs {
        return Err(MachineStdTheoremIndexError::NonCanonicalEntryOrder {
            expected: expected_sorted_refs,
            actual: actual_refs,
        });
    }
    Ok(())
}

fn theorem_entry_global_ref_pairs(
    entries: &[MachineStdTheoremEntry],
) -> Result<Vec<(Vec<u8>, MachineStdGlobalRef)>, MachineStdTheoremIndexError> {
    entries
        .iter()
        .map(|entry| {
            Ok((
                machine_std_global_ref_canonical_bytes(&entry.global_ref)
                    .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?,
                entry.global_ref.clone(),
            ))
        })
        .collect()
}

fn expected_theorem_entries_by_key(
    expected: &MachineStdTheoremIndex,
) -> Result<BTreeMap<Vec<u8>, &MachineStdTheoremEntry>, MachineStdTheoremIndexError> {
    expected
        .entries
        .iter()
        .map(|entry| {
            Ok((
                machine_std_global_ref_canonical_bytes(&entry.global_ref)
                    .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?,
                entry,
            ))
        })
        .collect()
}

fn validate_theorem_entry_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    validate_theorem_modes_order(entry)?;
    validate_theorem_attributes_order(entry)?;
    validate_theorem_constants_order(entry)?;
    validate_theorem_rewrite_descriptors_order(entry)?;
    validate_theorem_axiom_dependencies_order(entry)?;
    Ok(())
}

fn validate_theorem_entry_contents(
    actual: &MachineStdTheoremEntry,
    expected: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    validate_certificate_derived_theorem_entry_contents(actual, expected)?;
    let global_ref = || Box::new(actual.global_ref.clone());
    if actual.modes.contains(&MachineTheoremMode::Exact)
        != expected.modes.contains(&MachineTheoremMode::Exact)
        || actual.modes.contains(&MachineTheoremMode::Apply)
            != expected.modes.contains(&MachineTheoremMode::Apply)
    {
        return Err(MachineStdTheoremIndexError::ModesMismatch {
            global_ref: global_ref(),
        });
    }
    Ok(())
}

fn validate_final_theorem_entry_contents(
    actual: &MachineStdTheoremEntry,
    expected: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    validate_certificate_derived_theorem_entry_contents(actual, expected)?;
    let global_ref = || Box::new(actual.global_ref.clone());
    if actual.modes != expected.modes {
        return Err(MachineStdTheoremIndexError::ModesMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.attributes != expected.attributes {
        return Err(MachineStdTheoremIndexError::AttributesMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.rewrite_descriptors != expected.rewrite_descriptors {
        return Err(MachineStdTheoremIndexError::RewriteDescriptorsMismatch {
            global_ref: global_ref(),
        });
    }
    Ok(())
}

fn validate_certificate_derived_theorem_entry_contents(
    actual: &MachineStdTheoremEntry,
    expected: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let global_ref = || Box::new(actual.global_ref.clone());
    if actual.kind != expected.kind {
        return Err(MachineStdTheoremIndexError::KindMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.universe_params != expected.universe_params {
        return Err(MachineStdTheoremIndexError::UniverseParamsMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.statement_core_hash != expected.statement_core_hash {
        return Err(MachineStdTheoremIndexError::StatementCoreHashMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.statement_head != expected.statement_head {
        return Err(MachineStdTheoremIndexError::StatementHeadMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.constants != expected.constants {
        return Err(MachineStdTheoremIndexError::ConstantsMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.axiom_dependencies != expected.axiom_dependencies {
        return Err(MachineStdTheoremIndexError::AxiomDependenciesMismatch {
            global_ref: global_ref(),
        });
    }
    if actual.proof_term_size.is_some() {
        return Err(MachineStdTheoremIndexError::NonNullProofTermSize {
            global_ref: global_ref(),
        });
    }
    Ok(())
}

fn validate_theorem_modes_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let mut previous = None;
    for mode in &entry.modes {
        let current = theorem_mode_byte(*mode);
        if previous.is_some_and(|previous| previous >= current) {
            return Err(MachineStdTheoremIndexError::NonCanonicalModes {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_theorem_attributes_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let mut previous = None;
    for attribute in &entry.attributes {
        let current = theorem_attribute_byte(*attribute);
        if previous.is_some_and(|previous| previous >= current) {
            return Err(MachineStdTheoremIndexError::NonCanonicalAttributes {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_theorem_constants_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let mut previous: Option<Vec<u8>> = None;
    for constant in &entry.constants {
        let current = machine_std_global_ref_view_canonical_bytes(constant)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        if previous
            .as_ref()
            .is_some_and(|previous| previous >= &current)
        {
            return Err(MachineStdTheoremIndexError::NonCanonicalConstants {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_theorem_axiom_dependencies_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let mut previous: Option<Vec<u8>> = None;
    for axiom in &entry.axiom_dependencies {
        let current = machine_std_axiom_ref_canonical_bytes(axiom)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        if previous
            .as_ref()
            .is_some_and(|previous| previous >= &current)
        {
            return Err(MachineStdTheoremIndexError::NonCanonicalAxiomDependencies {
                global_ref: Box::new(entry.global_ref.clone()),
            });
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_theorem_rewrite_descriptors_order(
    entry: &MachineStdTheoremEntry,
) -> Result<(), MachineStdTheoremIndexError> {
    let mut previous: Option<Vec<u8>> = None;
    for descriptor in &entry.rewrite_descriptors {
        let current = machine_std_rewrite_descriptor_canonical_bytes(descriptor)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        if previous
            .as_ref()
            .is_some_and(|previous| previous >= &current)
        {
            return Err(
                MachineStdTheoremIndexError::NonCanonicalRewriteDescriptors {
                    global_ref: Box::new(entry.global_ref.clone()),
                },
            );
        }
        previous = Some(current);
    }
    Ok(())
}

fn theorem_export_name(
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> Result<Name, MachineStdTheoremIndexError> {
    module
        .verified_module
        .name_table()
        .get(export.name)
        .cloned()
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: module.module.clone(),
        })
}

fn ensure_renderable_theorem_name(
    module: &MachineStdLoadedModule,
    name: &Name,
) -> Result<(), MachineStdTheoremIndexError> {
    parse_machine_surface_renderable_name_wire(&name.as_dotted())
        .map(|_| ())
        .map_err(|_| MachineStdTheoremIndexError::InvalidRenderableName {
            module: module.module.clone(),
            name: name.clone(),
        })
}

fn theorem_export_universe_params(
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> Result<Vec<String>, MachineStdTheoremIndexError> {
    let export_name = theorem_export_name(module, export)?;
    let mut seen = BTreeSet::new();
    export
        .universe_params
        .iter()
        .map(|name_id| {
            let name = module
                .verified_module
                .name_table()
                .get(*name_id)
                .ok_or_else(|| MachineStdTheoremIndexError::InvalidUniverseParam {
                    module: module.module.clone(),
                    name: export_name.clone(),
                })?;
            let [component] = name.0.as_slice() else {
                return Err(MachineStdTheoremIndexError::InvalidUniverseParam {
                    module: module.module.clone(),
                    name: export_name.clone(),
                });
            };
            let param = parse_machine_universe_param_name(component).map_err(|_| {
                MachineStdTheoremIndexError::InvalidUniverseParam {
                    module: module.module.clone(),
                    name: export_name.clone(),
                }
            })?;
            if !seen.insert(param.clone()) {
                return Err(MachineStdTheoremIndexError::DuplicateUniverseParam {
                    module: module.module.clone(),
                    name: export_name.clone(),
                    param,
                });
            }
            Ok(param)
        })
        .collect()
}

fn theorem_statement_head(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    ty: TermId,
) -> Result<Option<MachineStdGlobalRefView>, MachineStdTheoremIndexError> {
    let mut conclusion = ty;
    while let TermNode::Pi { body, .. } = term_node(owner, conclusion)?.clone() {
        conclusion = body;
    }
    let mut current = conclusion;
    while let TermNode::App(func, _) = term_node(owner, current)?.clone() {
        current = func;
    }
    match term_node(owner, current)? {
        TermNode::Const { global_ref, .. } => {
            normalize_std_global_ref_view(loaded, owner, global_ref).map(Some)
        }
        _ => Ok(None),
    }
}

fn theorem_statement_constants(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    ty: TermId,
) -> Result<Vec<MachineStdGlobalRefView>, MachineStdTheoremIndexError> {
    let mut constants = BTreeMap::new();
    let mut visited = BTreeSet::new();
    collect_term_constants(loaded, owner, ty, &mut visited, &mut constants)?;
    Ok(constants.into_values().collect())
}

fn collect_term_constants(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    term: TermId,
    visited: &mut BTreeSet<TermId>,
    constants: &mut BTreeMap<Vec<u8>, MachineStdGlobalRefView>,
) -> Result<(), MachineStdTheoremIndexError> {
    if !visited.insert(term) {
        return Ok(());
    }
    match term_node(owner, term)?.clone() {
        TermNode::Sort(_) | TermNode::BVar(_) => Ok(()),
        TermNode::Const { global_ref, .. } => {
            let view = normalize_std_global_ref_view(loaded, owner, &global_ref)?;
            let key = machine_std_global_ref_view_canonical_bytes(&view)
                .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
            constants.insert(key, view);
            Ok(())
        }
        TermNode::App(func, arg) => {
            collect_term_constants(loaded, owner, func, visited, constants)?;
            collect_term_constants(loaded, owner, arg, visited, constants)
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_term_constants(loaded, owner, ty, visited, constants)?;
            collect_term_constants(loaded, owner, body, visited, constants)
        }
        TermNode::Let { ty, value, body } => {
            collect_term_constants(loaded, owner, ty, visited, constants)?;
            collect_term_constants(loaded, owner, value, visited, constants)?;
            collect_term_constants(loaded, owner, body, visited, constants)
        }
    }
}

fn has_leading_pi_term(
    module: &MachineStdLoadedModule,
    ty: TermId,
) -> Result<bool, MachineStdTheoremIndexError> {
    Ok(matches!(term_node(module, ty)?, TermNode::Pi { .. }))
}

fn term_node(
    module: &MachineStdLoadedModule,
    term: TermId,
) -> Result<&TermNode, MachineStdTheoremIndexError> {
    module
        .verified_module
        .term_table()
        .get(term)
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidTermRef {
            module: module.module.clone(),
        })
}

fn normalize_std_global_ref_view(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    global_ref: &GlobalRef,
) -> Result<MachineStdGlobalRefView, MachineStdTheoremIndexError> {
    match global_ref {
        GlobalRef::Builtin { .. } => Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        }),
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => normalize_imported_global_ref_view(
            loaded,
            owner,
            *import_index,
            *name,
            *decl_interface_hash,
        ),
        GlobalRef::Local { decl_index } => normalize_local_global_ref_view(owner, *decl_index),
        GlobalRef::LocalGenerated { decl_index, name } => {
            normalize_local_generated_global_ref_view(owner, *decl_index, *name)
        }
    }
}

fn normalize_imported_global_ref_view(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    import_index: usize,
    name_id: usize,
    decl_interface_hash: Hash,
) -> Result<MachineStdGlobalRefView, MachineStdTheoremIndexError> {
    let import = owner.imports.get(import_index).ok_or_else(|| {
        MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        }
    })?;
    let imported = loaded.module(&import.module).ok_or_else(|| {
        MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        }
    })?;
    if import.export_hash != imported.expected_export_hash
        || import.certificate_hash != Some(imported.expected_certificate_hash)
    {
        return Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        });
    }
    let name = owner
        .verified_module
        .name_table()
        .get(name_id)
        .cloned()
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        })?;
    let export = unique_public_export(imported, &name, decl_interface_hash).ok_or_else(|| {
        MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        }
    })?;
    match export.kind {
        ExportKind::Constructor | ExportKind::Recursor => {
            let (parent_name, parent_decl_interface_hash) =
                generated_parent_for_public_export(imported, export)?;
            Ok(MachineStdGlobalRefView::Generated {
                module: imported.module.clone(),
                parent_name,
                name,
                export_hash: imported.expected_export_hash,
                certificate_hash: imported.expected_certificate_hash,
                parent_decl_interface_hash,
                decl_interface_hash,
                public_export: true,
            })
        }
        _ => Ok(MachineStdGlobalRefView::Decl {
            module: imported.module.clone(),
            name,
            export_hash: imported.expected_export_hash,
            certificate_hash: imported.expected_certificate_hash,
            decl_interface_hash,
            public_export: true,
        }),
    }
}

fn normalize_local_global_ref_view(
    owner: &MachineStdLoadedModule,
    decl_index: usize,
) -> Result<MachineStdGlobalRefView, MachineStdTheoremIndexError> {
    let decl = owner
        .verified_module
        .declarations()
        .get(decl_index)
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        })?;
    let name = decl_name(owner, decl)?;
    Ok(MachineStdGlobalRefView::Decl {
        module: owner.module.clone(),
        name: name.clone(),
        export_hash: owner.expected_export_hash,
        certificate_hash: owner.expected_certificate_hash,
        decl_interface_hash: decl.hashes.decl_interface_hash,
        public_export: public_export_exists(owner, &name, decl.hashes.decl_interface_hash),
    })
}

fn normalize_local_generated_global_ref_view(
    owner: &MachineStdLoadedModule,
    decl_index: usize,
    name_id: usize,
) -> Result<MachineStdGlobalRefView, MachineStdTheoremIndexError> {
    let decl = owner
        .verified_module
        .declarations()
        .get(decl_index)
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        })?;
    let generated_name = owner
        .verified_module
        .name_table()
        .get(name_id)
        .cloned()
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: owner.module.clone(),
        })?;
    let parent_name = local_generated_parent_name(owner, decl, &generated_name)?;
    Ok(MachineStdGlobalRefView::Generated {
        module: owner.module.clone(),
        parent_name,
        name: generated_name.clone(),
        export_hash: owner.expected_export_hash,
        certificate_hash: owner.expected_certificate_hash,
        parent_decl_interface_hash: decl.hashes.decl_interface_hash,
        decl_interface_hash: decl.hashes.decl_interface_hash,
        public_export: public_generated_export_exists(
            owner,
            &generated_name,
            decl.hashes.decl_interface_hash,
        ),
    })
}

fn unique_public_export<'a>(
    module: &'a MachineStdLoadedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> Option<&'a ExportEntry> {
    let mut matches = module
        .verified_module
        .export_block()
        .iter()
        .filter(|entry| {
            module
                .verified_module
                .name_table()
                .get(entry.name)
                .is_some_and(|entry_name| {
                    entry_name == name && entry.decl_interface_hash == decl_interface_hash
                })
        });
    let first = matches.next()?;
    if matches.next().is_none() {
        Some(first)
    } else {
        None
    }
}

fn public_export_exists(
    module: &MachineStdLoadedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> bool {
    unique_public_export(module, name, decl_interface_hash).is_some()
}

fn public_generated_export_exists(
    module: &MachineStdLoadedModule,
    name: &Name,
    decl_interface_hash: Hash,
) -> bool {
    unique_public_export(module, name, decl_interface_hash)
        .is_some_and(|entry| matches!(entry.kind, ExportKind::Constructor | ExportKind::Recursor))
}

fn generated_parent_for_public_export(
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> Result<(Name, Hash), MachineStdTheoremIndexError> {
    let generated_name = theorem_export_name(module, export)?;
    let mut matches = Vec::new();
    for decl in module.verified_module.declarations() {
        if decl.hashes.decl_interface_hash != export.decl_interface_hash {
            continue;
        }
        if inductive_decl_contains_generated(module, decl, &generated_name, Some(export.kind))? {
            matches.push((decl_name(module, decl)?, decl.hashes.decl_interface_hash));
        }
    }
    match matches.as_slice() {
        [result] => Ok(result.clone()),
        _ => Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: module.module.clone(),
        }),
    }
}

fn local_generated_parent_name(
    module: &MachineStdLoadedModule,
    decl: &DeclCert,
    generated_name: &Name,
) -> Result<Name, MachineStdTheoremIndexError> {
    if inductive_decl_contains_generated(module, decl, generated_name, None)? {
        decl_name(module, decl)
    } else {
        Err(MachineStdTheoremIndexError::InvalidGlobalRef {
            module: module.module.clone(),
        })
    }
}

fn inductive_decl_contains_generated(
    module: &MachineStdLoadedModule,
    decl: &DeclCert,
    generated_name: &Name,
    expected_kind: Option<ExportKind>,
) -> Result<bool, MachineStdTheoremIndexError> {
    let DeclPayload::Inductive {
        constructors,
        recursor,
        ..
    } = &decl.decl
    else {
        return Ok(false);
    };
    let constructor_allowed = expected_kind
        .map(|kind| kind == ExportKind::Constructor)
        .unwrap_or(true);
    let recursor_allowed = expected_kind
        .map(|kind| kind == ExportKind::Recursor)
        .unwrap_or(true);
    let constructor_match = constructor_allowed
        && constructors.iter().any(|constructor| {
            module
                .verified_module
                .name_table()
                .get(constructor.name)
                .is_some_and(|name| name == generated_name)
        });
    let recursor_match = recursor_allowed
        && recursor.as_ref().is_some_and(|recursor| {
            module
                .verified_module
                .name_table()
                .get(recursor.name)
                .is_some_and(|name| name == generated_name)
        });
    Ok(constructor_match || recursor_match)
}

fn decl_name(
    module: &MachineStdLoadedModule,
    decl: &DeclCert,
) -> Result<Name, MachineStdTheoremIndexError> {
    let name_id = match &decl.decl {
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
    module
        .verified_module
        .name_table()
        .get(name_id)
        .cloned()
        .ok_or_else(|| MachineStdTheoremIndexError::InvalidGlobalRef {
            module: module.module.clone(),
        })
}

fn project_export_axiom_dependencies(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> Result<Vec<MachineStdAxiomRef>, MachineStdTheoremIndexError> {
    let mut projected = BTreeMap::new();
    for axiom in &export.axiom_dependencies {
        let axiom = project_axiom_ref(loaded, owner, axiom).map_err(|_| {
            MachineStdTheoremIndexError::AxiomRefProjectionFailed {
                module: owner.module.clone(),
            }
        })?;
        let key = machine_std_axiom_ref_canonical_bytes(&axiom)
            .map_err(|source| MachineStdTheoremIndexError::CanonicalBytes { source })?;
        projected.insert(key, axiom);
    }
    Ok(projected.into_values().collect())
}

pub fn generate_machine_std_mvp_rewrite_profile_set(
    loaded: &MachineStdLoadedRelease,
) -> Result<MachineStdRewriteProfileSet, MachineStdRewriteProfileError> {
    let profiles = expected_mvp_rewrite_profile_specs()
        .into_iter()
        .map(|spec| generate_mvp_rewrite_profile(loaded, spec))
        .collect::<Result<Vec<_>, _>>()?;
    let mut profile_set = MachineStdRewriteProfileSet {
        library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
        profiles,
        rewrite_profiles_hash: [0; 32],
    };
    profile_set.rewrite_profiles_hash = machine_std_rewrite_profile_set_hash(&profile_set)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    Ok(profile_set)
}

pub fn validate_machine_std_mvp_rewrite_profile_set(
    actual: &MachineStdRewriteProfileSet,
    expected: &MachineStdRewriteProfileSet,
) -> Result<(), MachineStdRewriteProfileError> {
    validate_rewrite_profile_hashes(actual)?;
    if actual.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdRewriteProfileError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: actual.library_profile_id.clone(),
        });
    }
    validate_rewrite_profile_membership(&actual.profiles)?;

    let expected_by_id = expected
        .profiles
        .iter()
        .map(|profile| (profile.profile_id.as_str(), profile))
        .collect::<BTreeMap<_, _>>();
    for profile in &actual.profiles {
        let expected_profile = expected_by_id
            .get(profile.profile_id.as_str())
            .expect("rewrite profile membership was validated");
        validate_rewrite_descriptor_order(&profile.profile_id, &profile.descriptors)?;
        if profile.required_import_bundle_id != expected_profile.required_import_bundle_id {
            return Err(MachineStdRewriteProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "required_import_bundle_id",
            });
        }
        if profile.kernel_check_profile != expected_profile.kernel_check_profile {
            return Err(MachineStdRewriteProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "kernel_check_profile",
            });
        }
        if profile.eq_family != expected_profile.eq_family {
            return Err(MachineStdRewriteProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "eq_family",
            });
        }
        if profile.descriptors != expected_profile.descriptors {
            return Err(MachineStdRewriteProfileError::DescriptorsMismatch {
                profile_id: profile.profile_id.clone(),
            });
        }
    }

    let actual_hash = machine_std_rewrite_profile_set_hash(actual)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    if actual_hash != actual.rewrite_profiles_hash {
        return Err(MachineStdRewriteProfileError::RewriteProfilesHashMismatch {
            expected: actual.rewrite_profiles_hash,
            actual: actual_hash,
        });
    }
    if actual.rewrite_profiles_hash != expected.rewrite_profiles_hash {
        return Err(MachineStdRewriteProfileError::RewriteProfilesHashMismatch {
            expected: expected.rewrite_profiles_hash,
            actual: actual.rewrite_profiles_hash,
        });
    }
    Ok(())
}

pub fn generate_machine_std_mvp_simp_profile_set(
    loaded: &MachineStdLoadedRelease,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<MachineStdSimpProfileSet, MachineStdSimpProfileError> {
    let profiles = expected_mvp_simp_profile_specs()
        .into_iter()
        .map(|spec| generate_mvp_simp_profile(loaded, rewrite_profiles, spec))
        .collect::<Result<Vec<_>, _>>()?;
    let mut profile_set = MachineStdSimpProfileSet {
        library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
        profiles,
        simp_profiles_hash: [0; 32],
    };
    profile_set.simp_profiles_hash = machine_std_simp_profile_set_hash(&profile_set)
        .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?;
    Ok(profile_set)
}

pub fn validate_machine_std_mvp_simp_profile_set(
    actual: &MachineStdSimpProfileSet,
    expected: &MachineStdSimpProfileSet,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<(), MachineStdSimpProfileError> {
    validate_simp_profile_hashes(actual)?;
    if actual.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdSimpProfileError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: actual.library_profile_id.clone(),
        });
    }
    validate_simp_profile_membership(&actual.profiles)?;

    let expected_by_id = expected
        .profiles
        .iter()
        .map(|profile| (profile.profile_id.as_str(), profile))
        .collect::<BTreeMap<_, _>>();
    for profile in &actual.profiles {
        let expected_profile = expected_by_id
            .get(profile.profile_id.as_str())
            .expect("simp profile membership was validated");
        validate_simp_rule_order(&profile.profile_id, &profile.rules)?;
        validate_simp_rules_have_paired_descriptors(profile, rewrite_profiles)?;
        if profile.required_import_bundle_id != expected_profile.required_import_bundle_id {
            return Err(MachineStdSimpProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "required_import_bundle_id",
            });
        }
        if profile.kernel_check_profile != expected_profile.kernel_check_profile {
            return Err(MachineStdSimpProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "kernel_check_profile",
            });
        }
        if profile.eq_family != expected_profile.eq_family {
            return Err(MachineStdSimpProfileError::ProfileFieldMismatch {
                profile_id: profile.profile_id.clone(),
                field: "eq_family",
            });
        }
        if profile.rules != expected_profile.rules {
            return Err(MachineStdSimpProfileError::RulesMismatch {
                profile_id: profile.profile_id.clone(),
            });
        }
    }

    let actual_hash = machine_std_simp_profile_set_hash(actual)
        .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?;
    if actual_hash != actual.simp_profiles_hash {
        return Err(MachineStdSimpProfileError::SimpProfilesHashMismatch {
            expected: actual.simp_profiles_hash,
            actual: actual_hash,
        });
    }
    if actual.simp_profiles_hash != expected.simp_profiles_hash {
        return Err(MachineStdSimpProfileError::SimpProfilesHashMismatch {
            expected: expected.simp_profiles_hash,
            actual: actual.simp_profiles_hash,
        });
    }
    Ok(())
}

fn generate_mvp_rewrite_profile(
    loaded: &MachineStdLoadedRelease,
    spec: MvpRewriteProfileSpec,
) -> Result<MachineStdRewriteProfile, MachineStdRewriteProfileError> {
    let eq_family = std_logic_eq_family(loaded).ok_or_else(|| {
        MachineStdRewriteProfileError::MissingEqFamily {
            profile_id: spec.id.to_owned(),
        }
    })?;
    let candidates = mvp_rewrite_rule_candidates(loaded, spec)?;
    let rules = candidates
        .iter()
        .map(|candidate| candidate.rule_ref.clone())
        .collect::<Vec<_>>();
    let resolved_rules = resolve_rewrite_profile_rules(
        loaded,
        spec.id,
        spec.required_import_bundle_id,
        &eq_family,
        &rules,
    )?;
    let resolved_by_key = resolved_rules
        .into_iter()
        .map(|rule| {
            Ok((
                simp_rule_ref_canonical_bytes(&rule.key)
                    .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
                rule,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, MachineStdRewriteProfileError>>()?;
    let mut descriptors = Vec::new();
    for candidate in candidates {
        let key = simp_rule_ref_canonical_bytes(&candidate.rule_ref)
            .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
        let rule = resolved_by_key.get(&key).ok_or_else(|| {
            MachineStdRewriteProfileError::RuleValidationFailed {
                profile_id: spec.id.to_owned(),
                name: candidate.rule_ref.name.clone(),
            }
        })?;
        let owner = loaded.module(&candidate.global_ref.module).ok_or_else(|| {
            MachineStdRewriteProfileError::RuleValidationFailed {
                profile_id: spec.id.to_owned(),
                name: candidate.rule_ref.name.clone(),
            }
        })?;
        validate_resolved_rule_telescope(spec.id, &candidate.rule_ref.name, rule)?;
        let descriptor = MachineStdRewriteDescriptor {
            source: candidate.global_ref.clone(),
            direction: candidate.rule_ref.direction,
            safety: candidate.safety,
            lhs_core_hash: std_library_core_expr_hash(loaded, owner, &rule.theorem_lhs)
                .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
            rhs_core_hash: std_library_core_expr_hash(loaded, owner, &rule.theorem_rhs)
                .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
            rule_telescope_hash: machine_std_rule_telescope_hash(loaded, owner, rule)
                .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
        };
        if descriptor.safety == MachineStdRewriteSafety::SimpSafe {
            validate_simp_safe_rule(loaded, spec.id, rule, &descriptor.source)?;
        }
        descriptors.push(descriptor);
    }
    sort_rewrite_descriptors(&mut descriptors)?;
    let mut profile = MachineStdRewriteProfile {
        profile_id: spec.id.to_owned(),
        required_import_bundle_id: spec.required_import_bundle_id.to_owned(),
        kernel_check_profile: STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE.to_owned(),
        eq_family: Some(eq_family),
        descriptors,
        profile_hash: [0; 32],
    };
    profile.profile_hash = machine_std_rewrite_profile_hash(&profile)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    Ok(profile)
}

fn generate_mvp_simp_profile(
    loaded: &MachineStdLoadedRelease,
    rewrite_profiles: &MachineStdRewriteProfileSet,
    spec: MvpSimpProfileSpec,
) -> Result<MachineStdSimpProfile, MachineStdSimpProfileError> {
    let eq_family =
        std_logic_eq_family(loaded).ok_or_else(|| MachineStdSimpProfileError::MissingEqFamily {
            profile_id: spec.id.to_owned(),
        })?;
    let mut rules = mvp_simp_rule_candidates(loaded, spec)?
        .into_iter()
        .map(|candidate| candidate.rule_ref)
        .collect::<Vec<_>>();
    sort_simp_rules(&mut rules)?;
    let mut profile = MachineStdSimpProfile {
        profile_id: spec.id.to_owned(),
        required_import_bundle_id: spec.required_import_bundle_id.to_owned(),
        kernel_check_profile: STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE.to_owned(),
        eq_family: Some(eq_family),
        rules,
        profile_hash: [0; 32],
    };
    validate_simp_rules_have_paired_descriptors(&profile, rewrite_profiles)?;
    profile.profile_hash = machine_std_simp_profile_hash(&profile)
        .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?;
    Ok(profile)
}

#[derive(Clone, Copy)]
struct MvpRewriteProfileSpec {
    id: &'static str,
    required_import_bundle_id: &'static str,
    simp_safe: &'static [&'static str],
    rw_only: &'static [&'static str],
}

#[derive(Clone, Copy)]
struct MvpSimpProfileSpec {
    id: &'static str,
    required_import_bundle_id: &'static str,
    rules: &'static [&'static str],
}

#[derive(Clone)]
struct MvpRuleCandidate {
    rule_ref: SimpRuleRef,
    global_ref: MachineStdGlobalRef,
    safety: MachineStdRewriteSafety,
}

fn expected_mvp_rewrite_profile_specs() -> Vec<MvpRewriteProfileSpec> {
    vec![
        MvpRewriteProfileSpec {
            id: STD_ALL_RW_PROFILE_ID,
            required_import_bundle_id: STD_ALL_BUNDLE_ID,
            simp_safe: &[
                "Nat.add_zero",
                "Nat.add_succ",
                "Nat.zero_add",
                "Nat.mul_zero",
                "Nat.mul_succ",
                "Nat.zero_mul",
                "Nat.pred_zero",
                "Nat.pred_succ",
                "List.nil_append",
                "List.cons_append",
                "List.append_nil",
                "List.length_nil",
                "List.length_cons",
                "List.map_nil",
                "List.map_cons",
                "List.map_id",
                "List.foldr_nil",
                "List.foldr_cons",
            ],
            rw_only: &[
                "Nat.add_comm",
                "Nat.add_assoc",
                "List.append_assoc",
                "List.length_append",
            ],
        },
        MvpRewriteProfileSpec {
            id: STD_LIST_RW_PROFILE_ID,
            required_import_bundle_id: STD_LIST_BUNDLE_ID,
            simp_safe: &[
                "List.nil_append",
                "List.cons_append",
                "List.append_nil",
                "List.length_nil",
                "List.length_cons",
                "List.map_nil",
                "List.map_cons",
                "List.map_id",
                "List.foldr_nil",
                "List.foldr_cons",
            ],
            rw_only: &["List.append_assoc", "List.length_append"],
        },
        MvpRewriteProfileSpec {
            id: STD_LOGIC_RW_PROFILE_ID,
            required_import_bundle_id: STD_LOGIC_BUNDLE_ID,
            simp_safe: &[],
            rw_only: &[],
        },
        MvpRewriteProfileSpec {
            id: STD_NAT_RW_PROFILE_ID,
            required_import_bundle_id: STD_NAT_BUNDLE_ID,
            simp_safe: &[
                "Nat.add_zero",
                "Nat.add_succ",
                "Nat.zero_add",
                "Nat.mul_zero",
                "Nat.mul_succ",
                "Nat.zero_mul",
                "Nat.pred_zero",
                "Nat.pred_succ",
            ],
            rw_only: &["Nat.add_comm", "Nat.add_assoc"],
        },
    ]
}

fn expected_mvp_simp_profile_specs() -> Vec<MvpSimpProfileSpec> {
    vec![
        MvpSimpProfileSpec {
            id: STD_ALL_SIMP_PROFILE_ID,
            required_import_bundle_id: STD_ALL_BUNDLE_ID,
            rules: &[
                "Nat.add_zero",
                "Nat.add_succ",
                "Nat.zero_add",
                "Nat.mul_zero",
                "Nat.mul_succ",
                "Nat.zero_mul",
                "Nat.pred_zero",
                "Nat.pred_succ",
                "List.nil_append",
                "List.cons_append",
                "List.append_nil",
                "List.length_nil",
                "List.length_cons",
                "List.map_nil",
                "List.map_cons",
                "List.map_id",
                "List.foldr_nil",
                "List.foldr_cons",
            ],
        },
        MvpSimpProfileSpec {
            id: STD_LIST_SIMP_PROFILE_ID,
            required_import_bundle_id: STD_LIST_BUNDLE_ID,
            rules: &[
                "List.nil_append",
                "List.cons_append",
                "List.append_nil",
                "List.length_nil",
                "List.length_cons",
                "List.map_nil",
                "List.map_cons",
                "List.map_id",
                "List.foldr_nil",
                "List.foldr_cons",
            ],
        },
        MvpSimpProfileSpec {
            id: STD_LOGIC_SIMP_PROFILE_ID,
            required_import_bundle_id: STD_LOGIC_BUNDLE_ID,
            rules: &[],
        },
        MvpSimpProfileSpec {
            id: STD_NAT_SIMP_PROFILE_ID,
            required_import_bundle_id: STD_NAT_BUNDLE_ID,
            rules: &[
                "Nat.add_zero",
                "Nat.add_succ",
                "Nat.zero_add",
                "Nat.mul_zero",
                "Nat.mul_succ",
                "Nat.zero_mul",
                "Nat.pred_zero",
                "Nat.pred_succ",
            ],
        },
    ]
}

fn mvp_rewrite_rule_candidates(
    loaded: &MachineStdLoadedRelease,
    spec: MvpRewriteProfileSpec,
) -> Result<Vec<MvpRuleCandidate>, MachineStdRewriteProfileError> {
    let mut candidates = Vec::new();
    for name in spec.simp_safe {
        candidates.push(mvp_rewrite_rule_candidate(
            loaded,
            spec.id,
            spec.required_import_bundle_id,
            name,
            MachineStdRewriteSafety::SimpSafe,
        )?);
    }
    for name in spec.rw_only {
        candidates.push(mvp_rewrite_rule_candidate(
            loaded,
            spec.id,
            spec.required_import_bundle_id,
            name,
            MachineStdRewriteSafety::RwOnly,
        )?);
    }
    Ok(candidates)
}

fn mvp_simp_rule_candidates(
    loaded: &MachineStdLoadedRelease,
    spec: MvpSimpProfileSpec,
) -> Result<Vec<MvpRuleCandidate>, MachineStdSimpProfileError> {
    spec.rules
        .iter()
        .map(|name| mvp_simp_rule_candidate(loaded, spec.id, spec.required_import_bundle_id, name))
        .collect()
}

fn mvp_rewrite_rule_candidate(
    loaded: &MachineStdLoadedRelease,
    profile_id: &str,
    bundle_id: &str,
    name: &str,
    safety: MachineStdRewriteSafety,
) -> Result<MvpRuleCandidate, MachineStdRewriteProfileError> {
    let (module, export, export_name) = resolve_profile_rule_export(loaded, bundle_id, name)
        .ok_or_else(|| MachineStdRewriteProfileError::RuleResolutionFailed {
            profile_id: profile_id.to_owned(),
            name: Name::from_dotted(name),
        })?;
    if !mvp_rule_axiom_dependencies_are_allowed(loaded, bundle_id, module, export) {
        return Err(
            MachineStdRewriteProfileError::NonEmptyMvpAxiomDependencies {
                profile_id: profile_id.to_owned(),
                name: export_name,
            },
        );
    }
    Ok(MvpRuleCandidate {
        rule_ref: SimpRuleRef {
            name: export_name.clone(),
            decl_interface_hash: export.decl_interface_hash,
            direction: RewriteDirection::Forward,
        },
        global_ref: MachineStdGlobalRef {
            module: module.module.clone(),
            name: export_name,
            export_hash: module.expected_export_hash,
            certificate_hash: module.expected_certificate_hash,
            decl_interface_hash: export.decl_interface_hash,
        },
        safety,
    })
}

fn mvp_simp_rule_candidate(
    loaded: &MachineStdLoadedRelease,
    profile_id: &str,
    bundle_id: &str,
    name: &str,
) -> Result<MvpRuleCandidate, MachineStdSimpProfileError> {
    let (module, export, export_name) = resolve_profile_rule_export(loaded, bundle_id, name)
        .ok_or_else(|| MachineStdSimpProfileError::RuleResolutionFailed {
            profile_id: profile_id.to_owned(),
            name: Name::from_dotted(name),
        })?;
    if !mvp_rule_axiom_dependencies_are_allowed(loaded, bundle_id, module, export) {
        return Err(MachineStdSimpProfileError::NonEmptyMvpAxiomDependencies {
            profile_id: profile_id.to_owned(),
            name: export_name,
        });
    }
    Ok(MvpRuleCandidate {
        rule_ref: SimpRuleRef {
            name: export_name.clone(),
            decl_interface_hash: export.decl_interface_hash,
            direction: RewriteDirection::Forward,
        },
        global_ref: MachineStdGlobalRef {
            module: module.module.clone(),
            name: export_name,
            export_hash: module.expected_export_hash,
            certificate_hash: module.expected_certificate_hash,
            decl_interface_hash: export.decl_interface_hash,
        },
        safety: MachineStdRewriteSafety::SimpSafe,
    })
}

fn mvp_rule_axiom_dependencies_are_allowed(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
) -> bool {
    if export.axiom_dependencies.is_empty() {
        return true;
    }
    let Ok(dependencies) = project_export_axiom_dependencies(loaded, module, export) else {
        return false;
    };
    let Ok(allowed) = mvp_bundle_allow_axiom_wire_keys(loaded, bundle_id) else {
        return false;
    };
    dependencies.iter().all(|dependency| {
        allowed.contains(&encode_machine_axiom_ref_wire(
            &machine_std_axiom_ref_to_wire(dependency),
        ))
    })
}

fn mvp_bundle_allow_axiom_wire_keys(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
) -> Result<BTreeSet<Vec<u8>>, MachineStdImportBundleError> {
    let Some(root_modules) = root_modules_for_bundle_id(bundle_id) else {
        return Err(MachineStdImportBundleError::InvalidBundleMembership {
            expected: expected_mvp_bundle_ids(),
            actual: vec![bundle_id.to_owned()],
        });
    };
    let mut root_imports = root_modules
        .iter()
        .map(|module| import_key_for_loaded_module(loaded, &Name::from_dotted(module), bundle_id))
        .collect::<Result<Vec<_>, _>>()?;
    root_imports.sort();
    let import_closure = import_closure_for_roots(loaded, bundle_id, &root_imports)?;
    Ok(mvp_bundle_allow_axioms(loaded, &import_closure)
        .iter()
        .map(encode_machine_axiom_ref_wire)
        .collect())
}

fn resolve_profile_rule_export<'a>(
    loaded: &'a MachineStdLoadedRelease,
    bundle_id: &str,
    name: &str,
) -> Option<(&'a MachineStdLoadedModule, &'a ExportEntry, Name)> {
    let target = Name::from_dotted(name);
    let mut matches = Vec::new();
    for module_name in root_modules_for_bundle_id(bundle_id)? {
        let module = loaded.module(&Name::from_dotted(module_name))?;
        for export in module
            .verified_module
            .export_block()
            .iter()
            .filter(|export| export.kind == ExportKind::Theorem)
        {
            let export_name = module.verified_module.name_table().get(export.name)?;
            if *export_name == target {
                matches.push((module, export, export_name.clone()));
            }
        }
    }
    match matches.as_slice() {
        [single] => Some(single.clone()),
        _ => None,
    }
}

fn root_modules_for_bundle_id(bundle_id: &str) -> Option<&'static [&'static str]> {
    expected_mvp_bundle_specs()
        .into_iter()
        .find(|spec| spec.id == bundle_id)
        .map(|spec| spec.root_modules)
}

fn resolve_rewrite_profile_rules(
    loaded: &MachineStdLoadedRelease,
    profile_id: &str,
    bundle_id: &str,
    eq_family: &EqFamilyRef,
    rules: &[SimpRuleRef],
) -> Result<Vec<ResolvedSimpRule>, MachineStdRewriteProfileError> {
    let imports = tactic_imports_for_bundle(loaded, bundle_id).map_err(|name| {
        MachineStdRewriteProfileError::RuleValidationFailed {
            profile_id: profile_id.to_owned(),
            name,
        }
    })?;
    let options = MachineTacticOptions {
        simp_rules: rules.to_vec(),
        max_simp_rewrite_steps: STD_MAX_SIMP_REWRITE_STEPS,
        max_open_goals: STD_MAX_OPEN_GOALS as usize,
        max_metas: STD_MAX_METAS as usize,
        eq_family: Some(eq_family.clone()),
        nat_family: None,
    };
    let env = MachineTacticEnv::new(imports, Vec::new(), options).map_err(|_| {
        MachineStdRewriteProfileError::RuleValidationFailed {
            profile_id: profile_id.to_owned(),
            name: rules
                .first()
                .map(|rule| rule.name.clone())
                .unwrap_or_else(|| Name::from_dotted(profile_id)),
        }
    })?;
    Ok(env.simp_registry.rules)
}

fn tactic_imports_for_bundle(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
) -> Result<Vec<VerifiedImportRef>, Name> {
    let root_modules = root_modules_for_bundle_id(bundle_id)
        .ok_or_else(|| Name::from_dotted(bundle_id))?
        .iter()
        .map(Name::from_dotted)
        .collect::<BTreeSet<_>>();
    let root_imports = root_modules
        .iter()
        .map(|module| {
            import_key_for_loaded_module(loaded, module, bundle_id)
                .map_err(|_| Name::from_dotted(bundle_id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let closure = import_closure_for_roots(loaded, bundle_id, &root_imports)
        .map_err(|_| Name::from_dotted(bundle_id))?;
    let mut imports = Vec::new();
    for certificate in closure {
        let module = loaded
            .module(&certificate.module)
            .ok_or_else(|| certificate.module.clone())?;
        let import = if root_modules.contains(&certificate.module) {
            VerifiedImportRef::from_verified_module(&module.verified_module)
        } else {
            VerifiedImportRef::from_verified_module_env_only(&module.verified_module)
        }
        .map_err(|_| certificate.module.clone())?;
        imports.push(import);
    }
    Ok(imports)
}

fn validate_resolved_rule_telescope(
    profile_id: &str,
    name: &Name,
    rule: &ResolvedSimpRule,
) -> Result<(), MachineStdRewriteProfileError> {
    for param in &rule.universe_params {
        parse_machine_universe_param_name(param).map_err(|_| {
            MachineStdRewriteProfileError::InvalidUniverseParam {
                profile_id: profile_id.to_owned(),
                name: name.clone(),
                param: param.clone(),
            }
        })?;
    }
    for (index, param) in rule.rule_telescope.iter().enumerate() {
        if expr_has_bvar_at_or_above(&param.ty, index as u32) {
            return Err(MachineStdRewriteProfileError::InvalidRuleTelescope {
                profile_id: profile_id.to_owned(),
                name: name.clone(),
            });
        }
    }
    Ok(())
}

fn expr_has_bvar_at_or_above(expr: &Expr, limit: u32) -> bool {
    match expr {
        Expr::BVar(index) => *index >= limit,
        Expr::Sort(_) | Expr::Const { .. } => false,
        Expr::App(fun, arg) => {
            expr_has_bvar_at_or_above(fun, limit) || expr_has_bvar_at_or_above(arg, limit)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_has_bvar_at_or_above(ty, limit) || expr_has_bvar_at_or_above(body, limit + 1)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_has_bvar_at_or_above(ty, limit)
                || expr_has_bvar_at_or_above(value, limit)
                || expr_has_bvar_at_or_above(body, limit + 1)
        }
    }
}

fn sort_rewrite_descriptors(
    descriptors: &mut Vec<MachineStdRewriteDescriptor>,
) -> Result<(), MachineStdRewriteProfileError> {
    let mut keyed = descriptors
        .drain(..)
        .map(|descriptor| {
            Ok((
                machine_std_rewrite_descriptor_canonical_bytes(&descriptor)
                    .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
                descriptor,
            ))
        })
        .collect::<Result<Vec<_>, MachineStdRewriteProfileError>>()?;
    keyed.sort_by_cached_key(|(key, _)| key.clone());
    *descriptors = keyed
        .into_iter()
        .map(|(_, descriptor)| descriptor)
        .collect();
    Ok(())
}

fn sort_simp_rules(rules: &mut Vec<SimpRuleRef>) -> Result<(), MachineStdSimpProfileError> {
    let mut keyed = rules
        .drain(..)
        .map(|rule| {
            Ok((
                simp_rule_ref_canonical_bytes(&rule)
                    .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?,
                rule,
            ))
        })
        .collect::<Result<Vec<_>, MachineStdSimpProfileError>>()?;
    keyed.sort_by_cached_key(|(key, _)| key.clone());
    keyed.dedup_by(|lhs, rhs| lhs.0 == rhs.0);
    *rules = keyed.into_iter().map(|(_, rule)| rule).collect();
    Ok(())
}

fn validate_simp_safe_rule(
    loaded: &MachineStdLoadedRelease,
    profile_id: &str,
    rule: &ResolvedSimpRule,
    source: &MachineStdGlobalRef,
) -> Result<(), MachineStdRewriteProfileError> {
    let owner = loaded.module(&source.module).ok_or_else(|| {
        MachineStdRewriteProfileError::RuleValidationFailed {
            profile_id: profile_id.to_owned(),
            name: rule.key.name.clone(),
        }
    })?;
    if rule.key.direction != RewriteDirection::Forward {
        return Err(MachineStdRewriteProfileError::SimpSafeLintFailed {
            profile_id: profile_id.to_owned(),
            name: rule.key.name.clone(),
        });
    }
    let lhs_hash = std_library_core_expr_hash(loaded, owner, &rule.from_pattern)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    let rhs_hash = std_library_core_expr_hash(loaded, owner, &rule.to_pattern)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    if lhs_hash == rhs_hash {
        return Err(MachineStdRewriteProfileError::SimpSafeLintFailed {
            profile_id: profile_id.to_owned(),
            name: rule.key.name.clone(),
        });
    }
    if !simp_size_exception(loaded, source)
        && syntactic_expr_size(&rule.from_pattern) < syntactic_expr_size(&rule.to_pattern)
    {
        return Err(MachineStdRewriteProfileError::SimpSafeLintFailed {
            profile_id: profile_id.to_owned(),
            name: rule.key.name.clone(),
        });
    }
    if variable_only_lhs(&rule.from_pattern)
        || is_commutativity_rule(loaded, owner, &rule.from_pattern, &rule.to_pattern)?
        || is_associativity_rule(loaded, owner, &rule.from_pattern, &rule.to_pattern)?
        || introduces_disallowed_heads(loaded, source, &rule.from_pattern, &rule.to_pattern)?
    {
        return Err(MachineStdRewriteProfileError::SimpSafeLintFailed {
            profile_id: profile_id.to_owned(),
            name: rule.key.name.clone(),
        });
    }
    Ok(())
}

fn simp_size_exception(loaded: &MachineStdLoadedRelease, source: &MachineStdGlobalRef) -> bool {
    mvp_source_matches_public_theorem(loaded, source, "Std.Nat", "Nat.mul_succ")
        || mvp_source_matches_public_theorem(loaded, source, "Std.List", "List.map_cons")
        || mvp_source_matches_public_theorem(loaded, source, "Std.List", "List.foldr_cons")
}

fn syntactic_expr_size(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => 1,
        Expr::App(fun, arg) => 1 + syntactic_expr_size(fun) + syntactic_expr_size(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            1 + syntactic_expr_size(ty) + syntactic_expr_size(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => 1 + syntactic_expr_size(ty) + syntactic_expr_size(value) + syntactic_expr_size(body),
    }
}

fn variable_only_lhs(expr: &Expr) -> bool {
    matches!(flatten_expr_app(expr).0, Expr::BVar(_))
}

fn flatten_expr_app(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(fun, arg) = head {
        args.push((**arg).clone());
        head = fun;
    }
    args.reverse();
    (head.clone(), args)
}

fn is_commutativity_rule(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<bool, MachineStdRewriteProfileError> {
    if !same_head_and_prefix(loaded, owner, lhs, rhs)? {
        return Ok(false);
    }
    let (_, lhs_args) = flatten_expr_app(lhs);
    let (_, rhs_args) = flatten_expr_app(rhs);
    let prefix_len = lhs_args.len() - 2;
    Ok(same_expr(
        loaded,
        owner,
        &lhs_args[prefix_len],
        &rhs_args[prefix_len + 1],
    )? && same_expr(
        loaded,
        owner,
        &lhs_args[prefix_len + 1],
        &rhs_args[prefix_len],
    )?)
}

fn is_associativity_rule(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<bool, MachineStdRewriteProfileError> {
    if !same_head_and_prefix(loaded, owner, lhs, rhs)? {
        return Ok(false);
    }
    let (head, args) = flatten_expr_app(lhs);
    let prefix = &args[..args.len() - 2];
    if let Some((x1, y1, z1)) = left_assoc_shape(loaded, owner, lhs, &head, prefix)? {
        if let Some((x2, y2, z2)) = right_assoc_shape(loaded, owner, rhs, &head, prefix)? {
            return Ok(same_expr(loaded, owner, &x1, &x2)?
                && same_expr(loaded, owner, &y1, &y2)?
                && same_expr(loaded, owner, &z1, &z2)?);
        }
    }
    if let Some((x1, y1, z1)) = right_assoc_shape(loaded, owner, lhs, &head, prefix)? {
        if let Some((x2, y2, z2)) = left_assoc_shape(loaded, owner, rhs, &head, prefix)? {
            return Ok(same_expr(loaded, owner, &x1, &x2)?
                && same_expr(loaded, owner, &y1, &y2)?
                && same_expr(loaded, owner, &z1, &z2)?);
        }
    }
    Ok(false)
}

fn same_head_and_prefix(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<bool, MachineStdRewriteProfileError> {
    let (lhs_head, lhs_args) = flatten_expr_app(lhs);
    let (rhs_head, rhs_args) = flatten_expr_app(rhs);
    if lhs_args.len() != rhs_args.len()
        || lhs_args.len() < 2
        || !same_expr(loaded, owner, &lhs_head, &rhs_head)?
    {
        return Ok(false);
    }
    let prefix_len = lhs_args.len() - 2;
    for index in 0..prefix_len {
        if !same_expr(loaded, owner, &lhs_args[index], &rhs_args[index])? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn left_assoc_shape(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
    expected_head: &Expr,
    prefix: &[Expr],
) -> Result<Option<(Expr, Expr, Expr)>, MachineStdRewriteProfileError> {
    let (outer_head, outer_args) = flatten_expr_app(expr);
    if !same_expr(loaded, owner, &outer_head, expected_head)?
        || outer_args.len() != prefix.len() + 2
    {
        return Ok(None);
    }
    for (actual, expected) in outer_args.iter().zip(prefix) {
        if !same_expr(loaded, owner, actual, expected)? {
            return Ok(None);
        }
    }
    let inner = &outer_args[prefix.len()];
    let z = outer_args[prefix.len() + 1].clone();
    let (inner_head, inner_args) = flatten_expr_app(inner);
    if !same_expr(loaded, owner, &inner_head, expected_head)?
        || inner_args.len() != prefix.len() + 2
    {
        return Ok(None);
    }
    for (actual, expected) in inner_args.iter().zip(prefix) {
        if !same_expr(loaded, owner, actual, expected)? {
            return Ok(None);
        }
    }
    Ok(Some((
        inner_args[prefix.len()].clone(),
        inner_args[prefix.len() + 1].clone(),
        z,
    )))
}

fn right_assoc_shape(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
    expected_head: &Expr,
    prefix: &[Expr],
) -> Result<Option<(Expr, Expr, Expr)>, MachineStdRewriteProfileError> {
    let (outer_head, outer_args) = flatten_expr_app(expr);
    if !same_expr(loaded, owner, &outer_head, expected_head)?
        || outer_args.len() != prefix.len() + 2
    {
        return Ok(None);
    }
    for (actual, expected) in outer_args.iter().zip(prefix) {
        if !same_expr(loaded, owner, actual, expected)? {
            return Ok(None);
        }
    }
    let x = outer_args[prefix.len()].clone();
    let inner = &outer_args[prefix.len() + 1];
    let (inner_head, inner_args) = flatten_expr_app(inner);
    if !same_expr(loaded, owner, &inner_head, expected_head)?
        || inner_args.len() != prefix.len() + 2
    {
        return Ok(None);
    }
    for (actual, expected) in inner_args.iter().zip(prefix) {
        if !same_expr(loaded, owner, actual, expected)? {
            return Ok(None);
        }
    }
    Ok(Some((
        x,
        inner_args[prefix.len()].clone(),
        inner_args[prefix.len() + 1].clone(),
    )))
}

fn same_expr(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<bool, MachineStdRewriteProfileError> {
    let lhs = std_library_core_expr_canonical_bytes(loaded, owner, lhs)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    let rhs = std_library_core_expr_canonical_bytes(loaded, owner, rhs)
        .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
    Ok(lhs == rhs)
}

fn introduces_disallowed_heads(
    loaded: &MachineStdLoadedRelease,
    source: &MachineStdGlobalRef,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<bool, MachineStdRewriteProfileError> {
    let Some(owner) = loaded.module(&source.module) else {
        return Ok(true);
    };
    let lhs_heads = expr_head_set(loaded, owner, lhs)?;
    let rhs_heads = expr_head_set(loaded, owner, rhs)?;
    let introduced = rhs_heads
        .keys()
        .filter(|key| !lhs_heads.contains_key(*key))
        .cloned()
        .collect::<BTreeSet<_>>();
    if introduced.is_empty() {
        return Ok(false);
    }
    let allowed = allowed_intro_heads(loaded, source)?;
    Ok(!introduced.iter().all(|key| allowed.contains(key)))
}

fn expr_head_set(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
) -> Result<BTreeMap<Vec<u8>, MachineStdGlobalRefView>, MachineStdRewriteProfileError> {
    let mut heads = BTreeMap::new();
    collect_expr_heads(loaded, owner, expr, &mut heads)?;
    Ok(heads)
}

fn collect_expr_heads(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
    heads: &mut BTreeMap<Vec<u8>, MachineStdGlobalRefView>,
) -> Result<(), MachineStdRewriteProfileError> {
    match expr {
        Expr::Const { name, .. } => {
            if let Some(view) = normalize_expr_const_global_ref_view(loaded, owner, name)? {
                let key = machine_std_global_ref_view_canonical_bytes(&view)
                    .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
                heads.insert(key, view);
            }
            Ok(())
        }
        Expr::Sort(_) | Expr::BVar(_) => Ok(()),
        Expr::App(fun, arg) => {
            collect_expr_heads(loaded, owner, fun, heads)?;
            collect_expr_heads(loaded, owner, arg, heads)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_expr_heads(loaded, owner, ty, heads)?;
            collect_expr_heads(loaded, owner, body, heads)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_expr_heads(loaded, owner, ty, heads)?;
            collect_expr_heads(loaded, owner, value, heads)?;
            collect_expr_heads(loaded, owner, body, heads)
        }
    }
}

fn normalize_expr_const_global_ref_view(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    name: &str,
) -> Result<Option<MachineStdGlobalRefView>, MachineStdRewriteProfileError> {
    let name = Name::from_dotted(name);
    for (decl_index, decl) in owner.verified_module.declarations().iter().enumerate() {
        if std_library_decl_name(owner, decl).as_ref() == Some(&name) {
            return Ok(Some(
                normalize_local_global_ref_view(owner, decl_index).map_err(|source| {
                    MachineStdRewriteProfileError::RuleValidationFailed {
                        profile_id: owner.module.as_dotted(),
                        name: match source {
                            MachineStdTheoremIndexError::InvalidGlobalRef { module } => module,
                            _ => name.clone(),
                        },
                    }
                })?,
            ));
        }
        if inductive_decl_contains_generated(owner, decl, &name, None).unwrap_or(false) {
            let name_id = std_library_name_id(owner, &name)
                .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
            return Ok(Some(
                normalize_local_generated_global_ref_view(owner, decl_index, name_id).map_err(
                    |source| MachineStdRewriteProfileError::RuleValidationFailed {
                        profile_id: owner.module.as_dotted(),
                        name: match source {
                            MachineStdTheoremIndexError::InvalidGlobalRef { module } => module,
                            _ => name.clone(),
                        },
                    },
                )?,
            ));
        }
    }
    for import in &owner.imports {
        let Some(imported) = loaded.module(&import.module) else {
            continue;
        };
        if let Some(export) = unique_public_export_by_name(imported, &name) {
            return Ok(Some(
                export_to_global_ref_view(imported, export, true).map_err(|source| {
                    MachineStdRewriteProfileError::RuleValidationFailed {
                        profile_id: owner.module.as_dotted(),
                        name: match source {
                            MachineStdTheoremIndexError::InvalidGlobalRef { module } => module,
                            _ => name.clone(),
                        },
                    }
                })?,
            ));
        }
    }
    Ok(None)
}

fn unique_public_export_by_name<'a>(
    module: &'a MachineStdLoadedModule,
    name: &Name,
) -> Option<&'a ExportEntry> {
    let mut matches = module
        .verified_module
        .export_block()
        .iter()
        .filter(|entry| {
            module
                .verified_module
                .name_table()
                .get(entry.name)
                .is_some_and(|entry_name| entry_name == name)
        });
    let first = matches.next()?;
    if matches.next().is_none() {
        Some(first)
    } else {
        None
    }
}

fn export_to_global_ref_view(
    module: &MachineStdLoadedModule,
    export: &ExportEntry,
    public_export: bool,
) -> Result<MachineStdGlobalRefView, MachineStdTheoremIndexError> {
    let name = theorem_export_name(module, export)?;
    match export.kind {
        ExportKind::Constructor | ExportKind::Recursor => {
            let (parent_name, parent_decl_interface_hash) =
                generated_parent_for_public_export(module, export)?;
            Ok(MachineStdGlobalRefView::Generated {
                module: module.module.clone(),
                parent_name,
                name,
                export_hash: module.expected_export_hash,
                certificate_hash: module.expected_certificate_hash,
                parent_decl_interface_hash,
                decl_interface_hash: export.decl_interface_hash,
                public_export,
            })
        }
        _ => Ok(MachineStdGlobalRefView::Decl {
            module: module.module.clone(),
            name,
            export_hash: module.expected_export_hash,
            certificate_hash: module.expected_certificate_hash,
            decl_interface_hash: export.decl_interface_hash,
            public_export,
        }),
    }
}

fn allowed_intro_heads(
    loaded: &MachineStdLoadedRelease,
    source: &MachineStdGlobalRef,
) -> Result<BTreeSet<Vec<u8>>, MachineStdRewriteProfileError> {
    let labels: &[(&str, &str)] =
        if mvp_source_matches_public_theorem(loaded, source, "Std.Nat", "Nat.mul_succ") {
            &[("Std.Nat", "Nat.add")]
        } else if mvp_source_matches_public_theorem(loaded, source, "Std.List", "List.cons_append")
        {
            &[("Std.List", "List.cons")]
        } else if mvp_source_matches_public_theorem(loaded, source, "Std.List", "List.length_nil") {
            &[("Std.Nat", "Nat.zero")]
        } else if mvp_source_matches_public_theorem(loaded, source, "Std.List", "List.length_cons")
        {
            &[("Std.Nat", "Nat.succ")]
        } else {
            &[]
        };
    let mut out = BTreeSet::new();
    for (module_name, label) in labels {
        let name = Name::from_dotted(label);
        let Some(module) = loaded.module(&Name::from_dotted(module_name)) else {
            return Ok(BTreeSet::new());
        };
        let Some(export) = unique_public_export_by_name(module, &name) else {
            return Ok(BTreeSet::new());
        };
        let view = export_to_global_ref_view(module, export, true).map_err(|_| {
            MachineStdRewriteProfileError::RuleValidationFailed {
                profile_id: source.module.as_dotted(),
                name: source.name.clone(),
            }
        })?;
        out.insert(
            machine_std_global_ref_view_canonical_bytes(&view)
                .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?,
        );
    }
    Ok(out)
}

fn mvp_source_matches_public_theorem(
    loaded: &MachineStdLoadedRelease,
    source: &MachineStdGlobalRef,
    module_name: &str,
    theorem_name: &str,
) -> bool {
    let module_name = Name::from_dotted(module_name);
    if source.module != module_name {
        return false;
    }
    let Some(module) = loaded.module(&module_name) else {
        return false;
    };
    let theorem_name = Name::from_dotted(theorem_name);
    if source.name != theorem_name {
        return false;
    }
    let Some(export) = unique_public_export_by_name(module, &theorem_name) else {
        return false;
    };
    export.kind == ExportKind::Theorem
        && source.export_hash == module.expected_export_hash
        && source.certificate_hash == module.expected_certificate_hash
        && source.decl_interface_hash == export.decl_interface_hash
}

fn validate_rewrite_profile_hashes(
    profile_set: &MachineStdRewriteProfileSet,
) -> Result<(), MachineStdRewriteProfileError> {
    for profile in &profile_set.profiles {
        let actual = machine_std_rewrite_profile_hash(profile)
            .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
        if actual != profile.profile_hash {
            return Err(MachineStdRewriteProfileError::ProfileHashMismatch {
                profile_id: profile.profile_id.clone(),
                expected: profile.profile_hash,
                actual,
            });
        }
    }
    Ok(())
}

fn validate_simp_profile_hashes(
    profile_set: &MachineStdSimpProfileSet,
) -> Result<(), MachineStdSimpProfileError> {
    for profile in &profile_set.profiles {
        let actual = machine_std_simp_profile_hash(profile)
            .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?;
        if actual != profile.profile_hash {
            return Err(MachineStdSimpProfileError::ProfileHashMismatch {
                profile_id: profile.profile_id.clone(),
                expected: profile.profile_hash,
                actual,
            });
        }
    }
    Ok(())
}

fn validate_rewrite_profile_membership(
    profiles: &[MachineStdRewriteProfile],
) -> Result<(), MachineStdRewriteProfileError> {
    let expected = expected_mvp_rewrite_profile_ids();
    let actual = profiles
        .iter()
        .map(|profile| profile.profile_id.clone())
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for profile_id in &actual {
        if !seen.insert(profile_id.clone()) {
            return Err(MachineStdRewriteProfileError::DuplicateProfile {
                profile_id: profile_id.clone(),
            });
        }
    }
    if expected.iter().cloned().collect::<BTreeSet<_>>()
        != actual.iter().cloned().collect::<BTreeSet<_>>()
    {
        return Err(MachineStdRewriteProfileError::InvalidProfileMembership { expected, actual });
    }
    if expected != actual {
        return Err(MachineStdRewriteProfileError::NonCanonicalProfileOrder { expected, actual });
    }
    Ok(())
}

fn validate_simp_profile_membership(
    profiles: &[MachineStdSimpProfile],
) -> Result<(), MachineStdSimpProfileError> {
    let expected = expected_mvp_simp_profile_ids();
    let actual = profiles
        .iter()
        .map(|profile| profile.profile_id.clone())
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for profile_id in &actual {
        if !seen.insert(profile_id.clone()) {
            return Err(MachineStdSimpProfileError::DuplicateProfile {
                profile_id: profile_id.clone(),
            });
        }
    }
    if expected.iter().cloned().collect::<BTreeSet<_>>()
        != actual.iter().cloned().collect::<BTreeSet<_>>()
    {
        return Err(MachineStdSimpProfileError::InvalidProfileMembership { expected, actual });
    }
    if expected != actual {
        return Err(MachineStdSimpProfileError::NonCanonicalProfileOrder { expected, actual });
    }
    Ok(())
}

fn expected_mvp_rewrite_profile_ids() -> Vec<String> {
    expected_mvp_rewrite_profile_specs()
        .into_iter()
        .map(|spec| spec.id.to_owned())
        .collect()
}

fn expected_mvp_simp_profile_ids() -> Vec<String> {
    expected_mvp_simp_profile_specs()
        .into_iter()
        .map(|spec| spec.id.to_owned())
        .collect()
}

fn validate_rewrite_descriptor_order(
    profile_id: &str,
    descriptors: &[MachineStdRewriteDescriptor],
) -> Result<(), MachineStdRewriteProfileError> {
    let mut previous: Option<Vec<u8>> = None;
    for descriptor in descriptors {
        let current = machine_std_rewrite_descriptor_canonical_bytes(descriptor)
            .map_err(|source| MachineStdRewriteProfileError::CanonicalBytes { source })?;
        if let Some(previous) = previous.as_ref() {
            if previous == &current {
                return Err(MachineStdRewriteProfileError::DuplicateDescriptor {
                    profile_id: profile_id.to_owned(),
                });
            }
            if previous > &current {
                return Err(MachineStdRewriteProfileError::NonCanonicalDescriptorOrder {
                    profile_id: profile_id.to_owned(),
                });
            }
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_simp_rule_order(
    profile_id: &str,
    rules: &[SimpRuleRef],
) -> Result<(), MachineStdSimpProfileError> {
    let mut previous: Option<Vec<u8>> = None;
    for rule in rules {
        let current = simp_rule_ref_canonical_bytes(rule)
            .map_err(|source| MachineStdSimpProfileError::CanonicalBytes { source })?;
        if let Some(previous) = previous.as_ref() {
            if previous == &current {
                return Err(MachineStdSimpProfileError::DuplicateRule {
                    profile_id: profile_id.to_owned(),
                });
            }
            if previous > &current {
                return Err(MachineStdSimpProfileError::NonCanonicalRuleOrder {
                    profile_id: profile_id.to_owned(),
                });
            }
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_simp_rules_have_paired_descriptors(
    profile: &MachineStdSimpProfile,
    rewrite_profiles: &MachineStdRewriteProfileSet,
) -> Result<(), MachineStdSimpProfileError> {
    let paired_id = paired_rewrite_profile_id(&profile.profile_id).ok_or_else(|| {
        MachineStdSimpProfileError::ProfileFieldMismatch {
            profile_id: profile.profile_id.clone(),
            field: "profile_id",
        }
    })?;
    let paired = rewrite_profiles
        .profiles
        .iter()
        .find(|rewrite| rewrite.profile_id == paired_id)
        .ok_or_else(|| MachineStdSimpProfileError::MissingSimpSafeDescriptor {
            profile_id: profile.profile_id.clone(),
            name: Name::from_dotted(paired_id),
        })?;
    for rule in &profile.rules {
        let found = paired.descriptors.iter().any(|descriptor| {
            descriptor.safety == MachineStdRewriteSafety::SimpSafe
                && descriptor.direction == rule.direction
                && descriptor.source.name == rule.name
                && descriptor.source.decl_interface_hash == rule.decl_interface_hash
        });
        if !found {
            return Err(MachineStdSimpProfileError::MissingSimpSafeDescriptor {
                profile_id: profile.profile_id.clone(),
                name: rule.name.clone(),
            });
        }
    }
    Ok(())
}

fn paired_rewrite_profile_id(simp_profile_id: &str) -> Option<&'static str> {
    match simp_profile_id {
        STD_LOGIC_SIMP_PROFILE_ID => Some(STD_LOGIC_RW_PROFILE_ID),
        STD_NAT_SIMP_PROFILE_ID => Some(STD_NAT_RW_PROFILE_ID),
        STD_LIST_SIMP_PROFILE_ID => Some(STD_LIST_RW_PROFILE_ID),
        STD_ALL_SIMP_PROFILE_ID => Some(STD_ALL_RW_PROFILE_ID),
        _ => None,
    }
}

pub fn generate_machine_std_mvp_import_bundle_set(
    loaded: &MachineStdLoadedRelease,
) -> Result<MachineStdImportBundleSet, MachineStdImportBundleError> {
    let mut bundle_set = MachineStdImportBundleSet {
        library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
        bundles: expected_mvp_bundle_specs()
            .into_iter()
            .map(|spec| generate_mvp_import_bundle(loaded, spec))
            .collect::<Result<Vec<_>, _>>()?,
        import_bundles_hash: [0; 32],
    };
    bundle_set.import_bundles_hash = machine_std_import_bundle_set_hash(&bundle_set)
        .map_err(|source| MachineStdImportBundleError::CanonicalBytes { source })?;
    Ok(bundle_set)
}

pub fn generate_machine_std_mvp_final_import_bundle_set(
    loaded: &MachineStdLoadedRelease,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<MachineStdImportBundleSet, MachineStdImportBundleError> {
    let bundle_set = generate_machine_std_mvp_import_bundle_set(loaded)?;
    finalize_machine_std_mvp_import_bundle_recipes(loaded, bundle_set, simp_profiles)
}

pub fn finalize_machine_std_mvp_import_bundle_recipes(
    loaded: &MachineStdLoadedRelease,
    mut bundle_set: MachineStdImportBundleSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<MachineStdImportBundleSet, MachineStdImportBundleError> {
    for bundle in &mut bundle_set.bundles {
        let profile = recipe_simp_profile_for_bundle(&bundle.bundle_id, simp_profiles)?;
        bundle.recommended_tactic_options =
            expected_final_recipe_for_bundle(loaded, &bundle.bundle_id, profile)?;
    }
    bundle_set.import_bundles_hash = machine_std_import_bundle_set_hash(&bundle_set)
        .map_err(|source| MachineStdImportBundleError::CanonicalBytes { source })?;
    validate_machine_std_mvp_import_bundle_recipes(loaded, &bundle_set, simp_profiles)?;
    Ok(bundle_set)
}

pub fn validate_machine_std_mvp_import_bundle_set(
    actual: &MachineStdImportBundleSet,
    expected: &MachineStdImportBundleSet,
) -> Result<(), MachineStdImportBundleError> {
    validate_machine_std_mvp_import_bundle_set_shape(actual, expected)?;
    validate_import_bundle_set_expected_hash(actual, expected)
}

fn validate_machine_std_mvp_import_bundle_set_shape(
    actual: &MachineStdImportBundleSet,
    expected: &MachineStdImportBundleSet,
) -> Result<(), MachineStdImportBundleError> {
    let actual_hash = machine_std_import_bundle_set_hash(actual)
        .map_err(|source| MachineStdImportBundleError::CanonicalBytes { source })?;
    if actual_hash != actual.import_bundles_hash {
        return Err(MachineStdImportBundleError::ImportBundlesHashMismatch {
            expected: actual.import_bundles_hash,
            actual: actual_hash,
        });
    }
    if actual.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdImportBundleError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: actual.library_profile_id.clone(),
        });
    }
    validate_import_bundle_membership(&actual.bundles)?;

    let expected_by_id = expected
        .bundles
        .iter()
        .map(|bundle| (bundle.bundle_id.as_str(), bundle))
        .collect::<BTreeMap<_, _>>();

    for bundle in &actual.bundles {
        let expected_bundle = expected_by_id
            .get(bundle.bundle_id.as_str())
            .expect("bundle membership was validated");
        validate_import_key_order(&bundle.bundle_id, &bundle.root_imports)?;
        validate_import_certificate_order(&bundle.bundle_id, &bundle.import_closure)?;
        let actual_closure_keys = bundle
            .import_closure
            .iter()
            .map(import_certificate_key)
            .collect::<Vec<_>>();
        let expected_closure_keys = expected_bundle
            .import_closure
            .iter()
            .map(import_certificate_key)
            .collect::<Vec<_>>();
        if bundle.root_imports != expected_bundle.root_imports {
            return Err(MachineStdImportBundleError::RootImportsMismatch {
                bundle_id: bundle.bundle_id.clone(),
                expected: expected_bundle.root_imports.clone(),
                actual: bundle.root_imports.clone(),
            });
        }
        if actual_closure_keys != expected_closure_keys {
            return Err(MachineStdImportBundleError::ImportClosureMismatch {
                bundle_id: bundle.bundle_id.clone(),
                expected: expected_closure_keys,
                actual: actual_closure_keys,
            });
        }
        for (actual_certificate, expected_certificate) in bundle
            .import_closure
            .iter()
            .zip(&expected_bundle.import_closure)
        {
            validate_import_certificate_bytes(
                &bundle.bundle_id,
                actual_certificate,
                expected_certificate,
            )?;
        }
        validate_allow_axiom_order(&bundle.bundle_id, &bundle.allow_axioms)?;
        if bundle.allow_axioms != expected_bundle.allow_axioms {
            return Err(MachineStdImportBundleError::AllowAxiomsMismatch {
                bundle_id: bundle.bundle_id.clone(),
                expected: expected_bundle.allow_axioms.clone(),
                actual: bundle.allow_axioms.clone(),
            });
        }
        let expected_recipe_id = expected_recipe_id_for_bundle(&bundle.bundle_id)
            .expect("bundle membership was validated");
        if bundle.recommended_tactic_options.recipe_id != expected_recipe_id {
            return Err(MachineStdImportBundleError::InvalidRecipeIdMapping {
                bundle_id: bundle.bundle_id.clone(),
                expected: expected_recipe_id,
                actual: bundle.recommended_tactic_options.recipe_id.clone(),
            });
        }
    }
    Ok(())
}

fn validate_import_bundle_set_expected_hash(
    actual: &MachineStdImportBundleSet,
    expected: &MachineStdImportBundleSet,
) -> Result<(), MachineStdImportBundleError> {
    if actual.import_bundles_hash != expected.import_bundles_hash {
        return Err(MachineStdImportBundleError::ImportBundlesHashMismatch {
            expected: expected.import_bundles_hash,
            actual: actual.import_bundles_hash,
        });
    }
    Ok(())
}

pub fn validate_machine_std_mvp_import_bundle_recipes(
    loaded: &MachineStdLoadedRelease,
    bundle_set: &MachineStdImportBundleSet,
    simp_profiles: &MachineStdSimpProfileSet,
) -> Result<(), MachineStdImportBundleError> {
    for bundle in &bundle_set.bundles {
        validate_recipe_machine_api_handoff(bundle)?;
        let profile = recipe_simp_profile_for_bundle(&bundle.bundle_id, simp_profiles)?;
        let expected_recipe = expected_final_recipe_for_bundle(loaded, &bundle.bundle_id, profile)?;
        validate_final_recipe_shape(
            bundle,
            profile,
            &bundle.recommended_tactic_options,
            &expected_recipe,
        )?;
    }
    Ok(())
}

pub fn machine_std_tactic_options_recipe_request(
    recipe: &MachineStdTacticOptionsRecipe,
) -> MachineTacticOptionsRequest {
    MachineTacticOptionsRequest {
        simp_rules: recipe.simp_rules.clone(),
        eq_family: recipe.eq_family.clone(),
        nat_family: recipe.nat_family.clone(),
        max_simp_rewrite_steps: recipe.max_simp_rewrite_steps,
        max_open_goals: recipe.max_open_goals,
        max_metas: recipe.max_metas,
    }
}

fn generate_mvp_import_bundle(
    loaded: &MachineStdLoadedRelease,
    spec: MvpBundleSpec,
) -> Result<MachineStdImportBundle, MachineStdImportBundleError> {
    let mut root_imports = spec
        .root_modules
        .iter()
        .map(|module| import_key_for_loaded_module(loaded, &Name::from_dotted(module), spec.id))
        .collect::<Result<Vec<_>, _>>()?;
    root_imports.sort();
    let import_closure = import_closure_for_roots(loaded, spec.id, &root_imports)?;
    let allow_axioms = mvp_bundle_allow_axioms(loaded, &import_closure);
    Ok(MachineStdImportBundle {
        bundle_id: spec.id.to_owned(),
        root_imports,
        import_closure,
        allow_axioms,
        recommended_tactic_options: MachineStdTacticOptionsRecipe {
            recipe_id: spec.recipe_id.to_owned(),
            kernel_check_profile: KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC.to_owned(),
            simp_rules: Vec::new(),
            eq_family: std_logic_eq_family(loaded),
            nat_family: expected_nat_family_for_bundle(loaded, spec.id)?,
            max_simp_rewrite_steps: STD_MAX_SIMP_REWRITE_STEPS,
            max_open_goals: STD_MAX_OPEN_GOALS,
            max_metas: STD_MAX_METAS,
        },
    })
}

fn recipe_simp_profile_for_bundle<'a>(
    bundle_id: &str,
    simp_profiles: &'a MachineStdSimpProfileSet,
) -> Result<&'a MachineStdSimpProfile, MachineStdImportBundleError> {
    let Some(profile_id) = expected_simp_profile_id_for_bundle(bundle_id) else {
        return Err(MachineStdImportBundleError::InvalidBundleMembership {
            expected: expected_mvp_bundle_ids(),
            actual: vec![bundle_id.to_owned()],
        });
    };
    simp_profiles
        .profiles
        .iter()
        .find(|profile| profile.profile_id == profile_id)
        .ok_or_else(|| MachineStdImportBundleError::MissingRecipeSimpProfile {
            bundle_id: bundle_id.to_owned(),
            profile_id,
        })
}

fn expected_final_recipe_for_bundle(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
    profile: &MachineStdSimpProfile,
) -> Result<MachineStdTacticOptionsRecipe, MachineStdImportBundleError> {
    let Some(recipe_id) = expected_recipe_id_for_bundle(bundle_id) else {
        return Err(MachineStdImportBundleError::InvalidBundleMembership {
            expected: expected_mvp_bundle_ids(),
            actual: vec![bundle_id.to_owned()],
        });
    };
    let eq_family = std_logic_eq_family(loaded).ok_or_else(|| {
        MachineStdImportBundleError::MissingEqFamily {
            bundle_id: bundle_id.to_owned(),
        }
    })?;
    Ok(MachineStdTacticOptionsRecipe {
        recipe_id: recipe_id.to_owned(),
        kernel_check_profile: STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE.to_owned(),
        simp_rules: profile.rules.clone(),
        eq_family: Some(eq_family),
        nat_family: expected_nat_family_for_bundle(loaded, bundle_id)?,
        max_simp_rewrite_steps: STD_MAX_SIMP_REWRITE_STEPS,
        max_open_goals: STD_MAX_OPEN_GOALS,
        max_metas: STD_MAX_METAS,
    })
}

fn expected_nat_family_for_bundle(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
) -> Result<Option<NatFamilyRef>, MachineStdImportBundleError> {
    let Some(root_modules) = root_modules_for_bundle_id(bundle_id) else {
        return Err(MachineStdImportBundleError::InvalidBundleMembership {
            expected: expected_mvp_bundle_ids(),
            actual: vec![bundle_id.to_owned()],
        });
    };
    if !root_modules.contains(&"Std.Nat") {
        return Ok(None);
    }
    std_nat_family(loaded)
        .map(Some)
        .ok_or_else(|| MachineStdImportBundleError::MissingNatFamily {
            bundle_id: bundle_id.to_owned(),
        })
}

fn validate_final_recipe_shape(
    bundle: &MachineStdImportBundle,
    profile: &MachineStdSimpProfile,
    actual: &MachineStdTacticOptionsRecipe,
    expected: &MachineStdTacticOptionsRecipe,
) -> Result<(), MachineStdImportBundleError> {
    if actual.recipe_id != expected.recipe_id {
        let expected_recipe_id = expected_recipe_id_for_bundle(&bundle.bundle_id)
            .expect("bundle membership is validated before recipe validation");
        return Err(MachineStdImportBundleError::InvalidRecipeIdMapping {
            bundle_id: bundle.bundle_id.clone(),
            expected: expected_recipe_id,
            actual: actual.recipe_id.clone(),
        });
    }
    if actual.kernel_check_profile != expected.kernel_check_profile {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "kernel_check_profile",
        });
    }
    if actual.simp_rules != expected.simp_rules {
        return Err(MachineStdImportBundleError::RecipeSimpRulesMismatch {
            bundle_id: bundle.bundle_id.clone(),
            profile_id: profile.profile_id.clone(),
        });
    }
    if actual.eq_family != expected.eq_family {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "eq_family",
        });
    }
    if actual.nat_family != expected.nat_family {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "nat_family",
        });
    }
    if actual.max_simp_rewrite_steps != expected.max_simp_rewrite_steps {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "max_simp_rewrite_steps",
        });
    }
    if actual.max_open_goals != expected.max_open_goals {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "max_open_goals",
        });
    }
    if actual.max_metas != expected.max_metas {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "max_metas",
        });
    }
    Ok(())
}

fn validate_recipe_machine_api_handoff(
    bundle: &MachineStdImportBundle,
) -> Result<(), MachineStdImportBundleError> {
    let import_context = import_bundle_certificate_context(bundle)?;
    let kernel_profile =
        KernelCheckProfileId::parse(&bundle.recommended_tactic_options.kernel_check_profile)
            .map_err(|_| MachineStdImportBundleError::RecipeFieldMismatch {
                bundle_id: bundle.bundle_id.clone(),
                field: "kernel_check_profile",
            })?;
    let request = machine_std_tactic_options_recipe_request(&bundle.recommended_tactic_options);
    let normalized = validate_machine_tactic_options_request_against_context(
        kernel_profile,
        &request,
        &import_context,
        &MachineCheckedCurrentDeclContext::empty(),
    )
    .map_err(
        |source| MachineStdImportBundleError::RecipeMachineApiValidationFailed {
            bundle_id: bundle.bundle_id.clone(),
            source,
        },
    )?;
    if normalized != request {
        return Err(MachineStdImportBundleError::RecipeFieldMismatch {
            bundle_id: bundle.bundle_id.clone(),
            field: "machine_api_tactic_options_request",
        });
    }
    Ok(())
}

fn import_bundle_certificate_context(
    bundle: &MachineStdImportBundle,
) -> Result<MachineImportCertificateContext, MachineStdImportBundleError> {
    let inputs = bundle
        .import_closure
        .iter()
        .map(|certificate| VerifiedModuleCertificateInput {
            module: &certificate.module,
            expected_export_hash: certificate.expected_export_hash,
            expected_certificate_hash: certificate.expected_certificate_hash,
            certificate_bytes: certificate.certificate_bytes.as_slice(),
        })
        .collect::<Vec<_>>();
    let policy = high_trust_policy_for_import_bundle(bundle);
    project_import_certificate_context(&inputs, &bundle.root_imports, &policy).map_err(|source| {
        MachineStdImportBundleError::RecipeImportProjectionFailed {
            bundle_id: bundle.bundle_id.clone(),
            source: Box::new(source),
        }
    })
}

fn high_trust_policy_for_import_bundle(bundle: &MachineStdImportBundle) -> AxiomPolicy {
    let mut policy = AxiomPolicy::high_trust();
    for certificate in &bundle.import_closure {
        if let Ok(cert) = decode_module_cert(&certificate.certificate_bytes) {
            policy
                .allowlisted_axioms
                .extend(cert.name_table.into_iter().filter(Name::is_canonical));
            policy
                .supported_core_features
                .extend(cert.axiom_report.core_features);
        }
    }
    policy
}

#[derive(Clone, Copy)]
struct MvpBundleSpec {
    id: &'static str,
    root_modules: &'static [&'static str],
    recipe_id: &'static str,
}

fn expected_mvp_bundle_specs() -> Vec<MvpBundleSpec> {
    vec![
        MvpBundleSpec {
            id: STD_ALGEBRA_BASIC_BUNDLE_ID,
            root_modules: &["Std.Algebra.Basic", "Std.Logic"],
            recipe_id: STD_LOGIC_RECIPE_ID,
        },
        MvpBundleSpec {
            id: STD_ALL_BUNDLE_ID,
            root_modules: &["Std.Algebra.Basic", "Std.List", "Std.Logic", "Std.Nat"],
            recipe_id: STD_ALL_RECIPE_ID,
        },
        MvpBundleSpec {
            id: STD_LIST_BUNDLE_ID,
            root_modules: &["Std.Logic", "Std.List"],
            recipe_id: STD_LIST_RECIPE_ID,
        },
        MvpBundleSpec {
            id: STD_LOGIC_BUNDLE_ID,
            root_modules: &["Std.Logic"],
            recipe_id: STD_LOGIC_RECIPE_ID,
        },
        MvpBundleSpec {
            id: STD_NAT_BUNDLE_ID,
            root_modules: &["Std.Logic", "Std.Nat"],
            recipe_id: STD_NAT_RECIPE_ID,
        },
    ]
}

fn expected_mvp_bundle_ids() -> Vec<String> {
    expected_mvp_bundle_specs()
        .into_iter()
        .map(|spec| spec.id.to_owned())
        .collect()
}

fn expected_recipe_id_for_bundle(bundle_id: &str) -> Option<&'static str> {
    expected_mvp_bundle_specs()
        .into_iter()
        .find(|spec| spec.id == bundle_id)
        .map(|spec| spec.recipe_id)
}

fn expected_simp_profile_id_for_bundle(bundle_id: &str) -> Option<&'static str> {
    match bundle_id {
        STD_ALGEBRA_BASIC_BUNDLE_ID | STD_LOGIC_BUNDLE_ID => Some(STD_LOGIC_SIMP_PROFILE_ID),
        STD_ALL_BUNDLE_ID => Some(STD_ALL_SIMP_PROFILE_ID),
        STD_LIST_BUNDLE_ID => Some(STD_LIST_SIMP_PROFILE_ID),
        STD_NAT_BUNDLE_ID => Some(STD_NAT_SIMP_PROFILE_ID),
        _ => None,
    }
}

fn std_logic_eq_family(loaded: &MachineStdLoadedRelease) -> Option<EqFamilyRef> {
    let logic = loaded.module(&Name::from_dotted("Std.Logic"))?;
    let eq = find_std_export(logic, &[ExportKind::Inductive], &["Std.Logic.Eq", "Eq"])?;
    let refl = find_std_logic_export(
        logic,
        &[ExportKind::Constructor],
        &["Std.Logic.Eq.refl", "Eq.refl"],
    )?;
    let rec = find_std_logic_export(
        logic,
        &[ExportKind::Recursor, ExportKind::Axiom],
        &["Std.Logic.Eq.rec", "Eq.rec"],
    )?;
    Some(EqFamilyRef {
        eq_name: eq.0,
        eq_interface_hash: eq.1,
        refl_name: refl.0,
        refl_interface_hash: refl.1,
        rec_name: rec.0,
        rec_interface_hash: rec.1,
    })
}

fn std_nat_family(loaded: &MachineStdLoadedRelease) -> Option<NatFamilyRef> {
    let nat = loaded.module(&Name::from_dotted("Std.Nat"))?;
    let nat_head = find_std_export(nat, &[ExportKind::Inductive], &["Std.Nat.Nat", "Nat"])?;
    let zero = find_std_export(
        nat,
        &[ExportKind::Constructor],
        &["Std.Nat.Nat.zero", "Nat.zero"],
    )?;
    let succ = find_std_export(
        nat,
        &[ExportKind::Constructor],
        &["Std.Nat.Nat.succ", "Nat.succ"],
    )?;
    let rec = find_std_export(
        nat,
        &[ExportKind::Recursor],
        &["Std.Nat.Nat.rec", "Nat.rec"],
    )?;
    Some(NatFamilyRef {
        nat_name: nat_head.0,
        nat_interface_hash: nat_head.1,
        zero_name: zero.0,
        zero_interface_hash: zero.1,
        succ_name: succ.0,
        succ_interface_hash: succ.1,
        rec_name: rec.0,
        rec_interface_hash: rec.1,
    })
}

fn find_std_logic_export(
    module: &MachineStdLoadedModule,
    kinds: &[ExportKind],
    candidates: &[&str],
) -> Option<(Name, Hash)> {
    find_std_export(module, kinds, candidates)
}

fn find_std_export(
    module: &MachineStdLoadedModule,
    kinds: &[ExportKind],
    candidates: &[&str],
) -> Option<(Name, Hash)> {
    module
        .verified_module
        .export_block()
        .iter()
        .filter(|entry| kinds.contains(&entry.kind))
        .find_map(|entry| {
            let name = module.verified_module.name_table().get(entry.name)?;
            candidates
                .iter()
                .any(|candidate| *name == Name::from_dotted(candidate))
                .then(|| (name.clone(), entry.decl_interface_hash))
        })
}

fn std_logic_eq_rec_axiom_ref(loaded: &MachineStdLoadedRelease) -> Option<MachineStdAxiomRef> {
    let family = std_logic_eq_family(loaded)?;
    let logic = loaded.module(&Name::from_dotted("Std.Logic"))?;
    let is_axiom_export = logic.verified_module.export_block().iter().any(|entry| {
        entry.kind == ExportKind::Axiom
            && entry.decl_interface_hash == family.rec_interface_hash
            && logic
                .verified_module
                .name_table()
                .get(entry.name)
                .is_some_and(|name| *name == family.rec_name)
    });
    let axiom = is_axiom_export.then(|| MachineStdAxiomRef {
        module: logic.module.clone(),
        name: family.rec_name,
        export_hash: logic.expected_export_hash,
        decl_interface_hash: family.rec_interface_hash,
    })?;
    std_logic_eq_rec_axiom_has_standard_shape(loaded, &axiom).then_some(axiom)
}

fn std_logic_eq_rec_axiom_has_standard_shape(
    loaded: &MachineStdLoadedRelease,
    axiom: &MachineStdAxiomRef,
) -> bool {
    if axiom.module != Name::from_dotted("Std.Logic") || axiom.name != Name::from_dotted("Eq.rec") {
        return false;
    }
    let Some(logic) = loaded.module(&axiom.module) else {
        return false;
    };
    let Ok(declarations) = npa_cert::verified_module_to_kernel_decls(&logic.verified_module) else {
        return false;
    };
    declarations.into_iter().any(|decl| {
        matches!(
            decl,
            npa_kernel::Decl::Axiom {
                name,
                universe_params,
                ty,
            } if name == "Eq.rec"
                && universe_params.len() == 2
                && universe_params[0] == "u"
                && universe_params[1] == "v"
                && npa_cert::core_expr_hash(&ty)
                    == npa_cert::core_expr_hash(&npa_kernel::eq_rec_type(
                        Level::param("u"),
                        Level::param("v"),
                    ))
        )
    })
}

fn machine_std_axiom_ref_to_wire(axiom: &MachineStdAxiomRef) -> MachineAxiomRefWire {
    MachineAxiomRefWire::Imported {
        module: axiom.module.clone(),
        name: axiom.name.clone(),
        export_hash: axiom.export_hash,
        decl_interface_hash: axiom.decl_interface_hash,
    }
}

fn mvp_bundle_allow_axioms(
    loaded: &MachineStdLoadedRelease,
    import_closure: &[MachineStdImportCertificate],
) -> Vec<MachineAxiomRefWire> {
    let Some(axiom) = std_logic_eq_rec_axiom_ref(loaded) else {
        return Vec::new();
    };
    let Some(logic) = loaded.module(&axiom.module) else {
        return Vec::new();
    };
    if import_closure.iter().any(|certificate| {
        certificate.module == logic.module
            && certificate.expected_export_hash == logic.expected_export_hash
            && certificate.expected_certificate_hash == logic.expected_certificate_hash
    }) {
        vec![machine_std_axiom_ref_to_wire(&axiom)]
    } else {
        Vec::new()
    }
}

fn validate_import_bundle_membership(
    bundles: &[MachineStdImportBundle],
) -> Result<(), MachineStdImportBundleError> {
    let expected = expected_mvp_bundle_ids();
    let actual = bundles
        .iter()
        .map(|bundle| bundle.bundle_id.clone())
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for bundle_id in &actual {
        if !seen.insert(bundle_id.clone()) {
            return Err(MachineStdImportBundleError::DuplicateBundle {
                bundle_id: bundle_id.clone(),
            });
        }
    }
    let expected_set = expected.iter().cloned().collect::<BTreeSet<_>>();
    let actual_set = actual.iter().cloned().collect::<BTreeSet<_>>();
    if expected_set != actual_set {
        return Err(MachineStdImportBundleError::InvalidBundleMembership { expected, actual });
    }
    if expected != actual {
        return Err(MachineStdImportBundleError::NonCanonicalBundleOrder { expected, actual });
    }
    Ok(())
}

fn import_key_for_loaded_module(
    loaded: &MachineStdLoadedRelease,
    module: &Name,
    bundle_id: &str,
) -> Result<VerifiedImportKey, MachineStdImportBundleError> {
    let loaded_module =
        loaded
            .module(module)
            .ok_or_else(|| MachineStdImportBundleError::MissingDependency {
                bundle_id: bundle_id.to_owned(),
                owner: module.clone(),
                missing: module.clone(),
            })?;
    Ok(VerifiedImportKey::new(
        loaded_module.module.clone(),
        loaded_module.expected_export_hash,
        loaded_module.expected_certificate_hash,
    ))
}

fn import_closure_for_roots(
    loaded: &MachineStdLoadedRelease,
    bundle_id: &str,
    root_imports: &[VerifiedImportKey],
) -> Result<Vec<MachineStdImportCertificate>, MachineStdImportBundleError> {
    let mut visited = BTreeSet::new();
    let mut pending = root_imports
        .iter()
        .map(|key| key.module.clone())
        .collect::<Vec<_>>();
    while let Some(module) = pending.pop() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let loaded_module = loaded.module(&module).ok_or_else(|| {
            MachineStdImportBundleError::MissingDependency {
                bundle_id: bundle_id.to_owned(),
                owner: module.clone(),
                missing: module.clone(),
            }
        })?;
        for import in &loaded_module.imports {
            let imported = loaded.module(&import.module).ok_or_else(|| {
                MachineStdImportBundleError::MissingDependency {
                    bundle_id: bundle_id.to_owned(),
                    owner: module.clone(),
                    missing: import.module.clone(),
                }
            })?;
            if import.export_hash != imported.expected_export_hash
                || import.certificate_hash != Some(imported.expected_certificate_hash)
            {
                return Err(MachineStdImportBundleError::MissingDependency {
                    bundle_id: bundle_id.to_owned(),
                    owner: module.clone(),
                    missing: import.module.clone(),
                });
            }
            pending.push(import.module.clone());
        }
    }
    let mut closure = visited
        .into_iter()
        .map(|module| {
            let loaded_module = loaded
                .module(&module)
                .expect("visited modules came from loaded release");
            MachineStdImportCertificate {
                module: loaded_module.module.clone(),
                expected_export_hash: loaded_module.expected_export_hash,
                expected_certificate_hash: loaded_module.expected_certificate_hash,
                certificate_encoding: STD_CERTIFICATE_ENCODING.to_owned(),
                certificate_bytes: loaded_module.certificate_bytes.clone(),
            }
        })
        .collect::<Vec<_>>();
    closure.sort_by_key(import_certificate_key);
    Ok(closure)
}

fn validate_import_key_order(
    bundle_id: &str,
    keys: &[VerifiedImportKey],
) -> Result<(), MachineStdImportBundleError> {
    let mut seen = BTreeSet::new();
    let mut previous: Option<Vec<u8>> = None;
    for key in keys {
        if !seen.insert(key.clone()) {
            return Err(MachineStdImportBundleError::DuplicateRootImport {
                bundle_id: bundle_id.to_owned(),
                key: Box::new(key.clone()),
            });
        }
        let bytes = verified_import_key_canonical_bytes(key)
            .map_err(|source| MachineStdImportBundleError::CanonicalBytes { source })?;
        if previous.as_ref().is_some_and(|previous| previous >= &bytes) {
            return Err(MachineStdImportBundleError::NonCanonicalRootImportOrder {
                bundle_id: bundle_id.to_owned(),
            });
        }
        previous = Some(bytes);
    }
    Ok(())
}

fn validate_import_certificate_order(
    bundle_id: &str,
    certificates: &[MachineStdImportCertificate],
) -> Result<(), MachineStdImportBundleError> {
    let mut seen = BTreeSet::new();
    let mut previous: Option<Vec<u8>> = None;
    for certificate in certificates {
        let key = import_certificate_key(certificate);
        if !seen.insert(key.clone()) {
            return Err(MachineStdImportBundleError::DuplicateImportClosure {
                bundle_id: bundle_id.to_owned(),
                key: Box::new(key),
            });
        }
        let bytes = verified_import_key_canonical_bytes(&key)
            .map_err(|source| MachineStdImportBundleError::CanonicalBytes { source })?;
        if previous.as_ref().is_some_and(|previous| previous >= &bytes) {
            return Err(
                MachineStdImportBundleError::NonCanonicalImportClosureOrder {
                    bundle_id: bundle_id.to_owned(),
                },
            );
        }
        previous = Some(bytes);
    }
    Ok(())
}

fn validate_allow_axiom_order(
    bundle_id: &str,
    axioms: &[MachineAxiomRefWire],
) -> Result<(), MachineStdImportBundleError> {
    let mut seen = BTreeSet::new();
    let mut previous: Option<Vec<u8>> = None;
    for axiom in axioms {
        let current = encode_machine_axiom_ref_wire(axiom);
        if !seen.insert(current.clone()) {
            return Err(MachineStdImportBundleError::DuplicateAllowAxiom {
                bundle_id: bundle_id.to_owned(),
                axiom: Box::new(axiom.clone()),
            });
        }
        if previous
            .as_ref()
            .is_some_and(|previous| previous > &current)
        {
            return Err(MachineStdImportBundleError::NonCanonicalAllowAxiomOrder {
                bundle_id: bundle_id.to_owned(),
            });
        }
        previous = Some(current);
    }
    Ok(())
}

fn validate_import_certificate_bytes(
    bundle_id: &str,
    actual: &MachineStdImportCertificate,
    expected: &MachineStdImportCertificate,
) -> Result<(), MachineStdImportBundleError> {
    if actual.certificate_encoding != STD_CERTIFICATE_ENCODING {
        return Err(MachineStdImportBundleError::CertificateEncodingMismatch {
            bundle_id: bundle_id.to_owned(),
            module: actual.module.clone(),
            actual: actual.certificate_encoding.clone(),
        });
    }
    if actual.expected_export_hash != expected.expected_export_hash
        || actual.expected_certificate_hash != expected.expected_certificate_hash
    {
        return Err(MachineStdImportBundleError::ImportKeyHashMismatch {
            bundle_id: bundle_id.to_owned(),
            module: actual.module.clone(),
        });
    }
    let actual_hash = sha256(&actual.certificate_bytes);
    let expected_hash = sha256(&expected.certificate_bytes);
    if actual_hash != expected_hash {
        return Err(MachineStdImportBundleError::CertificateBytesHashMismatch {
            bundle_id: bundle_id.to_owned(),
            module: actual.module.clone(),
            expected: expected_hash,
            actual: actual_hash,
        });
    }
    if actual.certificate_bytes != expected.certificate_bytes {
        return Err(MachineStdImportBundleError::CertificateBytesMismatch {
            bundle_id: bundle_id.to_owned(),
            module: actual.module.clone(),
        });
    }
    Ok(())
}

fn import_certificate_key(certificate: &MachineStdImportCertificate) -> VerifiedImportKey {
    VerifiedImportKey::new(
        certificate.module.clone(),
        certificate.expected_export_hash,
        certificate.expected_certificate_hash,
    )
}

fn validate_machine_std_axiom_report(
    manifest: &MachineStdLibraryRelease,
    loaded: &MachineStdLoadedRelease,
    report: &MachineStdAxiomReport,
) -> Result<(), MachineStdAxiomPolicyError> {
    if report.library_profile_id != STD_LIBRARY_PROFILE_ID {
        return Err(MachineStdAxiomPolicyError::LibraryProfileMismatch {
            expected: STD_LIBRARY_PROFILE_ID,
            actual: report.library_profile_id.clone(),
        });
    }
    validate_axiom_report_module_membership(manifest, report)?;

    let mut expected_transitive_by_module: BTreeMap<Name, Vec<MachineStdAxiomRef>> =
        BTreeMap::new();
    let report_by_module = report
        .modules
        .iter()
        .map(|module| (module.module.clone(), module))
        .collect::<BTreeMap<_, _>>();

    for module_name in loaded.verification_order() {
        let loaded_module = loaded
            .module(module_name)
            .expect("verification order came from loaded module table");
        let report_module = report_by_module
            .get(module_name)
            .expect("axiom report membership was validated");

        compare_axiom_report_hash(
            module_name,
            "export_hash",
            report_module.export_hash,
            loaded_module.expected_export_hash,
        )?;
        compare_axiom_report_hash(
            module_name,
            "certificate_hash",
            report_module.certificate_hash,
            loaded_module.expected_certificate_hash,
        )?;
        validate_axiom_ref_list_order(module_name, "module_axioms", &report_module.module_axioms)?;
        validate_axiom_ref_list_order(
            module_name,
            "transitive_axioms",
            &report_module.transitive_axioms,
        )?;
        if report_module
            .module_axioms
            .iter()
            .any(|axiom| !is_allowed_mvp_std_axiom(loaded, axiom))
        {
            return Err(MachineStdAxiomPolicyError::NonEmptyMvpAxiomList {
                module: module_name.clone(),
                field: "module_axioms",
            });
        }
        if report_module
            .transitive_axioms
            .iter()
            .any(|axiom| !is_allowed_mvp_std_axiom(loaded, axiom))
        {
            return Err(MachineStdAxiomPolicyError::NonEmptyMvpAxiomList {
                module: module_name.clone(),
                field: "transitive_axioms",
            });
        }

        let expected_module_axioms = project_module_axioms(loaded, loaded_module)?;
        if report_module.module_axioms != expected_module_axioms {
            return Err(MachineStdAxiomPolicyError::ModuleAxiomsMismatch {
                module: module_name.clone(),
            });
        }

        let mut transitive = BTreeMap::new();
        for axiom in expected_module_axioms {
            let key = machine_std_axiom_ref_canonical_bytes(&axiom)
                .map_err(|source| MachineStdAxiomPolicyError::CanonicalBytes { source })?;
            transitive.insert(key, axiom);
        }
        for import in &loaded_module.imports {
            let imported = expected_transitive_by_module
                .get(&import.module)
                .ok_or_else(|| MachineStdAxiomPolicyError::TransitiveAxiomsMismatch {
                    module: module_name.clone(),
                })?;
            for axiom in imported {
                let key = machine_std_axiom_ref_canonical_bytes(axiom)
                    .map_err(|source| MachineStdAxiomPolicyError::CanonicalBytes { source })?;
                transitive.insert(key, axiom.clone());
            }
        }
        let expected_transitive = transitive.into_values().collect::<Vec<_>>();
        if report_module.transitive_axioms != expected_transitive {
            return Err(MachineStdAxiomPolicyError::TransitiveAxiomsMismatch {
                module: module_name.clone(),
            });
        }
        expected_transitive_by_module.insert(module_name.clone(), expected_transitive);
    }

    Ok(())
}

fn validate_loaded_mvp_axiom_policy(
    loaded: &MachineStdLoadedRelease,
) -> Result<(), MachineStdReleaseLoaderError> {
    for module_name in loaded.verification_order() {
        let loaded_module = loaded
            .module(module_name)
            .expect("verification order came from loaded module table");
        let module_axioms = project_module_axioms(loaded, loaded_module)
            .map_err(MachineStdReleaseLoaderError::InvalidStdAxiomPolicy)?;
        if module_axioms
            .iter()
            .any(|axiom| !is_allowed_mvp_std_axiom(loaded, axiom))
        {
            return Err(MachineStdReleaseLoaderError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::NonEmptyMvpAxiomList {
                    module: module_name.clone(),
                    field: "module_axioms",
                },
            ));
        }
    }
    Ok(())
}

fn is_allowed_mvp_std_axiom(loaded: &MachineStdLoadedRelease, axiom: &MachineStdAxiomRef) -> bool {
    std_logic_eq_rec_axiom_ref(loaded)
        .as_ref()
        .is_some_and(|allowed| allowed == axiom)
}

fn validate_axiom_report_module_membership(
    manifest: &MachineStdLibraryRelease,
    report: &MachineStdAxiomReport,
) -> Result<(), MachineStdAxiomPolicyError> {
    let expected = manifest
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<Vec<_>>();
    let actual = report
        .modules
        .iter()
        .map(|module| module.module.clone())
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for module in &actual {
        if !seen.insert(module.clone()) {
            return Err(MachineStdAxiomPolicyError::DuplicateModule {
                module: module.clone(),
            });
        }
    }
    let expected_set = expected.iter().cloned().collect::<BTreeSet<_>>();
    let actual_set = actual.iter().cloned().collect::<BTreeSet<_>>();
    if expected_set != actual_set {
        return Err(MachineStdAxiomPolicyError::InvalidModuleMembership { expected, actual });
    }
    if expected != actual {
        return Err(MachineStdAxiomPolicyError::NonCanonicalModuleOrder { expected, actual });
    }
    Ok(())
}

fn compare_axiom_report_hash(
    module: &Name,
    field: &'static str,
    expected: Hash,
    actual: Hash,
) -> Result<(), MachineStdAxiomPolicyError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MachineStdAxiomPolicyError::ModuleHashMismatch {
            module: module.clone(),
            field,
            expected,
            actual,
        })
    }
}

fn validate_axiom_ref_list_order(
    module: &Name,
    field: &'static str,
    axioms: &[MachineStdAxiomRef],
) -> Result<(), MachineStdAxiomPolicyError> {
    let mut previous: Option<Vec<u8>> = None;
    for axiom in axioms {
        let bytes = machine_std_axiom_ref_canonical_bytes(axiom)
            .map_err(|source| MachineStdAxiomPolicyError::CanonicalBytes { source })?;
        if previous.as_ref().is_some_and(|previous| previous >= &bytes) {
            return Err(MachineStdAxiomPolicyError::NonCanonicalAxiomOrder {
                module: module.clone(),
                field,
            });
        }
        previous = Some(bytes);
    }
    Ok(())
}

fn project_module_axioms(
    loaded: &MachineStdLoadedRelease,
    module: &MachineStdLoadedModule,
) -> Result<Vec<MachineStdAxiomRef>, MachineStdAxiomPolicyError> {
    let mut projected = BTreeMap::new();
    for axiom in &module.verified_module.axiom_report().module_axioms {
        let axiom = project_axiom_ref(loaded, module, axiom)?;
        let key = machine_std_axiom_ref_canonical_bytes(&axiom)
            .map_err(|source| MachineStdAxiomPolicyError::CanonicalBytes { source })?;
        projected.insert(key, axiom);
    }
    Ok(projected.into_values().collect())
}

fn project_axiom_ref(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    axiom: &AxiomRef,
) -> Result<MachineStdAxiomRef, MachineStdAxiomPolicyError> {
    match &axiom.global_ref {
        GlobalRef::Local { decl_index } => {
            let Some(decl) = owner.verified_module.declarations().get(*decl_index) else {
                return Err(axiom_projection_error(&owner.module));
            };
            if !matches!(decl.decl, DeclPayload::Axiom { .. }) {
                return Err(axiom_projection_error(&owner.module));
            }
            let Some(name) = owner.verified_module.name_table().get(axiom.name) else {
                return Err(axiom_projection_error(&owner.module));
            };
            Ok(MachineStdAxiomRef {
                module: owner.module.clone(),
                name: name.clone(),
                export_hash: owner.expected_export_hash,
                decl_interface_hash: axiom.decl_interface_hash,
            })
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            let Some(import) = owner.imports.get(*import_index) else {
                return Err(axiom_projection_error(&owner.module));
            };
            let Some(imported) = loaded.module(&import.module) else {
                return Err(axiom_projection_error(&owner.module));
            };
            if import.export_hash != imported.expected_export_hash
                || import.certificate_hash != Some(imported.expected_certificate_hash)
            {
                return Err(axiom_projection_error(&owner.module));
            }
            let Some(axiom_name) = owner.verified_module.name_table().get(*name) else {
                return Err(axiom_projection_error(&owner.module));
            };
            let matches_export = imported.verified_module.export_block().iter().any(|entry| {
                imported
                    .verified_module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|entry_name| {
                        entry.kind == ExportKind::Axiom
                            && entry_name == axiom_name
                            && entry.decl_interface_hash == *decl_interface_hash
                    })
            });
            if !matches_export || axiom.decl_interface_hash != *decl_interface_hash {
                return Err(axiom_projection_error(&owner.module));
            }
            Ok(MachineStdAxiomRef {
                module: imported.module.clone(),
                name: axiom_name.clone(),
                export_hash: imported.expected_export_hash,
                decl_interface_hash: *decl_interface_hash,
            })
        }
        GlobalRef::Builtin { .. } | GlobalRef::LocalGenerated { .. } => {
            Err(axiom_projection_error(&owner.module))
        }
    }
}

fn axiom_projection_error(module: &Name) -> MachineStdAxiomPolicyError {
    MachineStdAxiomPolicyError::AxiomRefProjectionFailed {
        module: module.clone(),
    }
}

fn expected_mvp_modules() -> Vec<Name> {
    machine_std_mvp_module_locators()
        .into_iter()
        .map(|locator| locator.module)
        .collect()
}

const LIBRARY_RELEASE_FIELDS: &[&str] = &[
    "protocol_version",
    "library_profile_id",
    "core_spec_id",
    "kernel_semantics_profile_id",
    "modules",
    "import_bundles_hash",
    "theorem_index_hash",
    "simp_profiles_hash",
    "rewrite_profiles_hash",
    "axiom_report_hash",
];
const MODULE_ARTIFACT_FIELDS: &[&str] = &[
    "module",
    "expected_export_hash",
    "expected_certificate_hash",
    "certificate_encoding",
    "certificate_bytes_hash",
    "axiom_report_hash",
    "public_export_count",
    "theorem_index_entry_count",
    "simp_rule_count",
];
const AXIOM_REPORT_FIELDS: &[&str] = &["library_profile_id", "modules", "axiom_report_hash"];
const MODULE_AXIOM_REPORT_FIELDS: &[&str] = &[
    "module",
    "export_hash",
    "certificate_hash",
    "module_axioms",
    "transitive_axioms",
];
const AXIOM_REF_FIELDS: &[&str] = &["module", "name", "export_hash", "decl_interface_hash"];
const IMPORT_BUNDLE_SET_FIELDS: &[&str] = &["library_profile_id", "bundles", "import_bundles_hash"];
const IMPORT_BUNDLE_FIELDS: &[&str] = &[
    "bundle_id",
    "root_imports",
    "import_closure",
    "allow_axioms",
    "recommended_tactic_options",
];
const IMPORT_KEY_FIELDS: &[&str] = &[
    "module",
    "expected_export_hash",
    "expected_certificate_hash",
];
const IMPORT_CERTIFICATE_FIELDS: &[&str] = &[
    "module",
    "expected_export_hash",
    "expected_certificate_hash",
    "certificate",
];
const CERTIFICATE_WRAPPER_FIELDS: &[&str] = &["encoding", "bytes"];
const TACTIC_OPTIONS_RECIPE_FIELDS: &[&str] = &[
    "recipe_id",
    "kernel_check_profile",
    "simp_rules",
    "eq_family",
    "nat_family",
    "max_simp_rewrite_steps",
    "max_open_goals",
    "max_metas",
];
const SIMP_RULE_FIELDS: &[&str] = &["name", "decl_interface_hash", "direction"];
const EQ_FAMILY_FIELDS: &[&str] = &[
    "eq_name",
    "eq_interface_hash",
    "refl_name",
    "refl_interface_hash",
    "rec_name",
    "rec_interface_hash",
];
const NAT_FAMILY_FIELDS: &[&str] = &[
    "nat_name",
    "nat_interface_hash",
    "zero_name",
    "zero_interface_hash",
    "succ_name",
    "succ_interface_hash",
    "rec_name",
    "rec_interface_hash",
];
const THEOREM_INDEX_FIELDS: &[&str] = &[
    "index_profile_id",
    "library_profile_id",
    "entries",
    "index_hash",
];
const THEOREM_ENTRY_FIELDS: &[&str] = &[
    "global_ref",
    "kind",
    "universe_params",
    "statement_core_hash",
    "statement_head",
    "constants",
    "modes",
    "attributes",
    "rewrite_descriptors",
    "axiom_dependencies",
    "proof_term_size",
];
const GLOBAL_REF_FIELDS: &[&str] = &[
    "module",
    "name",
    "export_hash",
    "certificate_hash",
    "decl_interface_hash",
];
const GLOBAL_REF_VIEW_DECL_FIELDS: &[&str] = &[
    "kind",
    "module",
    "name",
    "export_hash",
    "certificate_hash",
    "decl_interface_hash",
    "public_export",
];
const GLOBAL_REF_VIEW_GENERATED_FIELDS: &[&str] = &[
    "kind",
    "module",
    "parent_name",
    "name",
    "export_hash",
    "certificate_hash",
    "parent_decl_interface_hash",
    "decl_interface_hash",
    "public_export",
];
const REWRITE_DESCRIPTOR_FIELDS: &[&str] = &[
    "source",
    "direction",
    "safety",
    "lhs_core_hash",
    "rhs_core_hash",
    "rule_telescope_hash",
];
const REWRITE_PROFILE_SET_FIELDS: &[&str] =
    &["library_profile_id", "profiles", "rewrite_profiles_hash"];
const REWRITE_PROFILE_FIELDS: &[&str] = &[
    "profile_id",
    "required_import_bundle_id",
    "kernel_check_profile",
    "eq_family",
    "descriptors",
    "profile_hash",
];
const SIMP_PROFILE_SET_FIELDS: &[&str] = &["library_profile_id", "profiles", "simp_profiles_hash"];
const SIMP_PROFILE_FIELDS: &[&str] = &[
    "profile_id",
    "required_import_bundle_id",
    "kernel_check_profile",
    "eq_family",
    "rules",
    "profile_hash",
];
const PROMPT_METADATA_SET_FIELDS: &[&str] = &[
    "metadata_profile_id",
    "library_profile_id",
    "entries",
    "prompt_metadata_hash",
];
const PROMPT_METADATA_FIELDS: &[&str] = &["global_ref", "short_doc", "examples", "tags"];
const PROMPT_EXAMPLE_FIELDS: &[&str] = &[
    "goal_core_hash",
    "imports_bundle_id",
    "candidate_kind",
    "display",
];

fn parse_std_json<'src>(
    source: &'src str,
    artifact: MachineStdArtifactKind,
) -> Result<JsonDocument<'src>, MachineStdArtifactShapeError> {
    JsonDocument::parse(source).map_err(|err| MachineStdArtifactShapeError {
        artifact,
        path: "$".to_owned(),
        reason: MachineStdArtifactShapeErrorReason::JsonParse {
            offset: err.offset,
            kind: err.kind,
        },
    })
}

fn parse_library_release_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdLibraryRelease, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::LibraryRelease,
        path,
        LIBRARY_RELEASE_FIELDS,
    )?;
    let modules = required_array(
        members,
        MachineStdArtifactKind::LibraryRelease,
        path,
        "modules",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_module_artifact_value(item, &array_path(path, "modules", index)))
    .collect::<Result<Vec<_>, _>>()?;

    Ok(MachineStdLibraryRelease {
        protocol_version: required_string(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "protocol_version",
        )?
        .to_owned(),
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        core_spec_id: required_string(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "core_spec_id",
        )?
        .to_owned(),
        kernel_semantics_profile_id: required_string(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "kernel_semantics_profile_id",
        )?
        .to_owned(),
        modules,
        import_bundles_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "import_bundles_hash",
        )?,
        theorem_index_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "theorem_index_hash",
        )?,
        simp_profiles_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "simp_profiles_hash",
        )?,
        rewrite_profiles_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "rewrite_profiles_hash",
        )?,
        axiom_report_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "axiom_report_hash",
        )?,
    })
}

fn parse_module_artifact_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdModuleArtifact, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::LibraryRelease,
        path,
        MODULE_ARTIFACT_FIELDS,
    )?;
    Ok(MachineStdModuleArtifact {
        module: required_module_name(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "module",
        )?,
        expected_export_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "expected_export_hash",
        )?,
        expected_certificate_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "expected_certificate_hash",
        )?,
        certificate_encoding: required_string(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "certificate_encoding",
        )?
        .to_owned(),
        certificate_bytes_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "certificate_bytes_hash",
        )?,
        axiom_report_hash: required_hash(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "axiom_report_hash",
        )?,
        public_export_count: required_u64(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "public_export_count",
        )?,
        theorem_index_entry_count: required_u64(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "theorem_index_entry_count",
        )?,
        simp_rule_count: required_u64(
            members,
            MachineStdArtifactKind::LibraryRelease,
            path,
            "simp_rule_count",
        )?,
    })
}

fn parse_import_bundle_set_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdImportBundleSet, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        path,
        IMPORT_BUNDLE_SET_FIELDS,
    )?;
    let bundles = required_array(
        members,
        MachineStdArtifactKind::ImportBundles,
        path,
        "bundles",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_import_bundle_value(item, &array_path(path, "bundles", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdImportBundleSet {
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        bundles,
        import_bundles_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "import_bundles_hash",
        )?,
    })
}

fn parse_import_bundle_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdImportBundle, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        path,
        IMPORT_BUNDLE_FIELDS,
    )?;
    Ok(MachineStdImportBundle {
        bundle_id: required_string(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "bundle_id",
        )?
        .to_owned(),
        root_imports: parse_import_key_array(members, path, "root_imports")?,
        import_closure: parse_import_certificate_array(members, path, "import_closure")?,
        allow_axioms: parse_machine_axiom_ref_wire_array(members, path, "allow_axioms")?,
        recommended_tactic_options: parse_tactic_options_recipe_value(
            required_value(members, "recommended_tactic_options"),
            &field_path(path, "recommended_tactic_options"),
        )?,
    })
}

fn parse_import_key_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<VerifiedImportKey>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::ImportBundles, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| parse_import_key_value(item, &array_path(path, field, index)))
        .collect()
}

fn parse_import_certificate_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdImportCertificate>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::ImportBundles, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| parse_import_certificate_value(item, &array_path(path, field, index)))
        .collect()
}

fn parse_import_key_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<VerifiedImportKey, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        path,
        IMPORT_KEY_FIELDS,
    )?;
    Ok(VerifiedImportKey::new(
        required_module_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "module",
        )?,
        required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "expected_export_hash",
        )?,
        required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "expected_certificate_hash",
        )?,
    ))
}

fn parse_import_certificate_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdImportCertificate, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        path,
        IMPORT_CERTIFICATE_FIELDS,
    )?;
    let certificate_members = validated_object_members(
        required_value(members, "certificate"),
        MachineStdArtifactKind::ImportBundles,
        &field_path(path, "certificate"),
        CERTIFICATE_WRAPPER_FIELDS,
    )?;
    Ok(MachineStdImportCertificate {
        module: required_module_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "module",
        )?,
        expected_export_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "expected_export_hash",
        )?,
        expected_certificate_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "expected_certificate_hash",
        )?,
        certificate_encoding: required_string(
            certificate_members,
            MachineStdArtifactKind::ImportBundles,
            &field_path(path, "certificate"),
            "encoding",
        )?
        .to_owned(),
        certificate_bytes: required_hex_bytes(
            certificate_members,
            MachineStdArtifactKind::ImportBundles,
            &field_path(path, "certificate"),
            "bytes",
        )?,
    })
}

fn parse_tactic_options_recipe_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdTacticOptionsRecipe, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        path,
        TACTIC_OPTIONS_RECIPE_FIELDS,
    )?;
    Ok(MachineStdTacticOptionsRecipe {
        recipe_id: required_string(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "recipe_id",
        )?
        .to_owned(),
        kernel_check_profile: required_string(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "kernel_check_profile",
        )?
        .to_owned(),
        simp_rules: parse_simp_rule_array(members, path, "simp_rules")?,
        eq_family: parse_optional_eq_family_value(required_value(members, "eq_family"), path)?,
        nat_family: parse_optional_nat_family_value(required_value(members, "nat_family"), path)?,
        max_simp_rewrite_steps: required_u64(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "max_simp_rewrite_steps",
        )?,
        max_open_goals: required_u64(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "max_open_goals",
        )?,
        max_metas: required_u64(
            members,
            MachineStdArtifactKind::ImportBundles,
            path,
            "max_metas",
        )?,
    })
}

fn parse_simp_rule_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<SimpRuleRef>, MachineStdArtifactShapeError> {
    parse_simp_rule_array_for(MachineStdArtifactKind::ImportBundles, members, path, field)
}

fn parse_simp_rule_array_for(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<SimpRuleRef>, MachineStdArtifactShapeError> {
    required_array(members, artifact, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_simp_rule_value_for(artifact, item, &array_path(path, field, index))
        })
        .collect()
}

fn parse_simp_rule_value_for(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
) -> Result<SimpRuleRef, MachineStdArtifactShapeError> {
    let members = validated_object_members(value, artifact, path, SIMP_RULE_FIELDS)?;
    let direction = match required_string(members, artifact, path, "direction")? {
        "forward" => RewriteDirection::Forward,
        "backward" => RewriteDirection::Backward,
        _ => {
            return Err(shape_error(
                artifact,
                &field_path(path, "direction"),
                MachineStdArtifactShapeErrorReason::InvalidEnumString { field: "direction" },
            ));
        }
    };
    Ok(SimpRuleRef {
        name: required_fully_qualified_name(members, artifact, path, "name")?,
        decl_interface_hash: required_hash(members, artifact, path, "decl_interface_hash")?,
        direction,
    })
}

fn parse_optional_eq_family_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Option<EqFamilyRef>, MachineStdArtifactShapeError> {
    parse_optional_eq_family_value_for(MachineStdArtifactKind::ImportBundles, value, path)
}

fn parse_optional_eq_family_value_for(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Option<EqFamilyRef>, MachineStdArtifactShapeError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let path = field_path(path, "eq_family");
    let members = validated_object_members(value, artifact, &path, EQ_FAMILY_FIELDS)?;
    Ok(Some(EqFamilyRef {
        eq_name: required_fully_qualified_name(members, artifact, &path, "eq_name")?,
        eq_interface_hash: required_hash(members, artifact, &path, "eq_interface_hash")?,
        refl_name: required_fully_qualified_name(members, artifact, &path, "refl_name")?,
        refl_interface_hash: required_hash(members, artifact, &path, "refl_interface_hash")?,
        rec_name: required_fully_qualified_name(members, artifact, &path, "rec_name")?,
        rec_interface_hash: required_hash(members, artifact, &path, "rec_interface_hash")?,
    }))
}

fn parse_optional_nat_family_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Option<NatFamilyRef>, MachineStdArtifactShapeError> {
    if value.kind() == JsonValueKind::Null {
        return Ok(None);
    }
    let path = field_path(path, "nat_family");
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::ImportBundles,
        &path,
        NAT_FAMILY_FIELDS,
    )?;
    Ok(Some(NatFamilyRef {
        nat_name: required_fully_qualified_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "nat_name",
        )?,
        nat_interface_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "nat_interface_hash",
        )?,
        zero_name: required_fully_qualified_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "zero_name",
        )?,
        zero_interface_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "zero_interface_hash",
        )?,
        succ_name: required_fully_qualified_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "succ_name",
        )?,
        succ_interface_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "succ_interface_hash",
        )?,
        rec_name: required_fully_qualified_name(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "rec_name",
        )?,
        rec_interface_hash: required_hash(
            members,
            MachineStdArtifactKind::ImportBundles,
            &path,
            "rec_interface_hash",
        )?,
    }))
}

fn parse_machine_axiom_ref_wire_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineAxiomRefWire>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::ImportBundles, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_machine_axiom_ref_wire_value(item, &array_path(path, field, index))
        })
        .collect()
}

fn parse_machine_axiom_ref_wire_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineAxiomRefWire, MachineStdArtifactShapeError> {
    let members = validated_machine_axiom_ref_wire_members(value, path)?;
    let kind = required_string(members, MachineStdArtifactKind::ImportBundles, path, "kind")?;
    match kind {
        "imported" => {
            let members = validated_object_members(
                value,
                MachineStdArtifactKind::ImportBundles,
                path,
                &[
                    "kind",
                    "module",
                    "name",
                    "export_hash",
                    "decl_interface_hash",
                ],
            )?;
            Ok(MachineAxiomRefWire::Imported {
                module: required_module_name(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "module",
                )?,
                name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "name",
                )?,
                export_hash: required_hash(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "export_hash",
                )?,
                decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "decl_interface_hash",
                )?,
            })
        }
        "current_module" => {
            let members = validated_object_members(
                value,
                MachineStdArtifactKind::ImportBundles,
                path,
                &[
                    "kind",
                    "module",
                    "name",
                    "source_index",
                    "decl_interface_hash",
                ],
            )?;
            Ok(MachineAxiomRefWire::CurrentModule {
                module: required_module_name(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "module",
                )?,
                name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "name",
                )?,
                source_index: required_u64(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "source_index",
                )?,
                decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "decl_interface_hash",
                )?,
            })
        }
        "builtin" => {
            let members = validated_object_members(
                value,
                MachineStdArtifactKind::ImportBundles,
                path,
                &["kind", "name", "decl_interface_hash"],
            )?;
            Ok(MachineAxiomRefWire::Builtin {
                name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "name",
                )?,
                decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::ImportBundles,
                    path,
                    "decl_interface_hash",
                )?,
            })
        }
        _ => Err(shape_error(
            MachineStdArtifactKind::ImportBundles,
            &field_path(path, "kind"),
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field: "kind" },
        )),
    }
}

fn validated_machine_axiom_ref_wire_members<'value, 'src>(
    value: &'value JsonValue<'src>,
    path: &str,
) -> Result<&'value [crate::json::JsonMember<'src>], MachineStdArtifactShapeError> {
    let Some(members) = value.object_members() else {
        return Err(shape_error(
            MachineStdArtifactKind::ImportBundles,
            path,
            MachineStdArtifactShapeErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(shape_error(
                MachineStdArtifactKind::ImportBundles,
                &field_path(path, member.key()),
                MachineStdArtifactShapeErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    if !members.iter().any(|member| member.key() == "kind") {
        return Err(shape_error(
            MachineStdArtifactKind::ImportBundles,
            &field_path(path, "kind"),
            MachineStdArtifactShapeErrorReason::MissingField { field: "kind" },
        ));
    }
    Ok(members)
}

fn parse_theorem_index_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdTheoremIndex, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::TheoremIndex,
        path,
        THEOREM_INDEX_FIELDS,
    )?;
    let entries = required_array(
        members,
        MachineStdArtifactKind::TheoremIndex,
        path,
        "entries",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_theorem_entry_value(item, &array_path(path, "entries", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdTheoremIndex {
        index_profile_id: required_string(
            members,
            MachineStdArtifactKind::TheoremIndex,
            path,
            "index_profile_id",
        )?
        .to_owned(),
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::TheoremIndex,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        entries,
        index_hash: required_hash(
            members,
            MachineStdArtifactKind::TheoremIndex,
            path,
            "index_hash",
        )?,
    })
}

fn parse_theorem_entry_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdTheoremEntry, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::TheoremIndex,
        path,
        THEOREM_ENTRY_FIELDS,
    )?;
    Ok(MachineStdTheoremEntry {
        global_ref: parse_global_ref_value(
            required_value(members, "global_ref"),
            &field_path(path, "global_ref"),
        )?,
        kind: parse_theorem_kind(members, path, "kind")?,
        universe_params: parse_string_array(
            MachineStdArtifactKind::TheoremIndex,
            members,
            path,
            "universe_params",
        )?,
        statement_core_hash: required_hash(
            members,
            MachineStdArtifactKind::TheoremIndex,
            path,
            "statement_core_hash",
        )?,
        statement_head: parse_optional_global_ref_view(
            required_value(members, "statement_head"),
            &field_path(path, "statement_head"),
        )?,
        constants: parse_global_ref_view_array(members, path, "constants")?,
        modes: parse_theorem_mode_array(members, path, "modes")?,
        attributes: parse_std_attribute_array(members, path, "attributes")?,
        rewrite_descriptors: parse_rewrite_descriptor_array(
            MachineStdArtifactKind::TheoremIndex,
            members,
            path,
            "rewrite_descriptors",
        )?,
        axiom_dependencies: parse_axiom_ref_array_for(
            MachineStdArtifactKind::TheoremIndex,
            members,
            path,
            "axiom_dependencies",
        )?,
        proof_term_size: parse_optional_u64_value(
            MachineStdArtifactKind::TheoremIndex,
            required_value(members, "proof_term_size"),
            &field_path(path, "proof_term_size"),
            "proof_term_size",
        )?,
    })
}

fn parse_global_ref_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdGlobalRef, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::TheoremIndex,
        path,
        GLOBAL_REF_FIELDS,
    )?;
    parse_global_ref_from_members(MachineStdArtifactKind::TheoremIndex, members, path)
}

fn parse_global_ref_value_for(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdGlobalRef, MachineStdArtifactShapeError> {
    let members = validated_object_members(value, artifact, path, GLOBAL_REF_FIELDS)?;
    parse_global_ref_from_members(artifact, members, path)
}

fn parse_global_ref_from_members(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
) -> Result<MachineStdGlobalRef, MachineStdArtifactShapeError> {
    Ok(MachineStdGlobalRef {
        module: required_module_name(members, artifact, path, "module")?,
        name: required_fully_qualified_name(members, artifact, path, "name")?,
        export_hash: required_hash(members, artifact, path, "export_hash")?,
        certificate_hash: required_hash(members, artifact, path, "certificate_hash")?,
        decl_interface_hash: required_hash(members, artifact, path, "decl_interface_hash")?,
    })
}

fn parse_optional_global_ref_view(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<Option<MachineStdGlobalRefView>, MachineStdArtifactShapeError> {
    if value.kind() == JsonValueKind::Null {
        Ok(None)
    } else {
        parse_global_ref_view_value(value, path).map(Some)
    }
}

fn parse_global_ref_view_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdGlobalRefView>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::TheoremIndex, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| parse_global_ref_view_value(item, &array_path(path, field, index)))
        .collect()
}

fn parse_global_ref_view_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdGlobalRefView, MachineStdArtifactShapeError> {
    let kind_members =
        validated_kinded_object_members(value, MachineStdArtifactKind::TheoremIndex, path)?;
    let kind = required_string(
        kind_members,
        MachineStdArtifactKind::TheoremIndex,
        path,
        "kind",
    )?;
    match kind {
        "decl" => {
            let members = validated_object_members(
                value,
                MachineStdArtifactKind::TheoremIndex,
                path,
                GLOBAL_REF_VIEW_DECL_FIELDS,
            )?;
            Ok(MachineStdGlobalRefView::Decl {
                module: required_module_name(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "module",
                )?,
                name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "name",
                )?,
                export_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "export_hash",
                )?,
                certificate_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "certificate_hash",
                )?,
                decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "decl_interface_hash",
                )?,
                public_export: required_bool(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "public_export",
                )?,
            })
        }
        "generated" => {
            let members = validated_object_members(
                value,
                MachineStdArtifactKind::TheoremIndex,
                path,
                GLOBAL_REF_VIEW_GENERATED_FIELDS,
            )?;
            Ok(MachineStdGlobalRefView::Generated {
                module: required_module_name(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "module",
                )?,
                parent_name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "parent_name",
                )?,
                name: required_fully_qualified_name(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "name",
                )?,
                export_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "export_hash",
                )?,
                certificate_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "certificate_hash",
                )?,
                parent_decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "parent_decl_interface_hash",
                )?,
                decl_interface_hash: required_hash(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "decl_interface_hash",
                )?,
                public_export: required_bool(
                    members,
                    MachineStdArtifactKind::TheoremIndex,
                    path,
                    "public_export",
                )?,
            })
        }
        _ => Err(shape_error(
            MachineStdArtifactKind::TheoremIndex,
            &field_path(path, "kind"),
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field: "kind" },
        )),
    }
}

fn parse_theorem_kind(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<MachineStdTheoremKind, MachineStdArtifactShapeError> {
    match required_string(members, MachineStdArtifactKind::TheoremIndex, path, field)? {
        "theorem" => Ok(MachineStdTheoremKind::Theorem),
        "axiom" => Ok(MachineStdTheoremKind::Axiom),
        _ => Err(shape_error(
            MachineStdArtifactKind::TheoremIndex,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field },
        )),
    }
}

fn parse_theorem_mode_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineTheoremMode>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::TheoremIndex, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| parse_theorem_mode_value(item, &array_path(path, field, index), field))
        .collect()
}

fn parse_theorem_mode_value(
    value: &JsonValue<'_>,
    path: &str,
    field: &'static str,
) -> Result<MachineTheoremMode, MachineStdArtifactShapeError> {
    match parse_string_value(MachineStdArtifactKind::TheoremIndex, value, path, field)? {
        "exact" => Ok(MachineTheoremMode::Exact),
        "apply" => Ok(MachineTheoremMode::Apply),
        "rw" => Ok(MachineTheoremMode::Rw),
        "simp" => Ok(MachineTheoremMode::Simp),
        _ => Err(shape_error(
            MachineStdArtifactKind::TheoremIndex,
            path,
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field },
        )),
    }
}

fn parse_std_attribute_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdAttribute>, MachineStdArtifactShapeError> {
    required_array(members, MachineStdArtifactKind::TheoremIndex, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_std_attribute_value(item, &array_path(path, field, index), field)
        })
        .collect()
}

fn parse_std_attribute_value(
    value: &JsonValue<'_>,
    path: &str,
    field: &'static str,
) -> Result<MachineStdAttribute, MachineStdArtifactShapeError> {
    match parse_string_value(MachineStdArtifactKind::TheoremIndex, value, path, field)? {
        "simp" => Ok(MachineStdAttribute::Simp),
        "rw" => Ok(MachineStdAttribute::Rw),
        "intro" => Ok(MachineStdAttribute::Intro),
        "elim" => Ok(MachineStdAttribute::Elim),
        "apply" => Ok(MachineStdAttribute::Apply),
        "refl" => Ok(MachineStdAttribute::Refl),
        "trans" => Ok(MachineStdAttribute::Trans),
        "congr" => Ok(MachineStdAttribute::Congr),
        _ => Err(shape_error(
            MachineStdArtifactKind::TheoremIndex,
            path,
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field },
        )),
    }
}

fn parse_rewrite_profile_set_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdRewriteProfileSet, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::RewriteProfiles,
        path,
        REWRITE_PROFILE_SET_FIELDS,
    )?;
    let profiles = required_array(
        members,
        MachineStdArtifactKind::RewriteProfiles,
        path,
        "profiles",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_rewrite_profile_value(item, &array_path(path, "profiles", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdRewriteProfileSet {
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        profiles,
        rewrite_profiles_hash: required_hash(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "rewrite_profiles_hash",
        )?,
    })
}

fn parse_rewrite_profile_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdRewriteProfile, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::RewriteProfiles,
        path,
        REWRITE_PROFILE_FIELDS,
    )?;
    Ok(MachineStdRewriteProfile {
        profile_id: required_string(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "profile_id",
        )?
        .to_owned(),
        required_import_bundle_id: required_string(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "required_import_bundle_id",
        )?
        .to_owned(),
        kernel_check_profile: required_string(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "kernel_check_profile",
        )?
        .to_owned(),
        eq_family: parse_optional_eq_family_value_for(
            MachineStdArtifactKind::RewriteProfiles,
            required_value(members, "eq_family"),
            path,
        )?,
        descriptors: parse_rewrite_descriptor_array(
            MachineStdArtifactKind::RewriteProfiles,
            members,
            path,
            "descriptors",
        )?,
        profile_hash: required_hash(
            members,
            MachineStdArtifactKind::RewriteProfiles,
            path,
            "profile_hash",
        )?,
    })
}

fn parse_rewrite_descriptor_array(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdRewriteDescriptor>, MachineStdArtifactShapeError> {
    required_array(members, artifact, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_rewrite_descriptor_value(artifact, item, &array_path(path, field, index))
        })
        .collect()
}

fn parse_rewrite_descriptor_value(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdRewriteDescriptor, MachineStdArtifactShapeError> {
    let members = validated_object_members(value, artifact, path, REWRITE_DESCRIPTOR_FIELDS)?;
    Ok(MachineStdRewriteDescriptor {
        source: parse_global_ref_value_for(
            artifact,
            required_value(members, "source"),
            &field_path(path, "source"),
        )?,
        direction: parse_rewrite_direction(artifact, members, path, "direction")?,
        safety: parse_rewrite_safety(artifact, members, path, "safety")?,
        lhs_core_hash: required_hash(members, artifact, path, "lhs_core_hash")?,
        rhs_core_hash: required_hash(members, artifact, path, "rhs_core_hash")?,
        rule_telescope_hash: required_hash(members, artifact, path, "rule_telescope_hash")?,
    })
}

fn parse_simp_profile_set_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdSimpProfileSet, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::SimpProfiles,
        path,
        SIMP_PROFILE_SET_FIELDS,
    )?;
    let profiles = required_array(
        members,
        MachineStdArtifactKind::SimpProfiles,
        path,
        "profiles",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_simp_profile_value(item, &array_path(path, "profiles", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdSimpProfileSet {
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        profiles,
        simp_profiles_hash: required_hash(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "simp_profiles_hash",
        )?,
    })
}

fn parse_simp_profile_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdSimpProfile, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::SimpProfiles,
        path,
        SIMP_PROFILE_FIELDS,
    )?;
    Ok(MachineStdSimpProfile {
        profile_id: required_string(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "profile_id",
        )?
        .to_owned(),
        required_import_bundle_id: required_string(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "required_import_bundle_id",
        )?
        .to_owned(),
        kernel_check_profile: required_string(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "kernel_check_profile",
        )?
        .to_owned(),
        eq_family: parse_optional_eq_family_value_for(
            MachineStdArtifactKind::SimpProfiles,
            required_value(members, "eq_family"),
            path,
        )?,
        rules: parse_simp_rule_array_for(
            MachineStdArtifactKind::SimpProfiles,
            members,
            path,
            "rules",
        )?,
        profile_hash: required_hash(
            members,
            MachineStdArtifactKind::SimpProfiles,
            path,
            "profile_hash",
        )?,
    })
}

fn parse_prompt_metadata_set_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdPromptMetadataSet, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::PromptMetadata,
        path,
        PROMPT_METADATA_SET_FIELDS,
    )?;
    let entries = required_array(
        members,
        MachineStdArtifactKind::PromptMetadata,
        path,
        "entries",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_prompt_metadata_value(item, &array_path(path, "entries", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdPromptMetadataSet {
        metadata_profile_id: required_string(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "metadata_profile_id",
        )?
        .to_owned(),
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        entries,
        prompt_metadata_hash: required_hash(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "prompt_metadata_hash",
        )?,
    })
}

fn parse_prompt_metadata_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdPromptMetadata, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::PromptMetadata,
        path,
        PROMPT_METADATA_FIELDS,
    )?;
    let examples = required_array(
        members,
        MachineStdArtifactKind::PromptMetadata,
        path,
        "examples",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_prompt_example_value(item, &array_path(path, "examples", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdPromptMetadata {
        global_ref: parse_global_ref_value_for(
            MachineStdArtifactKind::PromptMetadata,
            required_value(members, "global_ref"),
            &field_path(path, "global_ref"),
        )?,
        short_doc: parse_optional_string_value(
            MachineStdArtifactKind::PromptMetadata,
            required_value(members, "short_doc"),
            &field_path(path, "short_doc"),
            "short_doc",
        )?,
        examples,
        tags: parse_string_array(
            MachineStdArtifactKind::PromptMetadata,
            members,
            path,
            "tags",
        )?,
    })
}

fn parse_prompt_example_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdPromptExample, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::PromptMetadata,
        path,
        PROMPT_EXAMPLE_FIELDS,
    )?;
    Ok(MachineStdPromptExample {
        goal_core_hash: required_hash(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "goal_core_hash",
        )?,
        imports_bundle_id: required_string(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "imports_bundle_id",
        )?
        .to_owned(),
        candidate_kind: required_string(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "candidate_kind",
        )?
        .to_owned(),
        display: required_string(
            members,
            MachineStdArtifactKind::PromptMetadata,
            path,
            "display",
        )?
        .to_owned(),
    })
}

fn parse_rewrite_direction(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<RewriteDirection, MachineStdArtifactShapeError> {
    match required_string(members, artifact, path, field)? {
        "forward" => Ok(RewriteDirection::Forward),
        "backward" => Ok(RewriteDirection::Backward),
        _ => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field },
        )),
    }
}

fn parse_rewrite_safety(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<MachineStdRewriteSafety, MachineStdArtifactShapeError> {
    match required_string(members, artifact, path, field)? {
        "simp_safe" => Ok(MachineStdRewriteSafety::SimpSafe),
        "rw_only" => Ok(MachineStdRewriteSafety::RwOnly),
        "unsafe_for_automation" => Ok(MachineStdRewriteSafety::UnsafeForAutomation),
        _ => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidEnumString { field },
        )),
    }
}

fn parse_axiom_report_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdAxiomReport, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::AxiomReport,
        path,
        AXIOM_REPORT_FIELDS,
    )?;
    let modules = required_array(
        members,
        MachineStdArtifactKind::AxiomReport,
        path,
        "modules",
    )?
    .iter()
    .enumerate()
    .map(|(index, item)| parse_module_axiom_report_value(item, &array_path(path, "modules", index)))
    .collect::<Result<Vec<_>, _>>()?;
    Ok(MachineStdAxiomReport {
        library_profile_id: required_string(
            members,
            MachineStdArtifactKind::AxiomReport,
            path,
            "library_profile_id",
        )?
        .to_owned(),
        modules,
        axiom_report_hash: required_hash(
            members,
            MachineStdArtifactKind::AxiomReport,
            path,
            "axiom_report_hash",
        )?,
    })
}

fn parse_module_axiom_report_value(
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdModuleAxiomReport, MachineStdArtifactShapeError> {
    let members = validated_object_members(
        value,
        MachineStdArtifactKind::AxiomReport,
        path,
        MODULE_AXIOM_REPORT_FIELDS,
    )?;
    Ok(MachineStdModuleAxiomReport {
        module: required_module_name(members, MachineStdArtifactKind::AxiomReport, path, "module")?,
        export_hash: required_hash(
            members,
            MachineStdArtifactKind::AxiomReport,
            path,
            "export_hash",
        )?,
        certificate_hash: required_hash(
            members,
            MachineStdArtifactKind::AxiomReport,
            path,
            "certificate_hash",
        )?,
        module_axioms: parse_axiom_ref_array(members, path, "module_axioms")?,
        transitive_axioms: parse_axiom_ref_array(members, path, "transitive_axioms")?,
    })
}

fn parse_axiom_ref_array(
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdAxiomRef>, MachineStdArtifactShapeError> {
    parse_axiom_ref_array_for(MachineStdArtifactKind::AxiomReport, members, path, field)
}

fn parse_axiom_ref_array_for(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<MachineStdAxiomRef>, MachineStdArtifactShapeError> {
    required_array(members, artifact, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_axiom_ref_value_for(artifact, item, &array_path(path, field, index))
        })
        .collect()
}

fn parse_axiom_ref_value_for(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
) -> Result<MachineStdAxiomRef, MachineStdArtifactShapeError> {
    let members = validated_object_members(value, artifact, path, AXIOM_REF_FIELDS)?;
    Ok(MachineStdAxiomRef {
        module: required_module_name(members, artifact, path, "module")?,
        name: required_fully_qualified_name(members, artifact, path, "name")?,
        export_hash: required_hash(members, artifact, path, "export_hash")?,
        decl_interface_hash: required_hash(members, artifact, path, "decl_interface_hash")?,
    })
}

fn validated_object_members<'value, 'src>(
    value: &'value JsonValue<'src>,
    artifact: MachineStdArtifactKind,
    path: &str,
    allowed_fields: &[&'static str],
) -> Result<&'value [crate::json::JsonMember<'src>], MachineStdArtifactShapeError> {
    let Some(members) = value.object_members() else {
        return Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(shape_error(
                artifact,
                &field_path(path, member.key()),
                MachineStdArtifactShapeErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    for member in members {
        if !allowed_fields.iter().any(|field| *field == member.key()) {
            return Err(shape_error(
                artifact,
                &field_path(path, member.key()),
                MachineStdArtifactShapeErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }
    for field in allowed_fields {
        if !members.iter().any(|member| member.key() == *field) {
            return Err(shape_error(
                artifact,
                &field_path(path, field),
                MachineStdArtifactShapeErrorReason::MissingField { field },
            ));
        }
    }
    Ok(members)
}

fn validated_kinded_object_members<'value, 'src>(
    value: &'value JsonValue<'src>,
    artifact: MachineStdArtifactKind,
    path: &str,
) -> Result<&'value [crate::json::JsonMember<'src>], MachineStdArtifactShapeError> {
    let Some(members) = value.object_members() else {
        return Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };
    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(shape_error(
                artifact,
                &field_path(path, member.key()),
                MachineStdArtifactShapeErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }
    if !members.iter().any(|member| member.key() == "kind") {
        return Err(shape_error(
            artifact,
            &field_path(path, "kind"),
            MachineStdArtifactShapeErrorReason::MissingField { field: "kind" },
        ));
    }
    Ok(members)
}

fn required_value<'value, 'src>(
    members: &'value [crate::json::JsonMember<'src>],
    field: &'static str,
) -> &'value JsonValue<'src> {
    members
        .iter()
        .find(|member| member.key() == field)
        .expect("validated object contains required field")
        .value()
}

fn required_string<'value, 'src>(
    members: &'value [crate::json::JsonMember<'src>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<&'value str, MachineStdArtifactShapeError> {
    let value = required_value(members, field);
    match value.kind() {
        JsonValueKind::Null => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::NullField { field },
        )),
        JsonValueKind::String => Ok(value.string_value().expect("kind checked string")),
        actual => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "string",
                actual,
            },
        )),
    }
}

fn parse_string_array(
    artifact: MachineStdArtifactKind,
    members: &[crate::json::JsonMember<'_>],
    path: &str,
    field: &'static str,
) -> Result<Vec<String>, MachineStdArtifactShapeError> {
    required_array(members, artifact, path, field)?
        .iter()
        .enumerate()
        .map(|(index, item)| {
            parse_string_value(artifact, item, &array_path(path, field, index), field)
                .map(str::to_owned)
        })
        .collect()
}

fn parse_string_value<'value>(
    artifact: MachineStdArtifactKind,
    value: &'value JsonValue<'_>,
    path: &str,
    field: &'static str,
) -> Result<&'value str, MachineStdArtifactShapeError> {
    match value.kind() {
        JsonValueKind::Null => Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::NullField { field },
        )),
        JsonValueKind::String => Ok(value.string_value().expect("kind checked string")),
        actual => Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "string",
                actual,
            },
        )),
    }
}

fn required_array<'value, 'src>(
    members: &'value [crate::json::JsonMember<'src>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<&'value [JsonValue<'src>], MachineStdArtifactShapeError> {
    let value = required_value(members, field);
    match value.kind() {
        JsonValueKind::Null => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::NullField { field },
        )),
        JsonValueKind::Array => Ok(value.array_elements().expect("kind checked array")),
        actual => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::ExpectedArray { actual },
        )),
    }
}

fn required_hash(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<Hash, MachineStdArtifactShapeError> {
    let value = required_string(members, artifact, path, field)?;
    parse_hash_string(value).map_err(|_| {
        shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidHashString { field },
        )
    })
}

fn required_bool(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<bool, MachineStdArtifactShapeError> {
    let value = required_value(members, field);
    match value.kind() {
        JsonValueKind::Null => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::NullField { field },
        )),
        JsonValueKind::Bool => Ok(value.bool_value().expect("kind checked bool")),
        actual => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "bool",
                actual,
            },
        )),
    }
}

fn required_hex_bytes(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<Vec<u8>, MachineStdArtifactShapeError> {
    let value = required_string(members, artifact, path, field)?;
    decode_lower_hex_bytes(value).map_err(|_| {
        shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidHexString { field },
        )
    })
}

fn required_module_name(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<Name, MachineStdArtifactShapeError> {
    let value = required_string(members, artifact, path, field)?;
    parse_module_name_wire(value).map_err(|_| {
        shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidName { field },
        )
    })
}

fn required_fully_qualified_name(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<Name, MachineStdArtifactShapeError> {
    let value = required_string(members, artifact, path, field)?;
    parse_fully_qualified_name_wire(value).map_err(|_| {
        shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::InvalidName { field },
        )
    })
}

fn required_u64(
    members: &[crate::json::JsonMember<'_>],
    artifact: MachineStdArtifactKind,
    path: &str,
    field: &'static str,
) -> Result<u64, MachineStdArtifactShapeError> {
    let value = required_value(members, field);
    match value.kind() {
        JsonValueKind::Null => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::NullField { field },
        )),
        JsonValueKind::Number => {
            let raw = value.number_raw().expect("kind checked number");
            parse_strict_u64_token(raw, u64::MAX).map_err(|error| {
                shape_error(
                    artifact,
                    &field_path(path, field),
                    MachineStdArtifactShapeErrorReason::InvalidUnsignedInteger {
                        field,
                        raw: raw.to_owned(),
                        error,
                    },
                )
            })
        }
        actual => Err(shape_error(
            artifact,
            &field_path(path, field),
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "unsigned integer",
                actual,
            },
        )),
    }
}

fn parse_optional_u64_value(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
    field: &'static str,
) -> Result<Option<u64>, MachineStdArtifactShapeError> {
    match value.kind() {
        JsonValueKind::Null => Ok(None),
        JsonValueKind::Number => {
            let raw = value.number_raw().expect("kind checked number");
            parse_strict_u64_token(raw, u64::MAX)
                .map(Some)
                .map_err(|error| {
                    shape_error(
                        artifact,
                        path,
                        MachineStdArtifactShapeErrorReason::InvalidUnsignedInteger {
                            field,
                            raw: raw.to_owned(),
                            error,
                        },
                    )
                })
        }
        actual => Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "unsigned integer or null",
                actual,
            },
        )),
    }
}

fn parse_optional_string_value(
    artifact: MachineStdArtifactKind,
    value: &JsonValue<'_>,
    path: &str,
    field: &'static str,
) -> Result<Option<String>, MachineStdArtifactShapeError> {
    match value.kind() {
        JsonValueKind::Null => Ok(None),
        JsonValueKind::String => Ok(Some(
            value
                .string_value()
                .expect("kind checked string")
                .to_owned(),
        )),
        actual => Err(shape_error(
            artifact,
            path,
            MachineStdArtifactShapeErrorReason::TypeMismatch {
                field,
                expected: "string or null",
                actual,
            },
        )),
    }
}

fn decode_lower_hex_bytes(value: &str) -> Result<Vec<u8>, ()> {
    if !value.len().is_multiple_of(2) {
        return Err(());
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|chunk| {
            let high = lowercase_hex_value(chunk[0])?;
            let low = lowercase_hex_value(chunk[1])?;
            Ok((high << 4) | low)
        })
        .collect()
}

fn lowercase_hex_value(byte: u8) -> Result<u8, ()> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(()),
    }
}

fn shape_error(
    artifact: MachineStdArtifactKind,
    path: &str,
    reason: MachineStdArtifactShapeErrorReason,
) -> MachineStdArtifactShapeError {
    MachineStdArtifactShapeError {
        artifact,
        path: path.to_owned(),
        reason,
    }
}

fn field_path(path: &str, field: &str) -> String {
    format!("{path}.{field}")
}

fn array_path(path: &str, field: &str, index: usize) -> String {
    format!("{path}.{field}[{index}]")
}

fn canonical_package_root(package_root: &Path) -> Result<PathBuf, MachineStdReleaseLoaderError> {
    fs::canonicalize(package_root).map_err(|source| {
        MachineStdReleaseLoaderError::InvalidPackageRoot {
            path: package_root.to_path_buf(),
            source,
        }
    })
}

fn read_and_decode_std_modules(
    package_root: &Path,
    locators: &[MachineStdModuleLocator],
) -> Result<BTreeMap<Name, DecodedStdModule>, MachineStdReleaseLoaderError> {
    let mut decoded = BTreeMap::new();
    for locator in locators {
        let (resolved_path, certificate_bytes) = read_locator_certificate(package_root, locator)?;
        let certificate_bytes_hash = sha256(&certificate_bytes);
        let cert = decode_module_cert(&certificate_bytes).map_err(|source| {
            MachineStdReleaseLoaderError::DecodeFailed {
                module: locator.module.clone(),
                source: Box::new(source),
            }
        })?;
        if cert.header.module != locator.module {
            return Err(MachineStdReleaseLoaderError::ModuleNameMismatch {
                expected: locator.module.clone(),
                actual: cert.header.module.clone(),
            });
        }
        decoded.insert(
            locator.module.clone(),
            DecodedStdModule {
                locator: locator.clone(),
                resolved_path,
                certificate_bytes,
                certificate_bytes_hash,
                cert,
            },
        );
    }
    Ok(decoded)
}

fn read_locator_certificate(
    package_root: &Path,
    locator: &MachineStdModuleLocator,
) -> Result<(PathBuf, Vec<u8>), MachineStdReleaseLoaderError> {
    let path = join_posix_relative_path(package_root, &locator.relative_path);
    let resolved = fs::canonicalize(&path).map_err(|source| {
        if source.kind() == io::ErrorKind::NotFound {
            MachineStdReleaseLoaderError::MissingCertificateFile {
                module: locator.module.clone(),
                path: path.clone(),
                source,
            }
        } else {
            MachineStdReleaseLoaderError::ReadCertificateFile {
                module: locator.module.clone(),
                path: path.clone(),
                source,
            }
        }
    })?;
    if !resolved.starts_with(package_root) {
        return Err(MachineStdReleaseLoaderError::SymlinkEscape {
            module: locator.module.clone(),
            path,
            resolved,
            package_root: package_root.to_path_buf(),
        });
    }
    let bytes = fs::read(&resolved).map_err(|source| {
        MachineStdReleaseLoaderError::ReadCertificateFile {
            module: locator.module.clone(),
            path: resolved.clone(),
            source,
        }
    })?;
    Ok((resolved, bytes))
}

fn join_posix_relative_path(root: &Path, relative_path: &str) -> PathBuf {
    let mut path = root.to_path_buf();
    for component in relative_path.split('/') {
        path.push(component);
    }
    path
}

fn validate_import_graph(
    modules: &BTreeMap<Name, DecodedStdModule>,
) -> Result<(), MachineStdReleaseLoaderError> {
    let mut keys = BTreeSet::new();
    for module in modules.values() {
        keys.insert(CertificateKey {
            module: module.cert.header.module.clone(),
            export_hash: module.cert.hashes.export_hash,
            certificate_hash: module.cert.hashes.certificate_hash,
        });
    }

    for module in modules.values() {
        for import in &module.cert.imports {
            let certificate_hash = import.certificate_hash.ok_or_else(|| {
                MachineStdReleaseLoaderError::MissingImportCertificateHash {
                    owner: module.cert.header.module.clone(),
                    imported_module: import.module.clone(),
                }
            })?;
            if !modules.contains_key(&import.module) {
                return Err(MachineStdReleaseLoaderError::UnresolvedImport {
                    owner: module.cert.header.module.clone(),
                    imported_module: import.module.clone(),
                });
            }
            let key = CertificateKey {
                module: import.module.clone(),
                export_hash: import.export_hash,
                certificate_hash,
            };
            if !keys.contains(&key) {
                return Err(MachineStdReleaseLoaderError::ImportHashMismatch {
                    owner: module.cert.header.module.clone(),
                    imported_module: import.module.clone(),
                });
            }
        }
    }
    Ok(())
}

fn topological_verification_order(
    modules: &BTreeMap<Name, DecodedStdModule>,
) -> Result<Vec<Name>, MachineStdReleaseLoaderError> {
    let mut remaining = modules.keys().cloned().collect::<BTreeSet<_>>();
    let mut order = Vec::new();

    while !remaining.is_empty() {
        let mut ready = Vec::new();
        for module in &remaining {
            let record = modules
                .get(module)
                .expect("remaining module came from decoded module table");
            if record
                .cert
                .imports
                .iter()
                .all(|import| !remaining.contains(&import.module))
            {
                ready.push(module.clone());
            }
        }

        let next = ready
            .into_iter()
            .min_by(compare_module_names)
            .ok_or_else(|| {
                let module = remaining
                    .iter()
                    .min_by(|lhs, rhs| compare_module_names(lhs, rhs))
                    .expect("remaining is non-empty")
                    .clone();
                MachineStdReleaseLoaderError::ImportCycle { module }
            })?;
        remaining.remove(&next);
        order.push(next);
    }

    Ok(order)
}

fn compare_module_names(lhs: &Name, rhs: &Name) -> std::cmp::Ordering {
    let lhs_bytes = module_name_canonical_bytes(lhs).unwrap_or_default();
    let rhs_bytes = module_name_canonical_bytes(rhs).unwrap_or_default();
    lhs_bytes.cmp(&rhs_bytes)
}

fn module_name_canonical_bytes(module: &Name) -> Result<Vec<u8>, MachineStdReleaseLoaderError> {
    machine_api_name_canonical_bytes(module).map_err(|source| {
        MachineStdReleaseLoaderError::InvalidCanonicalModuleName {
            module: module.clone(),
            source: Box::new(source),
        }
    })
}

fn verify_decoded_modules(
    decoded: BTreeMap<Name, DecodedStdModule>,
    verification_order: Vec<Name>,
    policy: AxiomPolicy,
) -> Result<MachineStdLoadedRelease, MachineStdReleaseLoaderError> {
    let mut session = VerifierSession::new();
    let mut verified_by_module = BTreeMap::new();

    for module in &verification_order {
        let record = decoded
            .get(module)
            .expect("verification order came from decoded module table");
        let verified = verify_module_cert(&record.certificate_bytes, &mut session, &policy)
            .map_err(|source| MachineStdReleaseLoaderError::VerifyFailed {
                module: module.clone(),
                source: Box::new(source),
            })?;
        if verified.module() != module
            || verified.export_hash() != record.cert.hashes.export_hash
            || verified.certificate_hash() != record.cert.hashes.certificate_hash
        {
            return Err(MachineStdReleaseLoaderError::VerifiedIdentityMismatch {
                module: module.clone(),
            });
        }
        verified_by_module.insert(module.clone(), verified);
    }

    let mut modules = Vec::new();
    for locator in machine_std_mvp_module_locators() {
        let record = decoded
            .get(&locator.module)
            .expect("validated locators contain every MVP module");
        let verified_module = verified_by_module
            .remove(&locator.module)
            .expect("every decoded module was verified");
        modules.push(MachineStdLoadedModule {
            module: locator.module.clone(),
            locator_path: record.locator.relative_path.clone(),
            resolved_path: record.resolved_path.clone(),
            certificate_bytes: record.certificate_bytes.clone(),
            certificate_bytes_hash: record.certificate_bytes_hash,
            expected_export_hash: record.cert.hashes.export_hash,
            expected_certificate_hash: record.cert.hashes.certificate_hash,
            axiom_report_hash: record.cert.hashes.axiom_report_hash,
            imports: verified_module.imports().to_vec(),
            verified_module,
        });
    }

    let module_index = modules
        .iter()
        .enumerate()
        .map(|(index, module)| (module.module.clone(), index))
        .collect();

    Ok(MachineStdLoadedRelease {
        modules,
        module_index,
        verification_order,
    })
}

fn machine_std_kernel_check_profile_canonical_bytes(profile: &str) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string(&mut out, MACHINE_TACTIC_KERNEL_CHECK_PROFILE_TAG);
    encode_string(&mut out, STD_CORE_SPEC_ID);
    encode_string(&mut out, STD_KERNEL_SEMANTICS_PROFILE_ID);
    encode_string(&mut out, STD_REDUCTION_PROFILE_ID);
    encode_string(&mut out, STD_UNIVERSE_PROFILE_ID);
    let builtin_profile_id = match profile {
        KERNEL_CHECK_PROFILE_BUILTIN_NAT_EQ_REC => STD_KERNEL_BUILTIN_NAT_EQ_REC_PROFILE_ID,
        STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE => STD_KERNEL_BUILTIN_NONE_PROFILE_ID,
        other => other,
    };
    encode_string(&mut out, builtin_profile_id);
    out
}

fn encode_verified_import_key(
    out: &mut Vec<u8>,
    key: &VerifiedImportKey,
) -> Result<(), MachineStdCanonicalBytesError> {
    encode_name(out, &key.module)?;
    encode_hash(out, &key.export_hash);
    encode_hash(out, &key.certificate_hash);
    Ok(())
}

fn verified_import_key_canonical_bytes(
    key: &VerifiedImportKey,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_verified_import_key(&mut out, key)?;
    Ok(out)
}

fn encode_import_certificate_key(
    out: &mut Vec<u8>,
    certificate: &MachineStdImportCertificate,
) -> Result<(), MachineStdCanonicalBytesError> {
    encode_name(out, &certificate.module)?;
    encode_hash(out, &certificate.expected_export_hash);
    encode_hash(out, &certificate.expected_certificate_hash);
    Ok(())
}

fn encode_simp_rule_ref(
    out: &mut Vec<u8>,
    rule: &SimpRuleRef,
) -> Result<(), MachineStdCanonicalBytesError> {
    encode_name(out, &rule.name)?;
    encode_hash(out, &rule.decl_interface_hash);
    encode_rewrite_direction(out, rule.direction);
    Ok(())
}

fn encode_rewrite_direction(out: &mut Vec<u8>, direction: RewriteDirection) {
    out.push(match direction {
        RewriteDirection::Forward => 0x00,
        RewriteDirection::Backward => 0x01,
    });
}

fn encode_option_eq_family(
    out: &mut Vec<u8>,
    value: Option<&EqFamilyRef>,
) -> Result<(), MachineStdCanonicalBytesError> {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_name(out, &value.eq_name)?;
            encode_hash(out, &value.eq_interface_hash);
            encode_name(out, &value.refl_name)?;
            encode_hash(out, &value.refl_interface_hash);
            encode_name(out, &value.rec_name)?;
            encode_hash(out, &value.rec_interface_hash);
        }
        None => out.push(0x00),
    }
    Ok(())
}

fn encode_option_nat_family(
    out: &mut Vec<u8>,
    value: Option<&NatFamilyRef>,
) -> Result<(), MachineStdCanonicalBytesError> {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_name(out, &value.nat_name)?;
            encode_hash(out, &value.nat_interface_hash);
            encode_name(out, &value.zero_name)?;
            encode_hash(out, &value.zero_interface_hash);
            encode_name(out, &value.succ_name)?;
            encode_hash(out, &value.succ_interface_hash);
            encode_name(out, &value.rec_name)?;
            encode_hash(out, &value.rec_interface_hash);
        }
        None => out.push(0x00),
    }
    Ok(())
}

fn encode_option_global_ref_view(
    out: &mut Vec<u8>,
    value: Option<&MachineStdGlobalRefView>,
) -> Result<(), MachineStdCanonicalBytesError> {
    match value {
        Some(value) => {
            out.push(0x01);
            out.extend(machine_std_global_ref_view_canonical_bytes(value)?);
        }
        None => out.push(0x00),
    }
    Ok(())
}

fn encode_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_uvar(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_option_string(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_string(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_option_hash(out: &mut Vec<u8>, value: Option<&Hash>) {
    match value {
        Some(value) => {
            out.push(0x01);
            encode_hash(out, value);
        }
        None => out.push(0x00),
    }
}

fn encode_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn theorem_kind_byte(kind: MachineStdTheoremKind) -> u8 {
    match kind {
        MachineStdTheoremKind::Theorem => 0x00,
        MachineStdTheoremKind::Axiom => 0x01,
    }
}

fn theorem_mode_byte(mode: MachineTheoremMode) -> u8 {
    match mode {
        MachineTheoremMode::Exact => 0x00,
        MachineTheoremMode::Apply => 0x01,
        MachineTheoremMode::Rw => 0x02,
        MachineTheoremMode::Simp => 0x03,
        MachineTheoremMode::ConstructorSupport => 0x04,
        MachineTheoremMode::InductionSupport => 0x05,
        MachineTheoremMode::TypeAware => 0x06,
        MachineTheoremMode::Lexical => 0x07,
        MachineTheoremMode::GraphAware => 0x08,
        MachineTheoremMode::Embedding => 0x09,
        MachineTheoremMode::ProofAnalogy => 0x0a,
        MachineTheoremMode::PremiseSet => 0x0b,
    }
}

fn theorem_attribute_byte(attribute: MachineStdAttribute) -> u8 {
    match attribute {
        MachineStdAttribute::Simp => 0x00,
        MachineStdAttribute::Rw => 0x01,
        MachineStdAttribute::Intro => 0x02,
        MachineStdAttribute::Elim => 0x03,
        MachineStdAttribute::Apply => 0x04,
        MachineStdAttribute::Refl => 0x05,
        MachineStdAttribute::Trans => 0x06,
        MachineStdAttribute::Congr => 0x07,
    }
}

fn human_std_theorem_category_byte(category: HumanStdTheoremCategory) -> u8 {
    match category {
        HumanStdTheoremCategory::Exact => 0x00,
        HumanStdTheoremCategory::Apply => 0x01,
        HumanStdTheoremCategory::Rw => 0x02,
        HumanStdTheoremCategory::Simp => 0x03,
        HumanStdTheoremCategory::Intro => 0x04,
        HumanStdTheoremCategory::Elim => 0x05,
    }
}

fn human_std_display_attribute_byte(attribute: HumanStdTheoremDisplayAttribute) -> u8 {
    match attribute {
        HumanStdTheoremDisplayAttribute::Simp => 0x00,
        HumanStdTheoremDisplayAttribute::Rw => 0x01,
        HumanStdTheoremDisplayAttribute::Apply => 0x02,
        HumanStdTheoremDisplayAttribute::Intro => 0x03,
        HumanStdTheoremDisplayAttribute::Elim => 0x04,
    }
}

fn human_std_dependency_kind_byte(kind: HumanStdDependencyKind) -> u8 {
    match kind {
        HumanStdDependencyKind::StatementHead => 0x00,
        HumanStdDependencyKind::StatementConstant => 0x01,
        HumanStdDependencyKind::AxiomDependency => 0x02,
    }
}

fn rewrite_safety_byte(safety: MachineStdRewriteSafety) -> u8 {
    match safety {
        MachineStdRewriteSafety::SimpSafe => 0x00,
        MachineStdRewriteSafety::RwOnly => 0x01,
        MachineStdRewriteSafety::UnsafeForAutomation => 0x02,
    }
}

fn simp_rule_ref_canonical_bytes(
    rule: &SimpRuleRef,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_simp_rule_ref(&mut out, rule)?;
    Ok(out)
}

fn std_library_core_expr_hash(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
) -> Result<Hash, MachineStdCanonicalBytesError> {
    let payload = std_library_core_expr_canonical_bytes(loaded, owner, expr)?;
    let mut bytes = b"NPA-TERM-0.1".to_vec();
    bytes.extend(payload);
    Ok(sha256(&bytes))
}

fn std_library_core_expr_canonical_bytes(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
) -> Result<Vec<u8>, MachineStdCanonicalBytesError> {
    let mut out = Vec::new();
    encode_std_library_core_expr(&mut out, loaded, owner, expr)?;
    Ok(out)
}

fn std_library_core_level_hash(level: &Level) -> Result<Hash, MachineStdCanonicalBytesError> {
    let mut payload = Vec::new();
    encode_std_library_core_level(&mut payload, &normalize_level(level.clone()))?;
    let mut bytes = b"NPA-LEVEL-0.1".to_vec();
    bytes.extend(payload);
    Ok(sha256(&bytes))
}

fn encode_std_library_core_expr(
    out: &mut Vec<u8>,
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    expr: &Expr,
) -> Result<(), MachineStdCanonicalBytesError> {
    match expr {
        Expr::Sort(level) => {
            out.push(0x00);
            encode_hash(out, &std_library_core_level_hash(level)?);
        }
        Expr::BVar(index) => {
            out.push(0x01);
            encode_uvar(out, u64::from(*index));
        }
        Expr::Const { name, levels } => {
            out.push(0x02);
            let global_ref = std_library_global_ref_for_const(loaded, owner, name)?;
            encode_std_library_global_ref(out, &global_ref);
            encode_uvar(out, levels.len() as u64);
            for level in levels {
                encode_hash(out, &std_library_core_level_hash(level)?);
            }
        }
        Expr::App(fun, arg) => {
            out.push(0x03);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, fun)?);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, arg)?);
        }
        Expr::Lam { ty, body, .. } => {
            out.push(0x04);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, ty)?);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, body)?);
        }
        Expr::Pi { ty, body, .. } => {
            out.push(0x05);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, ty)?);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, body)?);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            out.push(0x06);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, ty)?);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, value)?);
            encode_hash(out, &std_library_core_expr_hash(loaded, owner, body)?);
        }
    }
    Ok(())
}

fn std_library_global_ref_for_const(
    loaded: &MachineStdLoadedRelease,
    owner: &MachineStdLoadedModule,
    name: &str,
) -> Result<GlobalRef, MachineStdCanonicalBytesError> {
    let name = Name::from_dotted(name);
    let name_id = std_library_name_id(owner, &name)?;
    for (decl_index, decl) in owner.verified_module.declarations().iter().enumerate() {
        if std_library_decl_name(owner, decl).as_ref() == Some(&name) {
            return Ok(GlobalRef::Local { decl_index });
        }
        if inductive_decl_contains_generated(owner, decl, &name, None).unwrap_or(false) {
            return Ok(GlobalRef::LocalGenerated {
                decl_index,
                name: name_id,
            });
        }
    }
    for (import_index, import) in owner.imports.iter().enumerate() {
        let Some(imported) = loaded.module(&import.module) else {
            continue;
        };
        if let Some(export) = unique_public_export_by_name(imported, &name) {
            return Ok(GlobalRef::Imported {
                import_index,
                name: name_id,
                decl_interface_hash: export.decl_interface_hash,
            });
        }
    }
    Err(MachineStdCanonicalBytesError::InvalidCoreGlobalRef {
        module: owner.module.clone(),
        name,
    })
}

fn std_library_decl_name(module: &MachineStdLoadedModule, decl: &DeclCert) -> Option<Name> {
    let name_id = match &decl.decl {
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
    module.verified_module.name_table().get(name_id).cloned()
}

fn std_library_name_id(
    owner: &MachineStdLoadedModule,
    name: &Name,
) -> Result<usize, MachineStdCanonicalBytesError> {
    owner
        .verified_module
        .name_table()
        .iter()
        .position(|entry| entry == name)
        .ok_or_else(|| MachineStdCanonicalBytesError::InvalidCoreGlobalRef {
            module: owner.module.clone(),
            name: name.clone(),
        })
}

fn encode_std_library_global_ref(out: &mut Vec<u8>, global_ref: &GlobalRef) {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_uvar(out, *name as u64);
            encode_hash(out, decl_interface_hash);
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_uvar(out, *import_index as u64);
            encode_uvar(out, *name as u64);
            encode_hash(out, decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_uvar(out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_uvar(out, *decl_index as u64);
            encode_uvar(out, *name as u64);
        }
    }
}

fn encode_std_library_core_level(
    out: &mut Vec<u8>,
    level: &Level,
) -> Result<(), MachineStdCanonicalBytesError> {
    match level {
        Level::Zero => out.push(0x00),
        Level::Succ(inner) => {
            out.push(0x01);
            encode_hash(out, &std_library_core_level_hash(inner)?);
        }
        Level::Max(lhs, rhs) => {
            out.push(0x02);
            encode_hash(out, &std_library_core_level_hash(lhs)?);
            encode_hash(out, &std_library_core_level_hash(rhs)?);
        }
        Level::IMax(lhs, rhs) => {
            out.push(0x03);
            encode_hash(out, &std_library_core_level_hash(lhs)?);
            encode_hash(out, &std_library_core_level_hash(rhs)?);
        }
        Level::Param(name) => {
            out.push(0x04);
            encode_name(out, &Name::from_dotted(name))?;
        }
    }
    Ok(())
}

fn encode_string(out: &mut Vec<u8>, value: &str) {
    encode_uvar(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn encode_name(out: &mut Vec<u8>, name: &Name) -> Result<(), MachineStdCanonicalBytesError> {
    let bytes = machine_api_name_canonical_bytes(name).map_err(|source| {
        MachineStdCanonicalBytesError::InvalidName {
            name: name.clone(),
            source: Box::new(source),
        }
    })?;
    out.extend(bytes);
    Ok(())
}

fn encode_hash(out: &mut Vec<u8>, hash: &Hash) {
    out.extend_from_slice(hash);
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn sha256(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut out = [0; 32];
    out.copy_from_slice(&digest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        adapter::machine_tactic_validate_machine_tactic_candidate,
        run_machine_replay_request, run_machine_tactic_batch_request, run_machine_verify_request,
        search_machine_theorems_for_goal,
        types::{format_goal_id_wire, format_hash_string},
        MachineApiResponseEnvelope, MachineSuggestedCandidateStatus,
        MachineTacticBatchItemResponse, SnapshotId,
    };
    use npa_cert::{build_module_cert, encode_module_cert, CoreModule};
    use npa_checker_ref::{
        check_certificate, ReferenceCheckErrorKind, ReferenceCheckReason, ReferenceCheckResult,
        ReferenceCheckedModule, ReferenceCheckerPolicy, ReferenceImportStore, ReferenceModuleName,
        ReferenceTrustMode,
    };
    use npa_frontend::{canonicalize_machine_term_source, parse_human_module, FileId, HumanItem};
    use npa_kernel::{
        eq, eq_inductive, eq_rec_type, eq_refl, nat, nat_inductive, nat_succ, nat_zero, type0,
        Binder, ConstructorDecl, Ctx, Decl, Env, Expr, InductiveDecl, Level, RecursorDecl,
        Reducibility,
    };
    use npa_tactic::{CandidateApplyArg, GoalId, MachineTacticCandidate, RewriteSite, TacticHead};
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };

    #[test]
    fn loads_valid_mvp_certificate_package() {
        let package = TestPackage::new("valid_mvp_certificate_package");
        write_valid_mvp_package(package.path());

        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        assert_eq!(loaded.modules().len(), 4);
        assert_eq!(
            loaded
                .modules()
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Nat", "Std.List", "Std.Logic", "Std.Algebra.Basic"]
        );
        assert_eq!(
            loaded
                .verification_order()
                .iter()
                .map(Name::as_dotted)
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        for module in loaded.modules() {
            assert_eq!(
                module.certificate_bytes_hash,
                sha256(&module.certificate_bytes)
            );
            assert_eq!(
                module.expected_certificate_hash,
                module.verified_module.certificate_hash()
            );
            assert_eq!(
                module.expected_export_hash,
                module.verified_module.export_hash()
            );
        }

        let logic = loaded.module(&Name::from_dotted("Std.Logic")).unwrap();
        assert!(
            logic.imports.is_empty(),
            "Std.Logic must not encode Core/prelude as an ordinary ImportEntry"
        );
        assert_eq!(export_entry(logic, "Eq").kind, ExportKind::Inductive);
        assert_eq!(export_entry(logic, "Eq.refl").kind, ExportKind::Constructor);
        assert_eq!(export_entry(logic, "Eq.rec").kind, ExportKind::Axiom);
        assert_eq!(export_entry(logic, "Not").kind, ExportKind::Def);
        for inductive in ["True", "False", "And", "Or", "Iff", "Exists"] {
            assert_eq!(export_entry(logic, inductive).kind, ExportKind::Inductive);
        }
        for recursor in [
            "True.rec",
            "False.rec",
            "And.rec",
            "Or.rec",
            "Iff.rec",
            "Exists.rec",
        ] {
            assert_eq!(export_entry(logic, recursor).kind, ExportKind::Recursor);
        }
        for theorem in ["Eq.symm", "Eq.trans", "Eq.subst", "Eq.congrArg"] {
            let entry = export_entry(logic, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert_eq!(
                entry
                    .axiom_dependencies
                    .iter()
                    .map(|axiom| logic.verified_module.name_table()[axiom.name].as_dotted())
                    .collect::<Vec<_>>(),
                vec!["Eq.rec"]
            );
        }
        for theorem in [
            "False.elim",
            "absurd",
            "not_intro",
            "not_elim",
            "And.left",
            "And.right",
            "And.intro",
            "Or.elim",
            "Or.inl",
            "Or.inr",
            "Iff.mp",
            "Iff.mpr",
            "Iff.refl",
            "Iff.symm",
            "Iff.trans",
            "Exists.intro",
            "Exists.elim",
        ] {
            let entry = export_entry(logic, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} must stay constructive"
            );
        }
        assert!(!logic
            .verified_module
            .name_table()
            .iter()
            .any(|name| matches!(
                name.as_dotted().as_str(),
                "Classical.choice" | "funext" | "propext"
            )));

        let axiom_report = mvp_axiom_report_for(&loaded);
        let logic_axioms = axiom_report
            .modules
            .iter()
            .find(|module| module.module == Name::from_dotted("Std.Logic"))
            .unwrap();
        assert_eq!(
            logic_axioms
                .module_axioms
                .iter()
                .map(|axiom| axiom.name.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Eq.rec"]
        );

        let theorem_index = generate_machine_std_mvp_theorem_index(&loaded).unwrap();
        assert!(!theorem_index
            .entries
            .iter()
            .any(|entry| entry.global_ref.name == Name::from_dotted("Eq.refl")));
        for theorem in ["Eq.trans", "And.intro", "False.elim"] {
            let entry = theorem_index_entry(&theorem_index, theorem);
            assert!(entry.modes.contains(&MachineTheoremMode::Apply));
        }
        assert_eq!(
            theorem_index_entry(&theorem_index, "False.elim").universe_params,
            Vec::<String>::new()
        );

        let nat_module = loaded.module(&Name::from_dotted("Std.Nat")).unwrap();
        assert_eq!(
            nat_module
                .imports
                .iter()
                .map(|import| import.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic"]
        );
        assert_eq!(export_entry(nat_module, "Nat").kind, ExportKind::Inductive);
        assert_eq!(
            export_entry(nat_module, "Nat.zero").kind,
            ExportKind::Constructor
        );
        assert_eq!(
            export_entry(nat_module, "Nat.succ").kind,
            ExportKind::Constructor
        );
        assert_eq!(
            export_entry(nat_module, "Nat.rec").kind,
            ExportKind::Recursor
        );
        assert_eq!(export_entry(nat_module, "Nat.one").kind, ExportKind::Def);
        assert_eq!(export_entry(nat_module, "Nat.pred").kind, ExportKind::Def);
        assert_eq!(export_entry(nat_module, "Nat.add").kind, ExportKind::Def);
        assert_eq!(export_entry(nat_module, "Nat.mul").kind, ExportKind::Def);
        for theorem in ["Nat.pred_zero", "Nat.pred_succ"] {
            let entry = export_entry(nat_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} must be proved by definitional equality without new axioms"
            );
        }
        for theorem in ["Nat.add_zero", "Nat.add_succ"] {
            let entry = export_entry(nat_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} must be proved by definitional equality without new axioms"
            );
        }
        for theorem in ["Nat.mul_zero", "Nat.mul_succ"] {
            let entry = export_entry(nat_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} must be proved by definitional equality without new axioms"
            );
        }
        for theorem in [
            "Nat.zero_add",
            "Nat.succ_add",
            "Nat.add_assoc",
            "Nat.add_comm",
            "Nat.zero_mul",
            "Nat.succ_mul",
            "Nat.mul_comm",
            "Nat.left_distrib",
            "Nat.mul_assoc",
            "Nat.right_distrib",
        ] {
            let entry = export_entry(nat_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert_eq!(
                entry
                    .axiom_dependencies
                    .iter()
                    .map(|axiom| nat_module.verified_module.name_table()[axiom.name].as_dotted())
                    .collect::<Vec<_>>(),
                vec!["Eq.rec"],
                "{theorem} should only depend on the standard Eq.rec axiom through induction/rewrite proof terms"
            );
        }
        let nat_axioms = axiom_report
            .modules
            .iter()
            .find(|module| module.module == Name::from_dotted("Std.Nat"))
            .unwrap();
        assert_eq!(
            nat_axioms
                .module_axioms
                .iter()
                .map(|axiom| axiom.name.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Eq.rec"],
            "Std.Nat may only depend on the standard Eq.rec axiom from Std.Logic"
        );

        let list_module = loaded.module(&Name::from_dotted("Std.List")).unwrap();
        assert_eq!(
            list_module
                .imports
                .iter()
                .map(|import| import.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat"]
        );
        assert_eq!(
            export_entry(list_module, "List").kind,
            ExportKind::Inductive
        );
        assert_eq!(
            export_entry(list_module, "List.nil").kind,
            ExportKind::Constructor
        );
        assert_eq!(
            export_entry(list_module, "List.cons").kind,
            ExportKind::Constructor
        );
        assert_eq!(
            export_entry(list_module, "List.rec").kind,
            ExportKind::Recursor
        );
        assert_eq!(
            export_entry(list_module, "List.append").kind,
            ExportKind::Def
        );
        assert_eq!(
            export_entry(list_module, "List.length").kind,
            ExportKind::Def
        );
        assert_eq!(export_entry(list_module, "List.map").kind, ExportKind::Def);
        assert_eq!(
            export_entry(list_module, "List.foldr").kind,
            ExportKind::Def
        );
        for theorem in [
            "List.nil_append",
            "List.cons_append",
            "List.length_nil",
            "List.length_cons",
            "List.map_nil",
            "List.map_cons",
            "List.foldr_nil",
            "List.foldr_cons",
        ] {
            let entry = export_entry(list_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} must be proved by definitional equality without new axioms"
            );
        }
        for theorem in [
            "List.append_nil",
            "List.append_assoc",
            "List.length_append",
            "List.map_id",
            "List.map_comp",
        ] {
            let entry = export_entry(list_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert_eq!(
                entry
                    .axiom_dependencies
                    .iter()
                    .map(|axiom| list_module.verified_module.name_table()[axiom.name].as_dotted())
                    .collect::<Vec<_>>(),
                vec!["Eq.rec"],
                "{theorem} should only depend on the standard Eq.rec axiom through induction/rewrite proof terms"
            );
        }

        let algebra_module = loaded
            .module(&Name::from_dotted("Std.Algebra.Basic"))
            .unwrap();
        assert_eq!(
            algebra_module
                .imports
                .iter()
                .map(|import| import.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic"]
        );
        for property in [
            "Associative",
            "Commutative",
            "LeftIdentity",
            "RightIdentity",
        ] {
            assert_eq!(export_entry(algebra_module, property).kind, ExportKind::Def);
        }
        for inductive in ["IsSemigroup", "IsMonoid", "IsCommMonoid"] {
            assert_eq!(
                export_entry(algebra_module, inductive).kind,
                ExportKind::Inductive
            );
        }
        for constructor in ["IsSemigroup.intro", "IsMonoid.intro", "IsCommMonoid.intro"] {
            assert_eq!(
                export_entry(algebra_module, constructor).kind,
                ExportKind::Constructor
            );
        }
        for recursor in ["IsSemigroup.rec", "IsMonoid.rec", "IsCommMonoid.rec"] {
            assert_eq!(
                export_entry(algebra_module, recursor).kind,
                ExportKind::Recursor
            );
        }
        for theorem in [
            "IsMonoid.assoc",
            "IsMonoid.left_id",
            "IsMonoid.right_id",
            "IsCommMonoid.assoc",
            "IsCommMonoid.comm",
            "IsCommMonoid.left_id",
            "IsCommMonoid.right_id",
        ] {
            let entry = export_entry(algebra_module, theorem);
            assert_eq!(entry.kind, ExportKind::Theorem);
            assert!(
                entry.axiom_dependencies.is_empty(),
                "{theorem} should be a direct projection with no axiom dependencies"
            );
        }
        let identity_unique = export_entry(algebra_module, "identity_unique");
        assert_eq!(identity_unique.kind, ExportKind::Theorem);
        assert_eq!(
            identity_unique
                .axiom_dependencies
                .iter()
                .map(|axiom| algebra_module.verified_module.name_table()[axiom.name].as_dotted())
                .collect::<Vec<_>>(),
            vec!["Eq.rec"],
            "identity_unique should only use the standard Eq.rec axiom through Eq.symm/Eq.trans"
        );
        let algebra_axioms = axiom_report
            .modules
            .iter()
            .find(|module| module.module == Name::from_dotted("Std.Algebra.Basic"))
            .unwrap();
        assert_eq!(
            algebra_axioms
                .module_axioms
                .iter()
                .map(|axiom| axiom.name.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Eq.rec"],
            "Std.Algebra.Basic may only depend on the standard Eq.rec axiom from Std.Logic"
        );
        for forbidden in [
            "Semigroup",
            "Monoid",
            "CommMonoid",
            "Nat.add_is_comm_monoid",
        ] {
            assert!(
                !algebra_module
                    .verified_module
                    .name_table()
                    .iter()
                    .any(|name| name.as_dotted() == forbidden),
                "{forbidden} must not be exported by Std.Algebra.Basic"
            );
            assert!(
                !nat_module
                    .verified_module
                    .name_table()
                    .iter()
                    .any(|name| name.as_dotted() == forbidden),
                "{forbidden} must not be exported by Std.Nat"
            );
        }

        for theorem in ["IsMonoid.assoc", "IsCommMonoid.comm", "identity_unique"] {
            let entry = theorem_index_entry(&theorem_index, theorem);
            assert_eq!(
                entry.global_ref.module,
                Name::from_dotted("Std.Algebra.Basic")
            );
            assert!(entry.modes.contains(&MachineTheoremMode::Apply));
        }
    }

    #[test]
    fn fixes_mvp_source_layout_without_expanding_release_modules() {
        assert_eq!(machine_std_mvp_source_package_root(), "Std");

        let source_layout = machine_std_mvp_source_package_layout();
        assert_eq!(
            source_layout
                .iter()
                .map(|entry| entry.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        assert_eq!(
            source_layout
                .iter()
                .map(|entry| entry.source_relative_path.as_str())
                .collect::<Vec<_>>(),
            vec![
                "Std/Logic.npa",
                "Std/Nat.npa",
                "Std/List.npa",
                "Std/Algebra/Basic.npa"
            ]
        );
        assert_eq!(
            source_layout
                .iter()
                .map(|entry| entry.certificate_relative_path.as_str())
                .collect::<Vec<_>>(),
            vec![
                "Std/Logic.npcert",
                "Std/Nat.npcert",
                "Std/List.npcert",
                "Std/Algebra/Basic.npcert"
            ]
        );

        let release_modules = machine_std_mvp_module_locators()
            .iter()
            .map(|locator| locator.module.as_dotted())
            .collect::<Vec<_>>();
        assert_eq!(
            release_modules,
            vec!["Std.Nat", "Std.List", "Std.Logic", "Std.Algebra.Basic"]
        );

        let source_modules = source_layout
            .iter()
            .map(|entry| entry.module.as_dotted())
            .collect::<Vec<_>>();
        assert_ne!(source_modules, release_modules);

        // `Std.Nat.Basic` and `Std.Logic.Eq` are legacy Human/frontend fixture
        // module names. They may appear in tests, but not as Phase 6 release
        // modules or source-package roots.
        for legacy_fixture in ["Std.Nat.Basic", "Std.Logic.Eq"] {
            assert!(!release_modules.contains(&legacy_fixture.to_owned()));
            assert!(!source_modules.contains(&legacy_fixture.to_owned()));
        }
    }

    #[test]
    fn docs_pin_human_ai_stdlib_release_contracts() {
        let readme = include_str!(concat!("../../../", "README.md"));
        let spec = include_str!(concat!("../../../testdata/docs/", "npa-spec.md"));

        for module in ["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"] {
            assert_doc_contains(readme, module);
            assert_doc_contains(spec, module);
        }

        for name in human_source_simp_intent(STD_NAT_SIMP_PROFILE_ID)
            .into_iter()
            .chain(human_source_simp_intent(STD_LIST_SIMP_PROFILE_ID))
        {
            assert_doc_contains(spec, &name);
        }
        for name in human_source_rw_only_intent(STD_ALL_RW_PROFILE_ID) {
            assert_doc_contains(spec, &name);
        }

        for text in ["Eq.rec", "Std.Nat.Basic", "Std.Logic.Eq"] {
            assert_doc_contains(spec, text);
        }
        for text in [
            "imported Std.Logic Eq.rec",
            "module_axioms",
            "transitive_axioms",
        ] {
            assert_doc_contains(spec, text);
        }
        for text in [
            "Std.machine-release.json",
            "Std.machine-import-bundles.json",
            "Std.machine-theorem-index.json",
            "release/build artifact",
            "source_built_std_artifacts_feed_machine_release_sessions_retrieval_and_audit",
        ] {
            assert_doc_contains(spec, text);
        }
        for text in [
            "std.nat.mvp",
            "std.list.mvp",
            "std.all.mvp",
            "release/build artifact",
            "source layout fixtures",
        ] {
            assert_doc_contains(readme, text);
        }
        for text in [
            "source skeletons",
            "Rust core-module builders",
            "manifest fixes module membership/certificate paths",
            "source skeleton fixes import intent",
        ] {
            assert_doc_contains(spec, text);
        }
    }

    #[test]
    fn machine_release_identity_ignores_human_source_layout_and_debug_views() {
        let package = TestPackage::new("human_source_ignored_by_machine_release");
        write_valid_mvp_package(package.path());
        let loaded_before = load_machine_std_mvp_certificates(package.path()).unwrap();
        let import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded_before).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded_before);
        let release_before = release_manifest_for(&loaded_before, axiom_report.axiom_report_hash);
        let release_hash_before = machine_std_library_release_hash(&release_before).unwrap();
        let release_json = release_manifest_json(&release_before);
        let import_bundles_json = import_bundle_set_json(&import_bundles);
        let axiom_report_json = axiom_report_json(&axiom_report);

        write_poison_human_std_source_and_debug_files(package.path());

        let loaded_after = load_machine_std_mvp_certificates(package.path()).unwrap();
        let axiom_report_after = mvp_axiom_report_for(&loaded_after);
        let release_after =
            release_manifest_for(&loaded_after, axiom_report_after.axiom_report_hash);
        assert_eq!(
            machine_std_library_release_hash(&release_after).unwrap(),
            release_hash_before
        );

        let validated = load_machine_std_mvp_release_with_import_bundles_from_json(
            package.path(),
            &release_json,
            &import_bundles_json,
            &axiom_report_json,
        )
        .unwrap();
        assert_eq!(validated.std_library_release_hash, release_hash_before);
        assert_eq!(
            validated
                .loaded
                .modules()
                .iter()
                .map(|module| module.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Nat", "Std.List", "Std.Logic", "Std.Algebra.Basic"]
        );
    }

    #[test]
    fn rejects_bad_mvp_locator_membership_order_and_path() {
        let mut missing = machine_std_mvp_module_locators();
        missing.pop();
        assert!(matches!(
            validate_machine_std_mvp_locators(&missing),
            Err(MachineStdReleaseLoaderError::InvalidModuleMembership { .. })
        ));

        let mut extra = machine_std_mvp_module_locators();
        extra.push(MachineStdModuleLocator::new(
            Name::from_dotted("Std.Extra"),
            "Std/Extra.npcert",
        ));
        assert!(matches!(
            validate_machine_std_mvp_locators(&extra),
            Err(MachineStdReleaseLoaderError::InvalidModuleMembership { .. })
        ));

        let mut reordered = machine_std_mvp_module_locators();
        reordered.swap(0, 1);
        assert!(matches!(
            validate_machine_std_mvp_locators(&reordered),
            Err(MachineStdReleaseLoaderError::NonCanonicalModuleOrder { .. })
        ));

        let mut wrong_path = machine_std_mvp_module_locators();
        wrong_path[0].relative_path = "Std/NatWrong.npcert".to_owned();
        assert!(matches!(
            validate_machine_std_mvp_locators(&wrong_path),
            Err(MachineStdReleaseLoaderError::FixedPathMismatch { .. })
        ));
    }

    #[test]
    fn rejects_invalid_locator_paths() {
        let cases = [
            ("", MachineStdLocatorPathError::Empty),
            ("/Std/Nat.npcert", MachineStdLocatorPathError::Absolute),
            ("Std\\Nat.npcert", MachineStdLocatorPathError::Backslash),
            ("Std/Nat.npcert/", MachineStdLocatorPathError::TrailingSlash),
            (
                "Std//Nat.npcert",
                MachineStdLocatorPathError::DuplicateSlash,
            ),
            ("Std/./Nat.npcert", MachineStdLocatorPathError::DotComponent),
            (
                "Std/../Nat.npcert",
                MachineStdLocatorPathError::ParentComponent,
            ),
        ];
        for (path, expected) in cases {
            assert_eq!(validate_machine_std_locator_path(path), Err(expected));
        }
    }

    #[test]
    fn rejects_missing_certificate_file() {
        let package = TestPackage::new("missing_certificate_file");
        let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::MissingCertificateFile { .. }
        ));
    }

    #[test]
    fn rejects_core_or_prelude_import_entry_as_unresolved_release_import() {
        for imported in ["Core", "Prelude"] {
            let package = TestPackage::new(&format!("{}_import_entry", imported.to_lowercase()));
            let mut certs = mvp_certificate_bytes();
            let mut logic = decode_module_cert(certs.logic.as_slice()).unwrap();
            logic.imports.push(ImportEntry {
                module: Name::from_dotted(imported),
                export_hash: [0; 32],
                certificate_hash: Some([0; 32]),
            });
            certs.logic = encode_module_cert(&logic).unwrap();
            write_mvp_package(package.path(), &certs);

            let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
            assert!(matches!(
                err,
                MachineStdReleaseLoaderError::UnresolvedImport {
                    imported_module,
                    ..
                } if imported_module == Name::from_dotted(imported)
            ));
        }
    }

    #[test]
    fn rejects_release_import_cycles_before_verification() {
        let package = TestPackage::new("import_cycle");
        let mut certs = mvp_certificate_bytes();
        let mut logic = decode_module_cert(certs.logic.as_slice()).unwrap();
        let mut nat = decode_module_cert(certs.nat.as_slice()).unwrap();
        logic.imports.push(ImportEntry {
            module: Name::from_dotted("Std.Nat"),
            export_hash: nat.hashes.export_hash,
            certificate_hash: Some(nat.hashes.certificate_hash),
        });
        nat.imports.push(ImportEntry {
            module: Name::from_dotted("Std.Logic"),
            export_hash: logic.hashes.export_hash,
            certificate_hash: Some(logic.hashes.certificate_hash),
        });
        certs.logic = encode_module_cert(&logic).unwrap();
        certs.nat = encode_module_cert(&nat).unwrap();
        write_mvp_package(package.path(), &certs);

        let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::ImportCycle { .. }
        ));
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlink_escape_from_package_root() {
        use std::os::unix::fs::symlink;

        let package = TestPackage::new("symlink_escape");
        let outside = TestPackage::new("symlink_escape_outside");
        let certs = mvp_certificate_bytes();
        write_mvp_package(package.path(), &certs);
        fs::write(outside.path().join("Logic.npcert"), &certs.logic).unwrap();
        fs::remove_file(package.path().join(STD_LOGIC_PATH)).unwrap();
        symlink(
            outside.path().join("Logic.npcert"),
            package.path().join(STD_LOGIC_PATH),
        )
        .unwrap();

        let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::SymlinkEscape { .. }
        ));
    }

    #[test]
    fn loads_valid_mvp_release_manifest_and_axiom_report() {
        let package = TestPackage::new("valid_mvp_release_manifest");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);
        let release_json = release_manifest_json(&release);
        let axiom_report_json = axiom_report_json(&axiom_report);

        let validated = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_json,
            &axiom_report_json,
        )
        .unwrap();
        assert_eq!(validated.loaded.modules().len(), 4);
        assert_eq!(
            validated.axiom_report.axiom_report_hash,
            axiom_report.axiom_report_hash
        );
        assert_eq!(
            validated.std_library_release_hash,
            machine_std_library_release_hash(&validated.manifest).unwrap()
        );
    }

    #[test]
    fn generates_mvp_import_bundle_set_with_canonical_membership() {
        let package = TestPackage::new("mvp_import_bundle_set");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();

        let bundle_set = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();
        assert_eq!(
            bundle_set
                .bundles
                .iter()
                .map(|bundle| bundle.bundle_id.as_str())
                .collect::<Vec<_>>(),
            vec![
                STD_ALGEBRA_BASIC_BUNDLE_ID,
                STD_ALL_BUNDLE_ID,
                STD_LIST_BUNDLE_ID,
                STD_LOGIC_BUNDLE_ID,
                STD_NAT_BUNDLE_ID,
            ]
        );
        let list_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_LIST_BUNDLE_ID)
            .unwrap();
        assert_eq!(
            list_bundle
                .root_imports
                .iter()
                .map(|key| key.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.List", "Std.Logic"]
        );
        assert_eq!(
            list_bundle
                .import_closure
                .iter()
                .map(|certificate| certificate.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Nat", "Std.List", "Std.Logic"]
        );
        assert!(list_bundle.recommended_tactic_options.nat_family.is_none());

        let algebra_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_ALGEBRA_BASIC_BUNDLE_ID)
            .unwrap();
        assert_eq!(
            algebra_bundle
                .root_imports
                .iter()
                .map(|key| key.module.as_dotted())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["Std.Algebra.Basic".to_owned(), "Std.Logic".to_owned()])
        );
        assert_eq!(
            algebra_bundle
                .import_closure
                .iter()
                .map(|certificate| certificate.module.as_dotted())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["Std.Algebra.Basic".to_owned(), "Std.Logic".to_owned()])
        );
        assert!(algebra_bundle
            .recommended_tactic_options
            .nat_family
            .is_none());

        let nat_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        assert_eq!(
            nat_bundle
                .root_imports
                .iter()
                .map(|key| key.module.as_dotted())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["Std.Logic".to_owned(), "Std.Nat".to_owned()])
        );
        assert_eq!(
            nat_bundle
                .import_closure
                .iter()
                .map(|certificate| certificate.module.as_dotted())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["Std.Logic".to_owned(), "Std.Nat".to_owned()])
        );
        assert_nat_family_matches_std_nat_exports(
            &loaded,
            nat_bundle
                .recommended_tactic_options
                .nat_family
                .as_ref()
                .expect("std.nat.mvp should expose certificate-bound Nat family"),
        );
        let all_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_ALL_BUNDLE_ID)
            .unwrap();
        assert!(all_bundle.recommended_tactic_options.nat_family.is_some());
        let logic_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_LOGIC_BUNDLE_ID)
            .unwrap();
        assert!(logic_bundle.recommended_tactic_options.nat_family.is_none());

        let eq_rec_allow_axiom =
            machine_std_axiom_ref_to_wire(&std_logic_eq_rec_axiom_ref(&loaded).unwrap());
        assert!(bundle_set
            .bundles
            .iter()
            .all(|bundle| bundle.allow_axioms == vec![eq_rec_allow_axiom.clone()]));
        assert!(bundle_set.bundles.iter().all(|bundle| {
            crate::types::KernelCheckProfileId::parse(
                &bundle.recommended_tactic_options.kernel_check_profile,
            )
            .is_ok()
        }));
        assert_eq!(
            bundle_set.import_bundles_hash,
            machine_std_import_bundle_set_hash(&bundle_set).unwrap()
        );
    }

    #[test]
    fn generates_mvp_rewrite_and_simp_profile_sets() {
        let package = TestPackage::new("mvp_rewrite_simp_profiles");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();

        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        validate_machine_std_mvp_rewrite_profile_set(&rewrite_profiles, &rewrite_profiles).unwrap();
        assert_eq!(
            rewrite_profiles
                .profiles
                .iter()
                .map(|profile| (
                    profile.profile_id.as_str(),
                    profile.required_import_bundle_id.as_str(),
                    profile.descriptors.len(),
                    profile
                        .descriptors
                        .iter()
                        .filter(|descriptor| descriptor.safety == MachineStdRewriteSafety::SimpSafe)
                        .count(),
                    profile
                        .descriptors
                        .iter()
                        .filter(|descriptor| descriptor.safety == MachineStdRewriteSafety::RwOnly)
                        .count(),
                ))
                .collect::<Vec<_>>(),
            vec![
                (STD_ALL_RW_PROFILE_ID, STD_ALL_BUNDLE_ID, 22, 18, 4),
                (STD_LIST_RW_PROFILE_ID, STD_LIST_BUNDLE_ID, 12, 10, 2),
                (STD_LOGIC_RW_PROFILE_ID, STD_LOGIC_BUNDLE_ID, 0, 0, 0),
                (STD_NAT_RW_PROFILE_ID, STD_NAT_BUNDLE_ID, 10, 8, 2),
            ]
        );
        assert!(rewrite_profiles
            .profiles
            .iter()
            .flat_map(|profile| &profile.descriptors)
            .all(|descriptor| descriptor.direction == RewriteDirection::Forward));
        assert!(rewrite_profiles.profiles.iter().all(|profile| {
            profile.profile_hash == machine_std_rewrite_profile_hash(profile).unwrap()
        }));
        assert_eq!(
            rewrite_profiles.rewrite_profiles_hash,
            machine_std_rewrite_profile_set_hash(&rewrite_profiles).unwrap()
        );

        let nat_rw = rewrite_profile(&rewrite_profiles, STD_NAT_RW_PROFILE_ID);
        let list_rw = rewrite_profile(&rewrite_profiles, STD_LIST_RW_PROFILE_ID);
        let all_rw = rewrite_profile(&rewrite_profiles, STD_ALL_RW_PROFILE_ID);
        let union = nat_rw
            .descriptors
            .iter()
            .chain(&list_rw.descriptors)
            .map(|descriptor| machine_std_rewrite_descriptor_canonical_bytes(descriptor).unwrap())
            .collect::<BTreeSet<_>>();
        let all = all_rw
            .descriptors
            .iter()
            .map(|descriptor| machine_std_rewrite_descriptor_canonical_bytes(descriptor).unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(all, union);

        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        validate_machine_std_mvp_simp_profile_set(
            &simp_profiles,
            &simp_profiles,
            &rewrite_profiles,
        )
        .unwrap();
        assert_eq!(
            simp_profiles
                .profiles
                .iter()
                .map(|profile| (
                    profile.profile_id.as_str(),
                    profile.required_import_bundle_id.as_str(),
                    profile.rules.len(),
                ))
                .collect::<Vec<_>>(),
            vec![
                (STD_ALL_SIMP_PROFILE_ID, STD_ALL_BUNDLE_ID, 18),
                (STD_LIST_SIMP_PROFILE_ID, STD_LIST_BUNDLE_ID, 10),
                (STD_LOGIC_SIMP_PROFILE_ID, STD_LOGIC_BUNDLE_ID, 0),
                (STD_NAT_SIMP_PROFILE_ID, STD_NAT_BUNDLE_ID, 8),
            ]
        );
        assert!(simp_profiles
            .profiles
            .iter()
            .flat_map(|profile| &profile.rules)
            .all(|rule| rule.direction == RewriteDirection::Forward));
        assert!(
            simp_profiles
                .profiles
                .iter()
                .all(|profile| profile.profile_hash
                    == machine_std_simp_profile_hash(profile).unwrap())
        );
        assert_eq!(
            simp_profiles.simp_profiles_hash,
            machine_std_simp_profile_set_hash(&simp_profiles).unwrap()
        );

        let nat_simp = simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID);
        let list_simp = simp_profile(&simp_profiles, STD_LIST_SIMP_PROFILE_ID);
        let all_simp = simp_profile(&simp_profiles, STD_ALL_SIMP_PROFILE_ID);
        let union = nat_simp
            .rules
            .iter()
            .chain(&list_simp.rules)
            .map(|rule| simp_rule_ref_canonical_bytes(rule).unwrap())
            .collect::<BTreeSet<_>>();
        let all = all_simp
            .rules
            .iter()
            .map(|rule| simp_rule_ref_canonical_bytes(rule).unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(all, union);
    }

    #[test]
    fn human_source_simp_rw_intent_matches_ai_profile_fixed_sets() {
        let package = TestPackage::new("human_source_profile_intent_matches_ai_fixed_sets");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();

        let expected_nat_simp = human_source_simp_intent(STD_NAT_SIMP_PROFILE_ID);
        let expected_list_simp = human_source_simp_intent(STD_LIST_SIMP_PROFILE_ID);
        let expected_all_simp = human_source_simp_intent(STD_ALL_SIMP_PROFILE_ID);
        let expected_nat_rw_only = human_source_rw_only_intent(STD_NAT_RW_PROFILE_ID);
        let expected_list_rw_only = human_source_rw_only_intent(STD_LIST_RW_PROFILE_ID);
        let expected_all_rw_only = human_source_rw_only_intent(STD_ALL_RW_PROFILE_ID);

        assert!(simp_profile(&simp_profiles, STD_LOGIC_SIMP_PROFILE_ID)
            .rules
            .is_empty());
        assert!(rewrite_profile(&rewrite_profiles, STD_LOGIC_RW_PROFILE_ID)
            .descriptors
            .is_empty());
        assert!(simp_profiles
            .profiles
            .iter()
            .flat_map(|profile| &profile.rules)
            .all(|rule| rule.name != Name::from_dotted("Eq.refl")));

        let nat_rw = rewrite_profile(&rewrite_profiles, STD_NAT_RW_PROFILE_ID);
        assert_eq!(
            rewrite_profile_rule_names_by_safety(nat_rw, MachineStdRewriteSafety::SimpSafe),
            expected_nat_simp
        );
        assert_eq!(
            rewrite_profile_rule_names_by_safety(nat_rw, MachineStdRewriteSafety::RwOnly),
            expected_nat_rw_only
        );
        assert_eq!(
            simp_profile_rule_names(simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID)),
            human_source_simp_intent(STD_NAT_SIMP_PROFILE_ID)
        );

        let list_rw = rewrite_profile(&rewrite_profiles, STD_LIST_RW_PROFILE_ID);
        let list_simp = simp_profile(&simp_profiles, STD_LIST_SIMP_PROFILE_ID);
        assert_eq!(
            rewrite_profile_rule_names_by_safety(list_rw, MachineStdRewriteSafety::SimpSafe),
            expected_list_simp
        );
        assert_eq!(
            rewrite_profile_rule_names_by_safety(list_rw, MachineStdRewriteSafety::RwOnly),
            expected_list_rw_only
        );
        assert_eq!(simp_profile_rule_names(list_simp), expected_list_simp);
        assert_eq!(
            simp_profile_rule_source_modules(list_simp, list_rw),
            string_set(&["Std.List"]),
            "std.list.simp must not include Std.Nat rule sources"
        );

        let all_rw = rewrite_profile(&rewrite_profiles, STD_ALL_RW_PROFILE_ID);
        let all_simp = simp_profile(&simp_profiles, STD_ALL_SIMP_PROFILE_ID);
        assert_eq!(
            rewrite_profile_rule_names_by_safety(all_rw, MachineStdRewriteSafety::SimpSafe),
            expected_all_simp
        );
        assert_eq!(
            rewrite_profile_rule_names_by_safety(all_rw, MachineStdRewriteSafety::RwOnly),
            expected_all_rw_only
        );
        assert_eq!(simp_profile_rule_names(all_simp), expected_all_simp);

        let profile_set_rewrite_names = rewrite_profiles
            .profiles
            .iter()
            .flat_map(|profile| &profile.descriptors)
            .map(|descriptor| descriptor.source.name.as_dotted())
            .collect::<BTreeSet<_>>();
        let profile_set_simp_names = simp_profiles
            .profiles
            .iter()
            .flat_map(|profile| &profile.rules)
            .map(|rule| rule.name.as_dotted())
            .collect::<BTreeSet<_>>();
        for excluded in ["Nat.mul_comm", "Nat.mul_assoc", "List.map_comp"] {
            assert!(
                !profile_set_rewrite_names.contains(excluded),
                "{excluded} must not be emitted in MVP rewrite profiles"
            );
            assert!(
                !profile_set_simp_names.contains(excluded),
                "{excluded} must not be emitted in MVP simp profiles"
            );
        }
    }

    #[test]
    fn std_all_simp_and_rw_profiles_are_reverified_semantic_unions() {
        let package = TestPackage::new("std_all_profiles_semantic_union");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        validate_machine_std_mvp_rewrite_profile_set(&rewrite_profiles, &rewrite_profiles).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        validate_machine_std_mvp_simp_profile_set(
            &simp_profiles,
            &simp_profiles,
            &rewrite_profiles,
        )
        .unwrap();

        let nat_rw = rewrite_profile(&rewrite_profiles, STD_NAT_RW_PROFILE_ID);
        let list_rw = rewrite_profile(&rewrite_profiles, STD_LIST_RW_PROFILE_ID);
        let all_rw = rewrite_profile(&rewrite_profiles, STD_ALL_RW_PROFILE_ID);
        let expected_rw_union = canonical_rewrite_descriptor_union(&[nat_rw, list_rw]);
        let actual_all_rw = canonical_rewrite_descriptor_sequence(all_rw);
        assert_eq!(
            actual_all_rw, expected_rw_union,
            "std.all.rw must be the canonical semantic union of Nat and List rw profiles"
        );

        let nat_simp = simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID);
        let list_simp = simp_profile(&simp_profiles, STD_LIST_SIMP_PROFILE_ID);
        let all_simp = simp_profile(&simp_profiles, STD_ALL_SIMP_PROFILE_ID);
        let expected_simp_union = canonical_simp_rule_union(&[nat_simp, list_simp]);
        let actual_all_simp = canonical_simp_rule_sequence(all_simp);
        assert_eq!(
            actual_all_simp, expected_simp_union,
            "std.all.simp must be the canonical semantic union of Nat and List simp profiles"
        );

        let mut source_targets = simp_rule_target_map(nat_simp, nat_rw);
        source_targets.extend(simp_rule_target_map(list_simp, list_rw));
        assert_eq!(
            simp_rule_target_map(all_simp, all_rw),
            source_targets,
            "std.all.simp rules must resolve to the same certificate-bound theorem targets"
        );
    }

    #[test]
    fn registers_std_nat_pred_rules_as_simp_safe_candidates() {
        let package = TestPackage::new("std_nat_pred_simp_safe_candidates");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let eq_family = std_logic_eq_family(&loaded).unwrap();
        let pred_candidates = ["Nat.pred_zero", "Nat.pred_succ"]
            .into_iter()
            .map(|name| {
                mvp_rewrite_rule_candidate(
                    &loaded,
                    STD_NAT_RW_PROFILE_ID,
                    STD_NAT_BUNDLE_ID,
                    name,
                    MachineStdRewriteSafety::SimpSafe,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        assert!(pred_candidates
            .iter()
            .all(|candidate| candidate.safety == MachineStdRewriteSafety::SimpSafe));
        let pred_rules = pred_candidates
            .iter()
            .map(|candidate| candidate.rule_ref.clone())
            .collect::<Vec<_>>();
        let resolved = resolve_rewrite_profile_rules(
            &loaded,
            STD_NAT_RW_PROFILE_ID,
            STD_NAT_BUNDLE_ID,
            &eq_family,
            &pred_rules,
        )
        .unwrap();
        assert_eq!(
            resolved
                .iter()
                .map(|rule| rule.key.name.as_dotted())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["Nat.pred_succ".to_owned(), "Nat.pred_zero".to_owned()])
        );
    }

    #[test]
    fn std_nat_add_reduces_on_second_argument() {
        let mut env = Env::with_builtins().unwrap();
        env.add_def(
            "Nat.add",
            Vec::new(),
            nat_add_type(),
            nat_add_value(),
            Reducibility::Reducible,
        )
        .unwrap();

        let mut ctx = Ctx::new();
        ctx.push_assumption("n", nat());
        ctx.push_assumption("m", nat());
        assert!(env
            .is_defeq(
                &ctx,
                &[],
                &nat_add(Expr::bvar(1), nat_zero()),
                &Expr::bvar(1),
            )
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &[],
                &nat_add(Expr::bvar(1), nat_succ(Expr::bvar(0))),
                &nat_succ(nat_add(Expr::bvar(1), Expr::bvar(0))),
            )
            .unwrap());
    }

    #[test]
    fn std_nat_mul_reduces_on_second_argument() {
        let mut env = Env::with_builtins().unwrap();
        env.add_def(
            "Nat.add",
            Vec::new(),
            nat_add_type(),
            nat_add_value(),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_def(
            "Nat.mul",
            Vec::new(),
            nat_mul_type(),
            nat_mul_value(),
            Reducibility::Reducible,
        )
        .unwrap();

        let mut ctx = Ctx::new();
        ctx.push_assumption("n", nat());
        ctx.push_assumption("m", nat());
        assert!(env
            .is_defeq(&ctx, &[], &nat_mul(Expr::bvar(1), nat_zero()), &nat_zero(),)
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &[],
                &nat_mul(Expr::bvar(1), nat_succ(Expr::bvar(0))),
                &nat_add(nat_mul(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
            )
            .unwrap());
    }

    #[test]
    fn std_list_append_reduces_on_first_argument() {
        let u = Level::param("u");
        let v = Level::param("v");
        let mut env = Env::new();
        env.add_inductive(list_inductive_with_rec()).unwrap();
        env.add_inductive(nat_inductive()).unwrap();
        env.add_def(
            "Nat.add",
            Vec::new(),
            nat_add_type(),
            nat_add_value(),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_def(
            "List.append",
            vec!["u".to_owned()],
            list_append_type(u.clone()),
            list_append_value(u.clone()),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_def(
            "List.length",
            vec!["u".to_owned()],
            list_length_type(u.clone()),
            list_length_value(u.clone()),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_def(
            "List.map",
            vec!["u".to_owned(), "v".to_owned()],
            list_map_type(u.clone(), v.clone()),
            list_map_value(u.clone(), v.clone()),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_def(
            "List.foldr",
            vec!["u".to_owned(), "v".to_owned()],
            list_foldr_type(u.clone(), v.clone()),
            list_foldr_value(u.clone(), v.clone()),
            Reducibility::Reducible,
        )
        .unwrap();

        let mut ctx = Ctx::new();
        ctx.push_assumption("A", Expr::sort(u.clone()));
        ctx.push_assumption("B", Expr::sort(v.clone()));
        ctx.push_assumption("x", Expr::bvar(1));
        ctx.push_assumption("f", Expr::pi("_", Expr::bvar(2), Expr::bvar(2)));
        ctx.push_assumption(
            "step",
            Expr::pi(
                "_",
                Expr::bvar(3),
                Expr::pi("_", Expr::bvar(3), Expr::bvar(4)),
            ),
        );
        ctx.push_assumption("init", Expr::bvar(3));
        ctx.push_assumption("xs", list(u.clone(), Expr::bvar(5)));
        ctx.push_assumption("ys", list(u.clone(), Expr::bvar(6)));

        let a = Expr::bvar(7);
        let x = Expr::bvar(5);
        let xs = Expr::bvar(1);
        let ys = Expr::bvar(0);
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned()],
                &list_append(
                    u.clone(),
                    a.clone(),
                    list_nil(u.clone(), a.clone()),
                    ys.clone()
                ),
                &ys,
            )
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned()],
                &list_append(
                    u.clone(),
                    a.clone(),
                    list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
                    ys.clone(),
                ),
                &list_cons(
                    u.clone(),
                    a.clone(),
                    x,
                    list_append(u.clone(), a.clone(), xs, ys),
                ),
            )
            .unwrap());
        let a = Expr::bvar(7);
        let b = Expr::bvar(6);
        let x = Expr::bvar(5);
        let f = Expr::bvar(4);
        let step = Expr::bvar(3);
        let init = Expr::bvar(2);
        let xs = Expr::bvar(1);
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned(), "v".to_owned()],
                &list_length(
                    u.clone(),
                    a.clone(),
                    list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
                ),
                &nat_succ(list_length(u.clone(), a.clone(), xs.clone())),
            )
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned(), "v".to_owned()],
                &list_map(
                    u.clone(),
                    v.clone(),
                    a.clone(),
                    b.clone(),
                    f.clone(),
                    list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
                ),
                &list_cons(
                    v.clone(),
                    b.clone(),
                    Expr::app(f.clone(), x.clone()),
                    list_map(u.clone(), v.clone(), a.clone(), b.clone(), f, xs.clone()),
                ),
            )
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned(), "v".to_owned()],
                &list_foldr(
                    u.clone(),
                    v.clone(),
                    a.clone(),
                    b.clone(),
                    step.clone(),
                    init.clone(),
                    list_nil(u.clone(), a.clone()),
                ),
                &init,
            )
            .unwrap());
        assert!(env
            .is_defeq(
                &ctx,
                &["u".to_owned(), "v".to_owned()],
                &list_foldr(
                    u.clone(),
                    v.clone(),
                    a.clone(),
                    b.clone(),
                    step.clone(),
                    init.clone(),
                    list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
                ),
                &Expr::apps(
                    step,
                    vec![x, list_foldr(u, v, a, b, Expr::bvar(3), init, xs),],
                ),
            )
            .unwrap());
    }

    #[test]
    fn classifies_std_nat_add_rules_as_simp_safe_or_rw_only() {
        let package = TestPackage::new("std_nat_add_profile_classification");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();

        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let nat_rw = rewrite_profile(&rewrite_profiles, STD_NAT_RW_PROFILE_ID);
        let nat_simp = simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID);
        let safety_by_name = nat_rw
            .descriptors
            .iter()
            .map(|descriptor| (descriptor.source.name.as_dotted(), descriptor.safety))
            .collect::<BTreeMap<_, _>>();
        for name in ["Nat.add_zero", "Nat.add_succ", "Nat.zero_add"] {
            assert_eq!(
                safety_by_name.get(name),
                Some(&MachineStdRewriteSafety::SimpSafe),
                "{name} should be a simp-safe Nat rewrite"
            );
        }
        for name in [
            "Nat.mul_zero",
            "Nat.mul_succ",
            "Nat.zero_mul",
            "Nat.pred_zero",
            "Nat.pred_succ",
        ] {
            assert_eq!(
                safety_by_name.get(name),
                Some(&MachineStdRewriteSafety::SimpSafe),
                "{name} should stay a simp-safe Nat rewrite"
            );
        }
        for name in ["Nat.add_comm", "Nat.add_assoc"] {
            assert_eq!(
                safety_by_name.get(name),
                Some(&MachineStdRewriteSafety::RwOnly),
                "{name} should be rw-only and excluded from simp"
            );
        }

        let nat_simp_names = nat_simp
            .rules
            .iter()
            .map(|rule| rule.name.as_dotted())
            .collect::<BTreeSet<_>>();
        for name in ["Nat.add_zero", "Nat.add_succ", "Nat.zero_add"] {
            assert!(
                nat_simp_names.contains(name),
                "{name} should be present in the Nat simp profile"
            );
        }
        for name in [
            "Nat.mul_zero",
            "Nat.mul_succ",
            "Nat.zero_mul",
            "Nat.pred_zero",
            "Nat.pred_succ",
        ] {
            assert!(
                nat_simp_names.contains(name),
                "{name} should be present in the Nat simp profile"
            );
        }
        for name in ["Nat.add_comm", "Nat.add_assoc"] {
            assert!(
                !nat_simp_names.contains(name),
                "{name} must not enter the Nat simp profile"
            );
        }
    }

    #[test]
    fn classifies_std_list_rules_and_keeps_late_map_theorems_out_of_mvp_profiles() {
        let package = TestPackage::new("std_list_profile_classification");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();

        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let theorem_index = generate_machine_std_mvp_final_theorem_index(
            &loaded,
            &rewrite_profiles,
            &simp_profiles,
        )
        .unwrap();
        let list_rw = rewrite_profile(&rewrite_profiles, STD_LIST_RW_PROFILE_ID);
        let list_simp = simp_profile(&simp_profiles, STD_LIST_SIMP_PROFILE_ID);
        let safety_by_name = list_rw
            .descriptors
            .iter()
            .map(|descriptor| (descriptor.source.name.as_dotted(), descriptor.safety))
            .collect::<BTreeMap<_, _>>();

        let expected_simp_safe = BTreeSet::from([
            "List.nil_append".to_owned(),
            "List.cons_append".to_owned(),
            "List.append_nil".to_owned(),
            "List.length_nil".to_owned(),
            "List.length_cons".to_owned(),
            "List.map_nil".to_owned(),
            "List.map_cons".to_owned(),
            "List.map_id".to_owned(),
            "List.foldr_nil".to_owned(),
            "List.foldr_cons".to_owned(),
        ]);
        for name in &expected_simp_safe {
            assert_eq!(
                safety_by_name.get(name.as_str()),
                Some(&MachineStdRewriteSafety::SimpSafe),
                "{name} should be a simp-safe List rewrite"
            );
        }
        for name in ["List.append_assoc", "List.length_append"] {
            assert_eq!(
                safety_by_name.get(name),
                Some(&MachineStdRewriteSafety::RwOnly),
                "{name} should be rw-only and excluded from simp"
            );
        }

        let list_simp_names = list_simp
            .rules
            .iter()
            .map(|rule| rule.name.as_dotted())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            list_simp_names, expected_simp_safe,
            "List simp-safe exact set should match the human/AI profile"
        );
        assert!(
            !list_simp_names.contains("List.append_assoc"),
            "List.append_assoc must not enter the List simp profile"
        );
        assert!(
            !list_simp_names.contains("List.length_append"),
            "List.length_append must not enter the List simp profile"
        );
        assert!(
            list_rw
                .descriptors
                .iter()
                .all(|descriptor| descriptor.source.module != Name::from_dotted("Std.Nat")),
            "std.list.rw must not include Std.Nat rewrite rule sources"
        );
        assert!(
            list_simp
                .rules
                .iter()
                .all(|rule| rule.name.as_dotted().starts_with("List.")),
            "std.list.simp must not include non-List rewrite rule names"
        );

        for name in ["List.append_assoc", "List.length_append"] {
            let entry = theorem_index_entry(&theorem_index, name);
            assert!(
                entry.modes.contains(&MachineTheoremMode::Exact)
                    && entry.modes.contains(&MachineTheoremMode::Apply)
                    && entry.modes.contains(&MachineTheoremMode::Rw),
                "{name} should remain searchable and rw-capable"
            );
            assert!(
                !entry.modes.contains(&MachineTheoremMode::Simp),
                "{name} must not be finalized as simp metadata"
            );
        }

        let map_comp = theorem_index_entry(&theorem_index, "List.map_comp");
        assert!(
            map_comp.modes.contains(&MachineTheoremMode::Exact)
                && map_comp.modes.contains(&MachineTheoremMode::Apply),
            "List.map_comp should remain searchable through the theorem index"
        );
        assert!(
            !map_comp.modes.contains(&MachineTheoremMode::Rw)
                && !map_comp.modes.contains(&MachineTheoremMode::Simp),
            "List.map_comp must not enter AI MVP rewrite or simp profiles"
        );
    }

    #[test]
    fn keeps_late_std_nat_mul_theorems_searchable_but_out_of_mvp_profiles() {
        let package = TestPackage::new("std_nat_late_mul_theorem_profile_exclusion");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();

        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let theorem_index = generate_machine_std_mvp_final_theorem_index(
            &loaded,
            &rewrite_profiles,
            &simp_profiles,
        )
        .unwrap();
        let nat_rw_names = rewrite_profile(&rewrite_profiles, STD_NAT_RW_PROFILE_ID)
            .descriptors
            .iter()
            .map(|descriptor| descriptor.source.name.as_dotted())
            .collect::<BTreeSet<_>>();
        let nat_simp_names = simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID)
            .rules
            .iter()
            .map(|rule| rule.name.as_dotted())
            .collect::<BTreeSet<_>>();

        for name in [
            "Nat.succ_mul",
            "Nat.mul_assoc",
            "Nat.mul_comm",
            "Nat.left_distrib",
            "Nat.right_distrib",
        ] {
            let entry = theorem_index_entry(&theorem_index, name);
            assert!(
                entry.modes.contains(&MachineTheoremMode::Exact)
                    && entry.modes.contains(&MachineTheoremMode::Apply),
                "{name} should remain searchable through the theorem index"
            );
            assert!(
                !entry.modes.contains(&MachineTheoremMode::Rw)
                    && !entry.modes.contains(&MachineTheoremMode::Simp),
                "{name} must not be finalized as rw/simp metadata"
            );
            assert!(
                !nat_rw_names.contains(name),
                "{name} must not be emitted in the Nat MVP rewrite profile"
            );
            assert!(
                !nat_simp_names.contains(name),
                "{name} must not be emitted in the Nat MVP simp profile"
            );
        }
    }

    #[test]
    fn finalizes_mvp_import_bundle_recipes_for_machine_api_handoff() {
        let package = TestPackage::new("mvp_import_bundle_recipe_finalizer");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();

        let bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();
        validate_machine_std_mvp_import_bundle_recipes(&loaded, &bundle_set, &simp_profiles)
            .unwrap();

        let nat_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        let nat_profile = simp_profile(&simp_profiles, STD_NAT_SIMP_PROFILE_ID);
        let recipe = &nat_bundle.recommended_tactic_options;
        let request = machine_std_tactic_options_recipe_request(recipe);
        assert_eq!(recipe.recipe_id, STD_NAT_RECIPE_ID);
        assert_eq!(
            recipe.kernel_check_profile,
            STD_KERNEL_CHECK_PROFILE_BUILTIN_NONE
        );
        assert_eq!(recipe.simp_rules, nat_profile.rules);
        assert_eq!(request.simp_rules, nat_profile.rules);
        assert_nat_family_matches_std_nat_exports(
            &loaded,
            recipe
                .nat_family
                .as_ref()
                .expect("std.nat.mvp final recipe should expose Nat family"),
        );
        assert_eq!(request.nat_family, recipe.nat_family);
        assert_eq!(recipe.max_simp_rewrite_steps, STD_MAX_SIMP_REWRITE_STEPS);
        assert_eq!(recipe.max_open_goals, STD_MAX_OPEN_GOALS);
        assert_eq!(recipe.max_metas, STD_MAX_METAS);

        let logic = loaded.module(&Name::from_dotted("Std.Logic")).unwrap();
        let family = recipe.eq_family.as_ref().unwrap();
        assert_eq!(
            family.eq_interface_hash,
            export_entry(logic, "Eq").decl_interface_hash
        );
        assert_eq!(
            family.refl_interface_hash,
            export_entry(logic, "Eq.refl").decl_interface_hash
        );
        assert_eq!(
            family.rec_interface_hash,
            export_entry(logic, "Eq.rec").decl_interface_hash
        );
    }

    #[test]
    fn machine_session_rejects_stale_recipe_payload_before_root_elaboration() {
        let package = TestPackage::new("mvp_import_bundle_recipe_session_handoff");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();
        let mut nat_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap()
            .clone();
        nat_bundle.recommended_tactic_options.simp_rules[0].decl_interface_hash = test_hash(231);

        let err = crate::create_machine_session(&session_create_json_for_bundle(&nat_bundle))
            .unwrap_err();
        assert_eq!(
            err.error.kind,
            crate::MachineApiErrorKind::InvalidMachineApiOptions
        );
    }

    #[test]
    fn machine_session_accepts_final_recipe_payload() {
        let package = TestPackage::new("mvp_import_bundle_recipe_session_accepts_final");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();
        let nat_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();

        let ok =
            crate::create_machine_session(&session_create_json_for_bundle(nat_bundle)).unwrap();

        assert_eq!(
            ok.session.options.kernel_check_profile,
            crate::KernelCheckProfileId::BuiltinNone
        );
        assert_eq!(
            ok.session.options.tactic_options,
            machine_std_tactic_options_recipe_request(&nat_bundle.recommended_tactic_options)
        );
    }

    #[test]
    fn rejects_stale_import_bundle_recipe_refs_with_machine_api_validation() {
        let package = TestPackage::new("stale_import_bundle_recipe_machine_api");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let mut simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let mut bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();

        let stale_rule = {
            let profile = simp_profiles
                .profiles
                .iter_mut()
                .find(|profile| profile.profile_id == STD_NAT_SIMP_PROFILE_ID)
                .unwrap();
            let mut rule = profile.rules[0].clone();
            rule.decl_interface_hash = test_hash(222);
            profile.rules[0] = rule.clone();
            rule
        };
        let nat_bundle = bundle_set
            .bundles
            .iter_mut()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        nat_bundle.recommended_tactic_options.simp_rules[0] = stale_rule;
        bundle_set.import_bundles_hash = machine_std_import_bundle_set_hash(&bundle_set).unwrap();

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_recipes(
                &loaded,
                &bundle_set,
                &simp_profiles,
            ),
            Err(MachineStdImportBundleError::RecipeMachineApiValidationFailed {
                bundle_id,
                ..
            }) if bundle_id == STD_NAT_BUNDLE_ID
        ));
    }

    #[test]
    fn stale_recipe_validation_runs_before_expected_final_hash_comparison() {
        let package = TestPackage::new("stale_import_bundle_recipe_before_hash");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let expected =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();
        let mut actual = expected.clone();

        let nat_bundle = actual
            .bundles
            .iter_mut()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        nat_bundle.recommended_tactic_options.simp_rules[0].decl_interface_hash = test_hash(232);
        actual.import_bundles_hash = machine_std_import_bundle_set_hash(&actual).unwrap();

        validate_machine_std_mvp_import_bundle_set_shape(&actual, &expected).unwrap();
        let recipe_error =
            validate_machine_std_mvp_import_bundle_recipes(&loaded, &actual, &simp_profiles)
                .unwrap_err();
        assert!(
            matches!(
                recipe_error,
                MachineStdImportBundleError::RecipeMachineApiValidationFailed {
                    ref bundle_id,
                    ..
                } if bundle_id == STD_NAT_BUNDLE_ID
            ),
            "{recipe_error:?}"
        );
        assert!(matches!(
            validate_import_bundle_set_expected_hash(&actual, &expected),
            Err(MachineStdImportBundleError::ImportBundlesHashMismatch { .. })
        ));
    }

    #[test]
    fn rejects_missing_mvp_import_bundle_recipe_nat_family() {
        let package = TestPackage::new("missing_import_bundle_recipe_nat_family");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let mut bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();

        let nat_bundle = bundle_set
            .bundles
            .iter_mut()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        nat_bundle.recommended_tactic_options.nat_family = None;
        bundle_set.import_bundles_hash = machine_std_import_bundle_set_hash(&bundle_set).unwrap();

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_recipes(
                &loaded,
                &bundle_set,
                &simp_profiles,
            ),
            Err(MachineStdImportBundleError::RecipeFieldMismatch {
                bundle_id,
                field: "nat_family",
            }) if bundle_id == STD_NAT_BUNDLE_ID
        ));
    }

    #[test]
    fn rejects_stale_rewrite_and_simp_profile_hashes_before_set_hash() {
        let package = TestPackage::new("stale_rewrite_simp_profile_hashes");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();

        let mut stale_rewrite = rewrite_profiles.clone();
        stale_rewrite.profiles[0].profile_hash = test_hash(77);
        stale_rewrite.rewrite_profiles_hash =
            machine_std_rewrite_profile_set_hash(&stale_rewrite).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_rewrite_profile_set(&stale_rewrite, &rewrite_profiles),
            Err(MachineStdRewriteProfileError::ProfileHashMismatch { profile_id, .. })
                if profile_id == STD_ALL_RW_PROFILE_ID
        ));

        let mut stale_simp = simp_profiles.clone();
        stale_simp.profiles[0].profile_hash = test_hash(78);
        stale_simp.simp_profiles_hash = machine_std_simp_profile_set_hash(&stale_simp).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_simp_profile_set(
                &stale_simp,
                &simp_profiles,
                &rewrite_profiles,
            ),
            Err(MachineStdSimpProfileError::ProfileHashMismatch { profile_id, .. })
                if profile_id == STD_ALL_SIMP_PROFILE_ID
        ));
    }

    #[test]
    fn simp_safe_exception_sources_are_hash_bound() {
        let package = TestPackage::new("simp_safe_exception_hash_bound");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let source_for = |module_name: &str, theorem_name: &str| {
            let module = loaded.module(&Name::from_dotted(module_name)).unwrap();
            let export = export_entry(module, theorem_name);
            MachineStdGlobalRef {
                module: module.module.clone(),
                name: Name::from_dotted(theorem_name),
                export_hash: module.expected_export_hash,
                certificate_hash: module.expected_certificate_hash,
                decl_interface_hash: export.decl_interface_hash,
            }
        };

        let source = source_for("Std.Nat", "Nat.mul_succ");
        assert!(simp_size_exception(&loaded, &source));
        assert_eq!(allowed_intro_heads(&loaded, &source).unwrap().len(), 1);

        let mut spoofed = source;
        spoofed.decl_interface_hash = test_hash(202);
        assert!(!simp_size_exception(&loaded, &spoofed));
        assert!(allowed_intro_heads(&loaded, &spoofed).unwrap().is_empty());

        for theorem_name in ["List.map_cons", "List.foldr_cons"] {
            let source = source_for("Std.List", theorem_name);
            assert!(
                simp_size_exception(&loaded, &source),
                "{theorem_name} should be a hash-bound simp size exception"
            );

            let mut spoofed = source;
            spoofed.decl_interface_hash = test_hash(203);
            assert!(
                !simp_size_exception(&loaded, &spoofed),
                "{theorem_name} size exception should reject spoofed source hashes"
            );
        }
    }

    #[test]
    fn finalizes_mvp_theorem_index_metadata_from_validated_profiles() {
        let package = TestPackage::new("mvp_theorem_index_metadata_finalizer");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let base = generate_machine_std_mvp_theorem_index(&loaded).unwrap();

        let finalized =
            finalize_machine_std_mvp_theorem_index(&base, &rewrite_profiles, &simp_profiles)
                .unwrap();
        assert_eq!(
            finalized,
            generate_machine_std_mvp_final_theorem_index(
                &loaded,
                &rewrite_profiles,
                &simp_profiles
            )
            .unwrap()
        );
        validate_machine_std_mvp_final_theorem_index(&finalized, &finalized).unwrap();
        assert_ne!(finalized.index_hash, [0; 32]);
        assert_eq!(
            finalized.index_hash,
            machine_std_theorem_index_hash(&finalized).unwrap()
        );

        let nat_add_zero = theorem_index_entry(&finalized, "Nat.add_zero");
        assert_eq!(
            nat_add_zero.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
                MachineTheoremMode::Simp,
            ]
        );
        assert_eq!(
            nat_add_zero.attributes,
            vec![
                MachineStdAttribute::Simp,
                MachineStdAttribute::Rw,
                MachineStdAttribute::Apply,
            ]
        );
        assert_eq!(nat_add_zero.rewrite_descriptors.len(), 1);
        assert_eq!(
            nat_add_zero.rewrite_descriptors[0].safety,
            MachineStdRewriteSafety::SimpSafe
        );

        let nat_add_comm = theorem_index_entry(&finalized, "Nat.add_comm");
        assert_eq!(
            nat_add_comm.modes,
            vec![
                MachineTheoremMode::Exact,
                MachineTheoremMode::Apply,
                MachineTheoremMode::Rw,
            ]
        );
        assert_eq!(
            nat_add_comm.attributes,
            vec![MachineStdAttribute::Rw, MachineStdAttribute::Apply]
        );
        assert_eq!(nat_add_comm.rewrite_descriptors.len(), 1);
        assert_eq!(
            nat_add_comm.rewrite_descriptors[0].safety,
            MachineStdRewriteSafety::RwOnly
        );

        let eq_rec = theorem_index_entry(&finalized, "Eq.rec");
        assert_eq!(
            eq_rec.modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply]
        );
        assert_eq!(eq_rec.attributes, vec![MachineStdAttribute::Apply]);
        assert!(eq_rec.rewrite_descriptors.is_empty());

        let human_only_attributes = [
            MachineStdAttribute::Intro,
            MachineStdAttribute::Elim,
            MachineStdAttribute::Refl,
            MachineStdAttribute::Trans,
            MachineStdAttribute::Congr,
        ];
        for entry in &finalized.entries {
            assert!(
                entry
                    .attributes
                    .iter()
                    .all(|attribute| !human_only_attributes.contains(attribute)),
                "{} must not expose human-facing source metadata in the AI theorem index",
                entry.global_ref.name.as_dotted()
            );
        }
        for theorem in ["Eq.trans", "And.intro", "False.elim"] {
            let entry = theorem_index_entry(&finalized, theorem);
            assert_eq!(entry.attributes, vec![MachineStdAttribute::Apply]);
        }

        let axiom_report = mvp_axiom_report_for(&loaded);
        let mut release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);
        let err = validate_machine_std_mvp_release_final_sidecar_counts(
            &release,
            &finalized,
            &simp_profiles,
            &rewrite_profiles,
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::ModuleArtifactCountMismatch {
                    field: "simp_rule_count",
                    ..
                }
            )
        ));

        apply_final_sidecar_counts(&mut release, &finalized, &simp_profiles, &rewrite_profiles);
        validate_machine_std_mvp_release_final_sidecar_counts(
            &release,
            &finalized,
            &simp_profiles,
            &rewrite_profiles,
        )
        .unwrap();
        assert_eq!(module_artifact(&release, "Std.Nat").simp_rule_count, 8);
        assert_eq!(module_artifact(&release, "Std.List").simp_rule_count, 10);
    }

    #[test]
    fn human_theorem_index_search_view_derives_categories_from_verified_std_artifacts() {
        let package = TestPackage::new("human_theorem_index_search_view_categories");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (_, _, theorem_index, _, _, _) = final_sidecar_artifacts_for_loaded(&loaded);

        let human_view = generate_human_std_theorem_search_view(&loaded, &theorem_index).unwrap();
        assert_eq!(human_view.library_profile_id, STD_LIBRARY_PROFILE_ID);
        assert_eq!(
            human_view.debug_hash,
            human_std_theorem_search_view_hash(&human_view).unwrap()
        );

        let nat_add_zero = human_theorem_search_entry(&human_view, "Nat.add_zero");
        assert_eq!(
            nat_add_zero.global_ref,
            theorem_index_entry(&theorem_index, "Nat.add_zero").global_ref
        );
        for category in [
            HumanStdTheoremCategory::Exact,
            HumanStdTheoremCategory::Rw,
            HumanStdTheoremCategory::Simp,
        ] {
            assert!(nat_add_zero.categories.contains(&category));
        }
        assert!(nat_add_zero
            .display_attributes
            .contains(&HumanStdTheoremDisplayAttribute::Simp));
        assert!(nat_add_zero
            .suggested_tactics
            .contains(&"rw [Nat.add_zero]".to_owned()));
        assert!(nat_add_zero
            .suggested_tactics
            .contains(&"simp-lite".to_owned()));
        assert!(nat_add_zero.proof_term_size.is_some_and(|size| size > 0));
        assert_eq!(
            theorem_index_entry(&theorem_index, "Nat.add_zero").proof_term_size,
            None,
            "AI theorem index keeps proof_term_size null"
        );

        let list_append_nil = human_theorem_search_entry(&human_view, "List.append_nil");
        for category in [
            HumanStdTheoremCategory::Exact,
            HumanStdTheoremCategory::Rw,
            HumanStdTheoremCategory::Simp,
        ] {
            assert!(list_append_nil.categories.contains(&category));
        }
        assert!(list_append_nil
            .suggested_tactics
            .contains(&"rw [List.append_nil]".to_owned()));
        assert!(list_append_nil
            .suggested_tactics
            .contains(&"simp-lite".to_owned()));

        let eq_trans = human_theorem_search_entry(&human_view, "Eq.trans");
        assert!(eq_trans
            .categories
            .contains(&HumanStdTheoremCategory::Apply));
        assert!(!eq_trans.categories.contains(&HumanStdTheoremCategory::Rw));
        assert!(!eq_trans.categories.contains(&HumanStdTheoremCategory::Simp));
        assert_eq!(eq_trans.suggested_tactics, vec!["apply Eq.trans"]);

        let false_elim = human_theorem_search_entry(&human_view, "False.elim");
        assert!(false_elim
            .categories
            .contains(&HumanStdTheoremCategory::Elim));
        assert!(false_elim
            .display_attributes
            .contains(&HumanStdTheoremDisplayAttribute::Elim));
        assert!(false_elim
            .suggested_tactics
            .contains(&"apply False.elim".to_owned()));
    }

    struct Phase6HumanRealStdlibFixture {
        verified_modules: Vec<VerifiedModule>,
        options: crate::HumanApiCompileOptions,
    }

    fn phase6_human_real_stdlib_fixture(label: &str) -> Phase6HumanRealStdlibFixture {
        let package = TestPackage::new(label);
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let bundle_set =
            generate_machine_std_mvp_final_import_bundle_set(&loaded, &simp_profiles).unwrap();
        let all_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_ALL_BUNDLE_ID)
            .expect("std.all.mvp bundle should be generated");

        Phase6HumanRealStdlibFixture {
            verified_modules: loaded
                .modules()
                .iter()
                .map(|module| module.verified_module.clone())
                .collect(),
            options: human_options_from_std_recipe(&all_bundle.recommended_tactic_options),
        }
    }

    fn human_options_from_std_recipe(
        recipe: &MachineStdTacticOptionsRecipe,
    ) -> crate::HumanApiCompileOptions {
        let mut options = crate::human_api_default_compile_options();
        options.kernel_profile = machine_kernel_profile_from_recipe(&recipe.kernel_check_profile);
        options.tactic_options = MachineTacticOptions {
            simp_rules: recipe.simp_rules.clone(),
            eq_family: recipe.eq_family.clone(),
            nat_family: recipe.nat_family.clone(),
            max_simp_rewrite_steps: recipe.max_simp_rewrite_steps,
            max_open_goals: usize::try_from(recipe.max_open_goals).unwrap(),
            max_metas: usize::try_from(recipe.max_metas).unwrap(),
        };
        options
    }

    fn machine_kernel_profile_from_recipe(value: &str) -> npa_tactic::MachineKernelProfile {
        match KernelCheckProfileId::parse(value).unwrap() {
            KernelCheckProfileId::BuiltinNone => npa_tactic::MachineKernelProfile::BuiltinNone,
            KernelCheckProfileId::BuiltinNatEqRec => {
                npa_tactic::MachineKernelProfile::BuiltinNatEqRec
            }
        }
    }

    fn assert_phase6_human_real_stdlib_certificate_verifies(
        fixture: &Phase6HumanRealStdlibFixture,
        module: &str,
        source: &str,
    ) -> crate::HumanCompileCertificateOk {
        let ok =
            crate::compile_human_source_to_certificate(crate::HumanCompileCertificateRequest {
                current_module: Name::from_dotted(module),
                current_source: crate::HumanCurrentModuleSource {
                    file_id: FileId(0),
                    source,
                },
                verified_modules: &fixture.verified_modules,
                imported_source_interfaces: &[],
                options: fixture.options.clone(),
            })
            .expect("Human real stdlib tactic fixture should compile to a certificate");
        assert!(ok
            .source_interface
            .declarations
            .iter()
            .all(|decl| decl.decl_interface_hash.is_some()));

        let bytes =
            encode_module_cert(&ok.certificate).expect("Human real stdlib cert should encode");
        let mut session = VerifierSession::new();
        for verified in &fixture.verified_modules {
            session.register_verified_module(verified.clone());
        }
        let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal())
            .expect("Human real stdlib certificate should verify");
        assert_eq!(verified.module(), &Name::from_dotted(module));
        ok
    }

    fn assert_phase6_human_real_stdlib_compile_error(
        fixture: &Phase6HumanRealStdlibFixture,
        module: &str,
        source: &str,
        kind: npa_frontend::HumanDiagnosticKind,
        phase: npa_frontend::HumanDiagnosticPhase,
    ) -> String {
        let err =
            crate::compile_human_source_to_certificate(crate::HumanCompileCertificateRequest {
                current_module: Name::from_dotted(module),
                current_source: crate::HumanCurrentModuleSource {
                    file_id: FileId(0),
                    source,
                },
                verified_modules: &fixture.verified_modules,
                imported_source_interfaces: &[],
                options: fixture.options.clone(),
            })
            .expect_err("negative Human real stdlib fixture must not produce a certificate");

        assert_eq!(err.diagnostic.kind, kind, "{}", err.diagnostic.message);
        assert_eq!(
            err.diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.phase),
            Some(phase),
            "{}",
            err.diagnostic.message
        );
        err.diagnostic.message
    }

    fn phase6_human_real_stdlib_session(
        fixture: &Phase6HumanRealStdlibFixture,
        module: &str,
        theorem: &str,
        source: &'static str,
    ) -> (
        crate::HumanProofSessionStore,
        crate::HumanStateRequestHeader,
        crate::HumanStateId,
        crate::HumanGoalId,
    ) {
        let mut store = crate::HumanProofSessionStore::new();
        let created = crate::create_human_session(
            &mut store,
            crate::HumanSessionCreateRequest {
                current_module: Name::from_dotted(module),
                current_source: crate::HumanCurrentModuleSource {
                    file_id: FileId(0),
                    source,
                },
                verified_modules: &fixture.verified_modules,
                imported_source_interfaces: &[],
                options: fixture.options.clone(),
            },
        )
        .expect("Human real stdlib session should be created");
        let started = crate::start_human_session_proof(
            &mut store,
            crate::HumanProofStateStartRequest {
                session_id: created.session_id.clone(),
                theorem_name: Name::from_dotted(theorem),
                source_span: None,
                selected_goal: None,
                messages: Vec::new(),
            },
        )
        .expect("Human real stdlib proof should start");
        let header = crate::HumanStateRequestHeader {
            session_id: created.session_id,
            document_id: created.document_id,
            document_version: created.document_version,
        };
        (
            store,
            header,
            started.state_id,
            started
                .selected_goal
                .expect("started Human proof should select a goal"),
        )
    }

    fn run_phase6_human_tactics(
        store: &mut crate::HumanProofSessionStore,
        header: &crate::HumanStateRequestHeader,
        mut state_id: crate::HumanStateId,
        mut goal_id: crate::HumanGoalId,
        tactics: &[&str],
    ) -> (crate::HumanStateId, crate::HumanGoalId) {
        for tactic in tactics {
            let response = crate::run_human_tactic(
                store,
                crate::HumanTacticRunRequest {
                    header: header.clone(),
                    state_id,
                    goal_id,
                    tactic: (*tactic).to_owned(),
                    budget: npa_tactic::TacticBudget::default(),
                },
            );
            assert_eq!(
                response.status,
                crate::HumanTacticRunStatus::Partial,
                "{tactic}: {:?}",
                response.error
            );
            state_id = response
                .new_state_id
                .expect("partial tactic should record a new state");
            goal_id = response
                .selected_goal
                .expect("partial tactic should select a new goal");
        }
        (state_id, goal_id)
    }

    #[test]
    fn phase6_human_real_stdlib_phase4_tactic_regressions_compile() {
        let fixture = phase6_human_real_stdlib_fixture("human_real_stdlib_tactics");
        let source = "\
import Std.Logic
import Std.Nat
import Std.List

theorem id_nat : forall (n : Nat), Nat := by
  intro n
  exact n

theorem refl_nat (n : Nat) : Eq.{1} Nat n n := by
  intro n
  exact @Eq.refl.{1} Nat n

theorem apply_false_elim (P : Prop) (h : False) : P := by
  intro P
  intro h
  apply False.elim
  exact h

theorem eq_trans_by_exact (A : Type) (x y z : A) (hxy : Eq.{1} A x y) (hyz : Eq.{1} A y z) : Eq.{1} A x z := by
  intro A
  intro x
  intro y
  intro z
  intro hxy
  intro hyz
  exact @Eq.trans.{1} A x y z hxy hyz

theorem eq_trans_infers_universe (A : Type) (x y z : A) (hxy : Eq.{1} A x y) (hyz : Eq.{1} A y z) : Eq.{1} A x z := by
  intro A
  intro x
  intro y
  intro z
  intro hxy
  intro hyz
  exact Eq.trans A x y z hxy hyz

theorem nat_add_zero_by_rw (n : Nat) : Eq.{1} Nat (Nat.add n Nat.zero) n := by
  intro n
  rw [Nat.add_zero]
  exact @Eq.refl.{1} Nat n

theorem nat_induction_self (n : Nat) : Eq.{1} Nat n n := by
  intro n
  induction n
  exact @Eq.refl.{1} Nat Nat.zero
  simp-lite

theorem nat_zero_add_by_simp (n : Nat) : Eq.{1} Nat (Nat.add Nat.zero n) n := by
  intro n
  simp-lite

theorem list_append_nil_by_rw (A : Type) (xs : List.{1} A) : Eq.{1} (List.{1} A) (List.append.{1} A xs (List.nil.{1} A)) xs := by
  intro A
  intro xs
  rw [List.append_nil]
  exact @Eq.refl.{1} (List.{1} A) xs

theorem list_append_nil_by_simp (A : Type) (xs : List.{1} A) : Eq.{1} (List.{1} A) (List.append.{1} A xs (List.nil.{1} A)) xs := by
  intro A
  intro xs
  simp-lite

theorem list_map_id_infers_universe (A : Type) (xs : List.{1} A) : Eq.{1} (List.{1} A) (List.map.{1,1} A A (fun (a : A) => a) xs) xs := by
  intro A
  intro xs
  exact List.map_id A xs";
        assert_phase6_human_real_stdlib_certificate_verifies(
            &fixture,
            "Api.HumanRealStdlibTactics",
            source,
        );

        let canonical = canonicalize_machine_term_source("@Eq.refl.{1} Nat n")
            .expect("Machine Surface fixture should remain accepted");
        assert_eq!(
            canonical.canonical_hash,
            [
                0x60, 0x8f, 0x3f, 0x0b, 0xa3, 0x6d, 0xbb, 0xaa, 0xd6, 0x8b, 0x50, 0x0a, 0xd8, 0x9e,
                0x90, 0x43, 0x18, 0x1a, 0xeb, 0x6c, 0x3d, 0xcf, 0xd9, 0x3e, 0xcc, 0xdb, 0x36, 0x8f,
                0x7d, 0x29, 0x89, 0xcf,
            ]
        );
        for human_only_source in [
            "rw [Nat.add_zero]",
            "simp-lite",
            "theorem x : Nat := by exact Nat.zero",
        ] {
            assert!(
                canonicalize_machine_term_source(human_only_source).is_err(),
                "Human proof syntax must not widen Machine Surface: {human_only_source}"
            );
        }
    }

    #[test]
    fn human_real_stdlib_negative_paths_do_not_certificate() {
        let fixture = phase6_human_real_stdlib_fixture("human_real_stdlib_negative");

        assert_phase6_human_real_stdlib_compile_error(
            &fixture,
            "Api.HumanRealStdlibOpenGoal",
            "\
import Std.Logic
import Std.Nat
import Std.List
theorem open_goal : forall (n : Nat), Nat := by
  intro n",
            npa_frontend::HumanDiagnosticKind::UnresolvedGoal,
            npa_frontend::HumanDiagnosticPhase::TacticUnresolvedGoal,
        );

        let sorry_err =
            crate::compile_human_source_to_certificate(crate::HumanCompileCertificateRequest {
                current_module: Name::from_dotted("Api.HumanRealStdlibSorry"),
                current_source: crate::HumanCurrentModuleSource {
                    file_id: FileId(0),
                    source: "\
axiom sorry_synthetic : Prop
theorem target : Prop := sorry_synthetic",
                },
                verified_modules: &[],
                imported_source_interfaces: &[],
                options: crate::human_api_default_compile_options(),
            })
            .expect_err("sorry-shaped axiom must not pass certificate handoff");
        assert_eq!(
            sorry_err.diagnostic.kind,
            npa_frontend::HumanDiagnosticKind::KernelRejected
        );
        assert_eq!(
            sorry_err
                .diagnostic
                .payload
                .as_ref()
                .and_then(|payload| payload.phase),
            Some(npa_frontend::HumanDiagnosticPhase::CertificateHandoff)
        );
        assert!(
            sorry_err.diagnostic.message.contains("SorryDenied"),
            "{}",
            sorry_err.diagnostic.message
        );

        assert_phase6_human_real_stdlib_compile_error(
            &fixture,
            "Api.HumanRealStdlibFailedRw",
            "\
import Std.Logic
import Std.Nat
import Std.List
theorem failed_rw (n : Nat) : Eq.{1} Nat n n := by
  intro n
  rw [Nat.add_zero]",
            npa_frontend::HumanDiagnosticKind::TypeMismatch,
            npa_frontend::HumanDiagnosticPhase::TacticExecution,
        );

        for excluded in ["Nat.add_comm", "Nat.add_assoc", "List.append_assoc"] {
            assert!(
                !fixture
                    .options
                    .tactic_options
                    .simp_rules
                    .iter()
                    .any(|rule| rule.name == Name::from_dotted(excluded)),
                "{excluded} must stay out of the simp-lite profile"
            );
        }
        let simp_message = assert_phase6_human_real_stdlib_compile_error(
            &fixture,
            "Api.HumanRealStdlibLoopProneSimp",
            "\
import Std.Logic
import Std.Nat
import Std.List
theorem no_comm_simp (n m : Nat) : Eq.{1} Nat (Nat.add n m) (Nat.add m n) := by
  intro n
  intro m
  simp-lite",
            npa_frontend::HumanDiagnosticKind::TypeMismatch,
            npa_frontend::HumanDiagnosticPhase::TacticExecution,
        );
        assert!(simp_message.contains("simp-lite"), "{simp_message}");

        let bad_package = TestPackage::new("human_unapproved_std_axiom");
        let bad_certs = mvp_certificate_bytes_with_logic_axiom("Std.Logic.human_bad_axiom");
        write_mvp_package(bad_package.path(), &bad_certs);
        let err = load_machine_std_mvp_certificates(bad_package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::VerifyFailed {
                module,
                source,
            } if module == Name::from_dotted("Std.Logic")
                && matches!(*source, CertError::ForbiddenAxiom { ref axiom }
                    if *axiom == Name::from_dotted("Std.Logic.human_bad_axiom"))
        ));
    }

    #[test]
    fn phase7_human_real_stdlib_search_missing_result_regressions() {
        let fixture = phase6_human_real_stdlib_fixture("human_real_stdlib_search");

        let (mut nat_store, nat_header, nat_state_id, nat_goal_id) =
            phase6_human_real_stdlib_session(
                &fixture,
                "Api.HumanRealStdlibNatSearch",
                "Api.HumanRealStdlibNatSearch.target",
                "\
import Std.Logic
import Std.Nat
import Std.List
theorem target (n : Nat) : Eq.{1} Nat (Nat.add n Nat.zero) n := by
  simp-lite",
            );
        let (nat_state_id, nat_goal_id) = run_phase6_human_tactics(
            &mut nat_store,
            &nat_header,
            nat_state_id,
            nat_goal_id,
            &["intro n"],
        );
        let nat_search = crate::search_human_theorems_for_goal(
            &nat_store,
            crate::HumanTheoremGoalSearchRequest {
                header: nat_header.clone(),
                state_id: nat_state_id.clone(),
                goal_id: nat_goal_id.clone(),
                modes: vec![
                    crate::HumanTheoremSearchMode::Exact,
                    crate::HumanTheoremSearchMode::Rw,
                    crate::HumanTheoremSearchMode::Simp,
                ],
                options: crate::HumanTheoremSearchOptions::default(),
            },
        )
        .expect("Nat.add_zero goal search should run over real stdlib");
        assert!(nat_search.results.iter().any(|result| {
            result.name == Name::from_dotted("Nat.add_zero")
                && result.module == Name::from_dotted("Std.Nat")
                && result.mode == crate::HumanTheoremSearchMode::Rw
                && result.suggested_tactic == "rw [Nat.add_zero]"
        }));

        let missing = crate::search_human_theorems_by_name(
            &nat_store,
            crate::HumanTheoremNameSearchRequest {
                header: nat_header.clone(),
                state_id: nat_state_id.clone(),
                query: "definitely_missing_human_std_theorem".to_owned(),
                options: crate::HumanTheoremSearchOptions::default(),
            },
        )
        .expect("missing-name Human theorem search should return an empty set");
        assert!(missing.results.is_empty());
        let eq_trans_name = crate::search_human_theorems_by_name(
            &nat_store,
            crate::HumanTheoremNameSearchRequest {
                header: nat_header,
                state_id: nat_state_id,
                query: "Eq.trans".to_owned(),
                options: crate::HumanTheoremSearchOptions::default(),
            },
        )
        .expect("Eq.trans name search should run over real stdlib");
        assert!(eq_trans_name.results.iter().any(|result| {
            result.name == Name::from_dotted("Eq.trans")
                && result.module == Name::from_dotted("Std.Logic")
        }));

        let (mut list_store, list_header, list_state_id, list_goal_id) =
            phase6_human_real_stdlib_session(
                &fixture,
                "Api.HumanRealStdlibListSearch",
                "Api.HumanRealStdlibListSearch.target",
                "\
import Std.Logic
import Std.Nat
import Std.List
theorem target (A : Type) (xs : List.{1} A) : Eq.{1} (List.{1} A) (List.append.{1} A xs (List.nil.{1} A)) xs := by
  simp-lite",
            );
        let (list_state_id, list_goal_id) = run_phase6_human_tactics(
            &mut list_store,
            &list_header,
            list_state_id,
            list_goal_id,
            &["intro A", "intro xs"],
        );
        let list_search = crate::search_human_theorems_for_goal(
            &list_store,
            crate::HumanTheoremGoalSearchRequest {
                header: list_header,
                state_id: list_state_id,
                goal_id: list_goal_id,
                modes: vec![
                    crate::HumanTheoremSearchMode::Rw,
                    crate::HumanTheoremSearchMode::Simp,
                ],
                options: crate::HumanTheoremSearchOptions::default(),
            },
        )
        .expect("List.append_nil goal search should run over real stdlib");
        assert!(list_search.results.iter().any(|result| {
            result.name == Name::from_dotted("List.append_nil")
                && result.module == Name::from_dotted("Std.List")
                && result.mode == crate::HumanTheoremSearchMode::Rw
                && result.suggested_tactic == "rw [List.append_nil]"
        }));
    }

    #[test]
    fn human_theorem_index_debug_views_are_per_module_and_do_not_extend_machine_schema() {
        let package = TestPackage::new("human_theorem_index_debug_views");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (release, _, theorem_index, _, _, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        let release_hash = machine_std_library_release_hash(&release).unwrap();
        let human_view = generate_human_std_theorem_search_view(&loaded, &theorem_index).unwrap();
        let debug_views =
            generate_human_std_module_debug_views(&loaded, &human_view, &axiom_report).unwrap();

        assert_eq!(
            debug_views
                .iter()
                .map(|view| view.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        let nat_debug = human_module_debug_view(&debug_views, "Std.Nat");
        assert!(nat_debug
            .index
            .entries
            .iter()
            .any(|entry| entry.global_ref.name == Name::from_dotted("Nat.add_zero")));
        assert!(nat_debug.graph.edges.iter().any(|edge| {
            edge.source.name == Name::from_dotted("Nat.add_zero")
                && matches!(
                    edge.kind,
                    HumanStdDependencyKind::StatementHead
                        | HumanStdDependencyKind::StatementConstant
                        | HumanStdDependencyKind::AxiomDependency
                )
        }));
        for view in &debug_views {
            assert_ne!(view.index.debug_hash, [0; 32]);
            assert_ne!(view.axioms.debug_hash, [0; 32]);
            assert_ne!(view.graph.debug_hash, [0; 32]);
            assert!(view
                .axioms
                .module_axioms
                .iter()
                .chain(view.axioms.transitive_axioms.iter())
                .all(|axiom| axiom.name == Name::from_dotted("Eq.rec")));
        }

        let theorem_index_json = theorem_index_json(&theorem_index);
        for human_only_field in ["categories", "suggested_tactics", "debug_hash"] {
            assert!(
                !theorem_index_json.contains(human_only_field),
                "MachineStdTheoremIndex JSON must stay separate from Human debug schema"
            );
        }
        assert!(human_view
            .entries
            .iter()
            .any(|entry| !entry.suggested_tactics.is_empty()));

        write_poison_human_std_source_and_debug_files(package.path());
        let loaded_after = load_machine_std_mvp_certificates(package.path()).unwrap();
        let (release_after, _, theorem_index_after, _, _, axiom_report_after) =
            final_sidecar_artifacts_for_loaded(&loaded_after);
        let human_view_after =
            generate_human_std_theorem_search_view(&loaded_after, &theorem_index_after).unwrap();
        let debug_views_after = generate_human_std_module_debug_views(
            &loaded_after,
            &human_view_after,
            &axiom_report_after,
        )
        .unwrap();
        assert_eq!(
            machine_std_library_release_hash(&release_after).unwrap(),
            release_hash,
            "Human debug/source files must not become trusted release hash inputs"
        );
        assert_eq!(human_view_after.debug_hash, human_view.debug_hash);
        assert_eq!(debug_views_after, debug_views);
    }

    #[test]
    fn rejects_final_theorem_index_metadata_mismatches() {
        let package = TestPackage::new("bad_final_theorem_index_metadata");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(&loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(&loaded, &rewrite_profiles).unwrap();
        let expected = generate_machine_std_mvp_final_theorem_index(
            &loaded,
            &rewrite_profiles,
            &simp_profiles,
        )
        .unwrap();
        let nat_add_zero_index = theorem_index_entry_index(&expected, "Nat.add_zero");

        let mut stale_hash = expected.clone();
        stale_hash.index_hash = test_hash(210);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&stale_hash, &expected),
            Err(MachineStdTheoremIndexError::TheoremIndexHashMismatch { .. })
        ));

        let mut bad_modes = expected.clone();
        bad_modes.entries[nat_add_zero_index]
            .modes
            .retain(|mode| *mode != MachineTheoremMode::Simp);
        refresh_theorem_index_hash(&mut bad_modes);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&bad_modes, &expected),
            Err(MachineStdTheoremIndexError::ModesMismatch { .. })
        ));

        let mut bad_attributes = expected.clone();
        bad_attributes.entries[nat_add_zero_index]
            .attributes
            .insert(2, MachineStdAttribute::Intro);
        refresh_theorem_index_hash(&mut bad_attributes);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&bad_attributes, &expected),
            Err(MachineStdTheoremIndexError::AttributesMismatch { .. })
        ));

        let mut bad_rewrites = expected.clone();
        bad_rewrites.entries[nat_add_zero_index]
            .rewrite_descriptors
            .clear();
        refresh_theorem_index_hash(&mut bad_rewrites);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&bad_rewrites, &expected),
            Err(MachineStdTheoremIndexError::RewriteDescriptorsMismatch { .. })
        ));

        let mut duplicate_modes = expected.clone();
        duplicate_modes.entries[nat_add_zero_index].modes =
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Exact];
        refresh_theorem_index_hash(&mut duplicate_modes);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&duplicate_modes, &expected),
            Err(MachineStdTheoremIndexError::NonCanonicalModes { .. })
        ));

        let mut duplicate_rewrites = expected.clone();
        let descriptor =
            duplicate_rewrites.entries[nat_add_zero_index].rewrite_descriptors[0].clone();
        duplicate_rewrites.entries[nat_add_zero_index]
            .rewrite_descriptors
            .push(descriptor);
        refresh_theorem_index_hash(&mut duplicate_rewrites);
        assert!(matches!(
            validate_machine_std_mvp_final_theorem_index(&duplicate_rewrites, &expected),
            Err(MachineStdTheoremIndexError::NonCanonicalRewriteDescriptors { .. })
        ));
    }

    #[test]
    fn package_loader_rejects_stale_final_theorem_index_self_hash() {
        let package = TestPackage::new("stale_final_theorem_index_package");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (
            mut release,
            import_bundles,
            mut theorem_index,
            rewrite_profiles,
            simp_profiles,
            axiom_report,
        ) = final_sidecar_artifacts_for_loaded(&loaded);
        theorem_index.index_hash = test_hash(210);
        release.theorem_index_hash = theorem_index.index_hash;

        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );

        let err = load_machine_std_mvp_release(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdTheoremIndex(
                MachineStdTheoremIndexError::TheoremIndexHashMismatch { .. }
            )
        ));
    }

    #[test]
    fn validates_optional_prompt_metadata_subset_without_manifest_binding() {
        let package = TestPackage::new("prompt_metadata_subset");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (
            release,
            import_bundles,
            theorem_index,
            _rewrite_profiles,
            _simp_profiles,
            _axiom_report,
        ) = final_sidecar_artifacts_for_loaded(&loaded);
        let nat_add_zero = theorem_index_entry(&theorem_index, "Nat.add_zero");
        let mut prompt_metadata = prompt_metadata_set_for_entries(vec![prompt_metadata_entry(
            nat_add_zero.global_ref.clone(),
            STD_NAT_BUNDLE_ID,
            "simp",
            &["nat", "simp"],
        )]);
        validate_machine_std_mvp_optional_prompt_metadata(None, &theorem_index, &import_bundles)
            .unwrap();
        validate_machine_std_mvp_optional_prompt_metadata(
            Some(&prompt_metadata),
            &theorem_index,
            &import_bundles,
        )
        .unwrap();

        let parsed =
            parse_machine_std_prompt_metadata_json(&prompt_metadata_set_json(&prompt_metadata))
                .unwrap();
        assert_eq!(parsed, prompt_metadata);
        validate_machine_std_mvp_prompt_metadata(&parsed, &theorem_index, &import_bundles).unwrap();

        let mut example_order = prompt_metadata.clone();
        example_order.entries[0]
            .examples
            .push(MachineStdPromptExample {
                goal_core_hash: test_hash(172),
                imports_bundle_id: STD_NAT_BUNDLE_ID.to_owned(),
                candidate_kind: "note".to_owned(),
                display: "note".to_owned(),
            });
        refresh_prompt_metadata_hash(&mut example_order);
        let original_example_order_hash = example_order.prompt_metadata_hash;
        example_order.entries[0].examples.swap(0, 1);
        refresh_prompt_metadata_hash(&mut example_order);
        assert_ne!(
            original_example_order_hash,
            example_order.prompt_metadata_hash
        );

        let release_hash = machine_std_library_release_hash(&release).unwrap();
        prompt_metadata.entries[0].short_doc =
            Some("same trusted release, new display text".into());
        refresh_prompt_metadata_hash(&mut prompt_metadata);
        assert_eq!(
            machine_std_library_release_hash(&release).unwrap(),
            release_hash
        );
        assert_ne!(
            parsed.prompt_metadata_hash,
            prompt_metadata.prompt_metadata_hash
        );
    }

    #[test]
    fn audits_mvp_release_artifacts_for_independent_checker() {
        let package = TestPackage::new("independent_checker_audit_report");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        let nat_add_zero = theorem_index_entry(&theorem_index, "Nat.add_zero");
        let prompt_metadata = prompt_metadata_set_for_entries(vec![prompt_metadata_entry(
            nat_add_zero.global_ref.clone(),
            STD_NAT_BUNDLE_ID,
            "simp",
            &["nat", "simp"],
        )]);

        let report = audit_machine_std_mvp_release_artifacts(
            &release,
            &loaded,
            MachineStdAuditArtifacts {
                import_bundles: &import_bundles,
                theorem_index: &theorem_index,
                rewrite_profiles: &rewrite_profiles,
                simp_profiles: &simp_profiles,
                axiom_report: &axiom_report,
                prompt_metadata: Some(&prompt_metadata),
            },
        )
        .unwrap();

        let check_ids = report
            .checks
            .iter()
            .map(|check| check.check_id.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            check_ids,
            vec![
                "manifest.verifier-output",
                "manifest.release-hash",
                "sidecar.axiom-report.hash",
                "sidecar.rewrite-profiles.hash",
                "sidecar.simp-profiles.hash",
                "sidecar.import-bundles.hash",
                "sidecar.theorem-index.hash",
                "profiles.target-decl-interface-hash",
                "import-bundles.minimal-closure-and-axioms",
                "optional.prompt-metadata.excluded-from-release-hash",
            ]
        );
        assert!(report.checks.iter().all(|check| check.passed));
        assert_eq!(report.audit_profile_id, STD_AUDIT_PROFILE_ID);
        assert_eq!(report.library_profile_id, STD_LIBRARY_PROFILE_ID);
        assert_eq!(
            report.std_library_release_hash,
            machine_std_library_release_hash(&release).unwrap()
        );
        assert_eq!(report.manifest_hash, report.std_library_release_hash);
        assert_eq!(
            report.prompt_metadata_hash,
            Some(prompt_metadata.prompt_metadata_hash)
        );
        assert!(report.prompt_metadata_excluded_from_release_hash);
        assert_eq!(
            report.audit_report_hash,
            machine_std_audit_report_hash(&report)
        );
        let validated = MachineStdValidatedRelease {
            manifest: release.clone(),
            loaded: loaded.clone(),
            axiom_report: axiom_report.clone(),
            import_bundles: import_bundles.clone(),
            std_library_release_hash: machine_std_library_release_hash(&release).unwrap(),
        };
        let validated_report = audit_machine_std_mvp_validated_release(
            &validated,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            Some(&prompt_metadata),
        )
        .unwrap();
        assert_eq!(validated_report.audit_report_hash, report.audit_report_hash);

        let mut stale_validated = validated.clone();
        stale_validated.std_library_release_hash = test_hash(233);
        assert!(matches!(
            audit_machine_std_mvp_validated_release(
                &stale_validated,
                &theorem_index,
                &rewrite_profiles,
                &simp_profiles,
                Some(&prompt_metadata),
            ),
            Err(MachineStdAuditError::ReleaseHashMismatch { .. })
        ));

        let mut display_only_metadata = prompt_metadata.clone();
        display_only_metadata.entries[0].short_doc = Some("different display text".to_owned());
        refresh_prompt_metadata_hash(&mut display_only_metadata);
        let display_report = audit_machine_std_mvp_release_artifacts(
            &release,
            &loaded,
            MachineStdAuditArtifacts {
                import_bundles: &import_bundles,
                theorem_index: &theorem_index,
                rewrite_profiles: &rewrite_profiles,
                simp_profiles: &simp_profiles,
                axiom_report: &axiom_report,
                prompt_metadata: Some(&display_only_metadata),
            },
        )
        .unwrap();
        assert_ne!(
            report.prompt_metadata_hash,
            display_report.prompt_metadata_hash
        );
        assert_eq!(
            report.std_library_release_hash,
            display_report.std_library_release_hash
        );
    }

    #[test]
    fn audit_rejects_manifest_bound_sidecar_hash_mismatch() {
        let package = TestPackage::new("independent_checker_audit_sidecar_hash_mismatch");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (
            mut release,
            import_bundles,
            theorem_index,
            rewrite_profiles,
            simp_profiles,
            axiom_report,
        ) = final_sidecar_artifacts_for_loaded(&loaded);
        release.theorem_index_hash = test_hash(231);

        let err = audit_machine_std_mvp_release_artifacts(
            &release,
            &loaded,
            MachineStdAuditArtifacts {
                import_bundles: &import_bundles,
                theorem_index: &theorem_index,
                rewrite_profiles: &rewrite_profiles,
                simp_profiles: &simp_profiles,
                axiom_report: &axiom_report,
                prompt_metadata: None,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdAuditError::SidecarHashMismatch {
                field: "theorem_index_hash",
                ..
            }
        ));
    }

    #[test]
    fn audit_rejects_custom_import_bundle_allow_axiom() {
        let package = TestPackage::new("independent_checker_audit_custom_allow_axiom");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (
            mut release,
            mut import_bundles,
            theorem_index,
            rewrite_profiles,
            simp_profiles,
            axiom_report,
        ) = final_sidecar_artifacts_for_loaded(&loaded);
        import_bundles.bundles[0]
            .allow_axioms
            .push(MachineAxiomRefWire::CurrentModule {
                module: Name::from_dotted("Std.Logic"),
                name: Name::from_dotted("Unsafe.custom"),
                source_index: 0,
                decl_interface_hash: test_hash(232),
            });
        import_bundles.import_bundles_hash =
            machine_std_import_bundle_set_hash(&import_bundles).unwrap();
        release.import_bundles_hash = import_bundles.import_bundles_hash;

        let err = audit_machine_std_mvp_release_artifacts(
            &release,
            &loaded,
            MachineStdAuditArtifacts {
                import_bundles: &import_bundles,
                theorem_index: &theorem_index,
                rewrite_profiles: &rewrite_profiles,
                simp_profiles: &simp_profiles,
                axiom_report: &axiom_report,
                prompt_metadata: None,
            },
        )
        .unwrap_err();
        assert!(matches!(err, MachineStdAuditError::CustomAllowAxiom { .. }));
    }

    #[test]
    fn std_library_release_artifacts_drive_m8_search_candidates_through_machine_api_batch() {
        let package = TestPackage::new("std_library_release_m8_search_candidates");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        let release_json = release_manifest_json(&release);
        let import_bundles_json = import_bundle_set_json(&import_bundles);
        let theorem_index_json = theorem_index_json(&theorem_index);
        let rewrite_profiles_json = rewrite_profile_set_json(&rewrite_profiles);
        let simp_profiles_json = simp_profile_set_json(&simp_profiles);
        let axiom_report_json = axiom_report_json(&axiom_report);
        let nat_add_zero_sidecar = theorem_index_entry(&theorem_index, "Nat.add_zero").clone();
        let prompt_metadata = prompt_metadata_set_for_entries(vec![prompt_metadata_entry(
            nat_add_zero_sidecar.global_ref.clone(),
            STD_NAT_BUNDLE_ID,
            "simp",
            &["nat", "simp"],
        )]);
        let prompt_metadata_json = prompt_metadata_set_json(&prompt_metadata);

        let (validated, loaded_prompt_metadata) =
            load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
                package.path(),
                &release_json,
                MachineStdReleaseSidecarJson {
                    import_bundles_json: &import_bundles_json,
                    theorem_index_json: &theorem_index_json,
                    rewrite_profiles_json: &rewrite_profiles_json,
                    simp_profiles_json: &simp_profiles_json,
                    axiom_report_json: &axiom_report_json,
                    prompt_metadata_json: Some(&prompt_metadata_json),
                },
            )
            .unwrap();
        assert_eq!(validated.import_bundles, import_bundles);

        let parsed_theorem_index =
            parse_machine_std_theorem_index_json(&theorem_index_json).unwrap();
        let loaded_prompt_metadata = loaded_prompt_metadata.unwrap();
        assert_eq!(loaded_prompt_metadata, prompt_metadata);
        assert_eq!(
            loaded_prompt_metadata.entries[0].global_ref,
            nat_add_zero_sidecar.global_ref
        );
        assert_eq!(
            loaded_prompt_metadata.entries[0].examples[0].imports_bundle_id,
            STD_NAT_BUNDLE_ID
        );

        let nat_bundle = validated
            .import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        assert_eq!(
            nat_bundle.recommended_tactic_options.recipe_id,
            STD_NAT_RECIPE_ID
        );
        let nat_add_zero_recipe_rule = nat_bundle
            .recommended_tactic_options
            .simp_rules
            .iter()
            .find(|rule| {
                rule.name == nat_add_zero_sidecar.global_ref.name
                    && rule.decl_interface_hash
                        == nat_add_zero_sidecar.global_ref.decl_interface_hash
                    && rule.direction == RewriteDirection::Forward
            })
            .unwrap();

        let session = crate::create_machine_session(&session_create_json_for_bundle(nat_bundle))
            .unwrap()
            .session;
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Std.Nat"]}"#;
        let first =
            search_machine_theorems_for_goal(&m8_search_json(&session, filters), &session).unwrap();
        let second =
            search_machine_theorems_for_goal(&m8_search_json(&session, filters), &session).unwrap();
        let (first_fields, second_fields) = match (first, second) {
            (MachineApiResponseEnvelope::Ok(first), MachineApiResponseEnvelope::Ok(second)) => {
                (first.endpoint_fields, second.endpoint_fields)
            }
            _ => panic!("standard library Nat bundle search should succeed"),
        };
        assert_eq!(
            first_fields.query_fingerprint,
            second_fields.query_fingerprint
        );
        assert_eq!(
            first_fields.theorem_index_fingerprint,
            second_fields.theorem_index_fingerprint
        );
        assert_eq!(first_fields.results, second_fields.results);

        let expected_nat_entries = parsed_theorem_index
            .entries
            .iter()
            .filter(|entry| entry.global_ref.module == Name::from_dotted("Std.Nat"))
            .map(|entry| (entry.global_ref.name.clone(), entry))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(first_fields.results.len(), expected_nat_entries.len());
        for result in &first_fields.results {
            let sidecar = expected_nat_entries.get(&result.global_ref.name).expect(
                "search result should come from the standard library theorem index sidecar",
            );
            assert_eq!(result.global_ref.module, sidecar.global_ref.module);
            assert_eq!(
                result.global_ref.export_hash,
                sidecar.global_ref.export_hash
            );
            assert_eq!(
                result.global_ref.decl_interface_hash,
                sidecar.global_ref.decl_interface_hash
            );
            assert_eq!(result.statement.core_hash, sidecar.statement_core_hash);
            for mode in &sidecar.modes {
                assert!(
                    result.modes.contains(mode),
                    "search result should preserve sidecar mode {mode:?}"
                );
            }
        }

        let result = first_fields
            .results
            .iter()
            .find(|result| result.global_ref.name == Name::from_dotted("Nat.add_zero"))
            .unwrap();
        assert_eq!(result.modes, nat_add_zero_sidecar.modes);
        assert_eq!(result.suggested_candidates.len(), 2);
        assert_eq!(
            result
                .suggested_candidates
                .iter()
                .map(|candidate| candidate.status)
                .collect::<Vec<_>>(),
            vec![
                MachineSuggestedCandidateStatus::Validated,
                MachineSuggestedCandidateStatus::Validated,
            ]
        );

        let MachineTacticCandidate::Rewrite {
            rule,
            direction,
            site,
        } = &result.suggested_candidates[0].candidate
        else {
            panic!("first Nat.add_zero suggestion should be rw");
        };
        assert_eq!(*direction, RewriteDirection::Forward);
        assert_eq!(*site, RewriteSite::EqTargetLeft);
        let TacticHead::Imported {
            name,
            decl_interface_hash,
        } = &rule.head
        else {
            panic!("rw suggestion should reference an imported theorem");
        };
        assert_eq!(name, &nat_add_zero_sidecar.global_ref.name);
        assert_eq!(
            decl_interface_hash,
            &nat_add_zero_sidecar.global_ref.decl_interface_hash
        );
        assert!(rule.universe_args.is_empty());
        assert_eq!(rule.args.len(), 1);
        assert!(matches!(rule.args[0], CandidateApplyArg::InferFromTarget));

        let MachineTacticCandidate::SimpLite { rules } = &result.suggested_candidates[1].candidate
        else {
            panic!("second Nat.add_zero suggestion should be simp-lite");
        };
        assert_eq!(
            rules.as_slice(),
            std::slice::from_ref(nat_add_zero_recipe_rule)
        );

        let batch_candidates = result
            .suggested_candidates
            .iter()
            .enumerate()
            .map(|(index, candidate)| {
                m8_batch_candidate_json(
                    &format!("std_library_nat_add_zero_{index}"),
                    &m8_suggested_candidate_json(&candidate.candidate),
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let mut batch_session =
            crate::create_machine_session(&session_create_json_for_bundle(nat_bundle))
                .unwrap()
                .session;
        let batch_response = run_machine_tactic_batch_request(
            &m8_batch_json(&batch_session, &format!("[{batch_candidates}]")),
            &mut batch_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(batch_ok) = batch_response else {
            panic!("standard library suggested candidates should re-enter machine API batch");
        };
        assert_eq!(
            batch_ok.endpoint_fields.success_count + batch_ok.endpoint_fields.failure_count,
            result.suggested_candidates.len() as u32
        );
        for (index, item) in batch_ok.endpoint_fields.results.iter().enumerate() {
            let candidate_hash = match item {
                MachineTacticBatchItemResponse::Success { candidate_hash, .. } => *candidate_hash,
                MachineTacticBatchItemResponse::Error {
                    candidate_hash: Some(candidate_hash),
                    ..
                } => *candidate_hash,
                MachineTacticBatchItemResponse::Error {
                    candidate_hash: None,
                    ..
                } => panic!("candidate {index} should canonicalize before execution"),
            };
            let suggested = &result.suggested_candidates[index];
            let payload_hash = machine_tactic_validate_machine_tactic_candidate(
                batch_session.initial_snapshot.open_goals[0],
                suggested.candidate.clone(),
            )
            .unwrap()
            .candidate_hash;
            assert_eq!(suggested.candidate_hash, payload_hash);
            assert_ne!(candidate_hash, suggested.candidate_hash);
        }
    }

    #[test]
    fn source_built_std_artifacts_feed_machine_release_sessions_retrieval_and_audit() {
        let package = TestPackage::new("source_built_std_ai_release_loader");
        write_valid_mvp_source_package(package.path());
        let built = build_mvp_source_package_artifacts(package.path()).unwrap();
        let built_by_module = built
            .iter()
            .map(|artifact| (artifact.module.clone(), artifact))
            .collect::<BTreeMap<_, _>>();

        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        assert_eq!(
            loaded
                .verification_order()
                .iter()
                .map(Name::as_dotted)
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        for module in loaded.modules() {
            let built = built_by_module.get(&module.module).unwrap();
            assert_eq!(module.certificate_bytes, built.certificate_bytes);
            assert_eq!(module.expected_export_hash, built.export_hash);
            assert_eq!(module.expected_certificate_hash, built.certificate_hash);
            assert_eq!(module.axiom_report_hash, built.axiom_report_hash);
        }

        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );

        let validated = load_machine_std_mvp_release(package.path()).unwrap();
        assert_eq!(validated.manifest, release);
        assert_eq!(validated.import_bundles, import_bundles);
        assert_eq!(
            validated.std_library_release_hash,
            machine_std_library_release_hash(&release).unwrap()
        );
        assert_eq!(
            release.import_bundles_hash,
            machine_std_import_bundle_set_hash(&import_bundles).unwrap()
        );
        assert_eq!(
            release.theorem_index_hash,
            machine_std_theorem_index_hash(&theorem_index).unwrap()
        );
        assert_eq!(
            release.rewrite_profiles_hash,
            machine_std_rewrite_profile_set_hash(&rewrite_profiles).unwrap()
        );
        assert_eq!(
            release.simp_profiles_hash,
            machine_std_simp_profile_set_hash(&simp_profiles).unwrap()
        );
        assert_eq!(
            release.axiom_report_hash,
            machine_std_axiom_report_hash(&axiom_report).unwrap()
        );

        let audit = audit_machine_std_mvp_validated_release(
            &validated,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            None,
        )
        .unwrap();
        assert!(audit.checks.iter().all(|check| check.passed));
        assert_eq!(
            audit.audit_report_hash,
            machine_std_audit_report_hash(&audit)
        );

        for bundle_id in [STD_NAT_BUNDLE_ID, STD_LIST_BUNDLE_ID, STD_ALL_BUNDLE_ID] {
            let bundle = validated
                .import_bundles
                .bundles
                .iter()
                .find(|bundle| bundle.bundle_id == bundle_id)
                .unwrap();
            for certificate in &bundle.import_closure {
                let built = built_by_module.get(&certificate.module).unwrap();
                assert_eq!(
                    certificate.certificate_bytes,
                    built.certificate_bytes,
                    "{bundle_id} must embed source-built certificate bytes for {}",
                    certificate.module.as_dotted()
                );
            }
            let session = crate::create_machine_session(&session_create_json_for_bundle(bundle))
                .unwrap()
                .session;
            assert_eq!(
                session.options.kernel_check_profile,
                crate::KernelCheckProfileId::BuiltinNone
            );
            assert_eq!(
                session.options.tactic_options,
                machine_std_tactic_options_recipe_request(&bundle.recommended_tactic_options)
            );
            assert_eq!(session.imports, bundle.root_imports);
        }

        let parsed_theorem_index =
            parse_machine_std_theorem_index_json(&theorem_index_json(&theorem_index)).unwrap();
        assert_eq!(parsed_theorem_index, theorem_index);
        let nat_bundle = validated
            .import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        let theorem_type = "Eq.{1} Nat (Nat.add Nat.zero Nat.zero) Nat.zero";
        let search_session = crate::create_machine_session(
            &session_create_json_for_bundle_with_theorem_type(nat_bundle, theorem_type),
        )
        .unwrap()
        .session;
        assert_eq!(search_session.initial_snapshot.open_goals, vec![GoalId(0)]);

        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Std.Nat"]}"#;
        let search = search_machine_theorems_for_goal(
            &m8_search_json(&search_session, filters),
            &search_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(search_ok) = search else {
            panic!("source-built std theorem retrieval should succeed");
        };
        let nat_add_zero_sidecar = theorem_index_entry(&parsed_theorem_index, "Nat.add_zero");
        let nat_add_zero = search_ok
            .endpoint_fields
            .results
            .iter()
            .find(|result| result.global_ref.name == Name::from_dotted("Nat.add_zero"))
            .expect("retrieval should expose Nat.add_zero from the source-built theorem index");
        assert_eq!(
            nat_add_zero.global_ref.export_hash,
            nat_add_zero_sidecar.global_ref.export_hash
        );
        assert_eq!(
            nat_add_zero.global_ref.decl_interface_hash,
            nat_add_zero_sidecar.global_ref.decl_interface_hash
        );
        assert!(nat_add_zero
            .suggested_candidates
            .iter()
            .all(|candidate| candidate.status == MachineSuggestedCandidateStatus::Validated));
        assert!(
            !nat_add_zero.suggested_candidates.is_empty(),
            "retrieval should produce candidates but not close the proof state"
        );
        assert_eq!(search_session.initial_snapshot.open_goals, vec![GoalId(0)]);

        let candidate_jsons = nat_add_zero
            .suggested_candidates
            .iter()
            .enumerate()
            .map(|(index, candidate)| {
                (
                    format!("source_built_nat_add_zero_{index}"),
                    m8_suggested_candidate_json(&candidate.candidate),
                )
            })
            .collect::<Vec<_>>();
        let batch_candidates = candidate_jsons
            .iter()
            .map(|(candidate_id, candidate_json)| {
                m8_batch_candidate_json(candidate_id, candidate_json)
            })
            .collect::<Vec<_>>()
            .join(",");
        let mut batch_session = crate::create_machine_session(
            &session_create_json_for_bundle_with_theorem_type(nat_bundle, theorem_type),
        )
        .unwrap()
        .session;
        let batch = run_machine_tactic_batch_request(
            &m8_batch_json(&batch_session, &format!("[{batch_candidates}]")),
            &mut batch_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(batch_ok) = batch else {
            panic!("source-built std candidates should re-enter machine batch");
        };
        let success = batch_ok
            .endpoint_fields
            .results
            .iter()
            .find_map(|item| match item {
                MachineTacticBatchItemResponse::Success {
                    candidate_id,
                    candidate_hash,
                    next_snapshot_id,
                    next_state_fingerprint,
                    proof_delta_hash,
                } => Some((
                    candidate_id,
                    candidate_hash,
                    next_snapshot_id,
                    next_state_fingerprint,
                    proof_delta_hash,
                )),
                MachineTacticBatchItemResponse::Error { .. } => None,
            })
            .expect("at least one retrieved candidate should close the source-built Nat goal");
        let candidate_json = candidate_jsons
            .iter()
            .find(|(candidate_id, _)| candidate_id == success.0)
            .map(|(_, json)| json.as_str())
            .unwrap();
        let replay_step = m8_replay_step_json(
            batch_ok.endpoint_fields.previous_state_fingerprint,
            GoalId(0),
            candidate_json,
            *success.1,
            batch_ok.endpoint_fields.deterministic_budget_hash,
            *success.4,
            *success.3,
        );
        assert_eq!(*success.2, SnapshotId::from_state_fingerprint(*success.3));

        let mut replay_session = crate::create_machine_session(
            &session_create_json_for_bundle_with_theorem_type(nat_bundle, theorem_type),
        )
        .unwrap()
        .session;
        let replay = run_machine_replay_request(
            &m8_replay_json(&replay_session, &format!("[{replay_step}]"), *success.3),
            &mut replay_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(replay_ok) = replay else {
            panic!("source-built std candidate should replay before adoption");
        };
        assert_eq!(
            replay_ok.endpoint_fields.final_state_fingerprint,
            *success.3
        );

        let verify = run_machine_verify_request(
            &m8_verify_json(
                &replay_session,
                replay_ok.endpoint_fields.final_snapshot_id,
                replay_ok.endpoint_fields.final_state_fingerprint,
            ),
            &replay_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(verify_ok) = verify else {
            panic!("source-built std replay must verify before adoption");
        };
        assert_eq!(verify_ok.endpoint_fields.root_axioms_used, Vec::new());
        for dependency in &verify_ok.endpoint_fields.dependency_import_closure {
            let bundled = nat_bundle
                .import_closure
                .iter()
                .find(|certificate| certificate.module == dependency.module)
                .unwrap();
            assert_eq!(
                dependency.expected_export_hash,
                bundled.expected_export_hash
            );
            assert_eq!(
                dependency.expected_certificate_hash,
                bundled.expected_certificate_hash
            );
            assert_eq!(
                dependency.certificate.bytes,
                lower_hex_bytes(&bundled.certificate_bytes)
            );
        }
    }

    #[test]
    fn source_built_std_release_rejects_stale_machine_artifact_refs() {
        let package = TestPackage::new("source_built_std_stale_ai_artifacts");
        write_valid_mvp_source_package(package.path());
        build_mvp_source_package_artifacts(package.path()).unwrap();
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        let import_bundles_json = import_bundle_set_json(&import_bundles);
        let theorem_index_json_value = theorem_index_json(&theorem_index);
        let rewrite_profiles_json = rewrite_profile_set_json(&rewrite_profiles);
        let simp_profiles_json = simp_profile_set_json(&simp_profiles);
        let axiom_report_json = axiom_report_json(&axiom_report);

        let mut stale_export = release.clone();
        module_artifact_mut(&mut stale_export, "Std.Nat").expected_export_hash = test_hash(240);
        let err = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
            package.path(),
            &release_manifest_json(&stale_export),
            MachineStdReleaseSidecarJson {
                import_bundles_json: &import_bundles_json,
                theorem_index_json: &theorem_index_json_value,
                rewrite_profiles_json: &rewrite_profiles_json,
                simp_profiles_json: &simp_profiles_json,
                axiom_report_json: &axiom_report_json,
                prompt_metadata_json: None,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::ModuleArtifactHashMismatch {
                    field: "expected_export_hash",
                    ..
                }
            )
        ));

        let mut stale_certificate = release.clone();
        module_artifact_mut(&mut stale_certificate, "Std.Nat").expected_certificate_hash =
            test_hash(241);
        let err = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
            package.path(),
            &release_manifest_json(&stale_certificate),
            MachineStdReleaseSidecarJson {
                import_bundles_json: &import_bundles_json,
                theorem_index_json: &theorem_index_json_value,
                rewrite_profiles_json: &rewrite_profiles_json,
                simp_profiles_json: &simp_profiles_json,
                axiom_report_json: &axiom_report_json,
                prompt_metadata_json: None,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::ModuleArtifactHashMismatch {
                    field: "expected_certificate_hash",
                    ..
                }
            )
        ));

        let mut stale_index = theorem_index.clone();
        let nat_add_zero_index = theorem_index_entry_index(&stale_index, "Nat.add_zero");
        stale_index.entries[nat_add_zero_index]
            .global_ref
            .decl_interface_hash = test_hash(242);
        stale_index.entries.sort_by_cached_key(|entry| {
            machine_std_global_ref_canonical_bytes(&entry.global_ref).unwrap()
        });
        refresh_theorem_index_hash(&mut stale_index);
        let mut stale_index_release = release.clone();
        stale_index_release.theorem_index_hash = stale_index.index_hash;
        let stale_theorem_index_json = theorem_index_json(&stale_index);
        let err = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
            package.path(),
            &release_manifest_json(&stale_index_release),
            MachineStdReleaseSidecarJson {
                import_bundles_json: &import_bundles_json,
                theorem_index_json: &stale_theorem_index_json,
                rewrite_profiles_json: &rewrite_profiles_json,
                simp_profiles_json: &simp_profiles_json,
                axiom_report_json: &axiom_report_json,
                prompt_metadata_json: None,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdTheoremIndex(
                MachineStdTheoremIndexError::InvalidEntryMembership { .. }
            )
        ));
    }

    #[test]
    fn exposes_std_logic_connectives_to_apply_search() {
        let package = TestPackage::new("std_logic_connective_apply_search");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );
        let release_json = release_manifest_json(&release);
        let import_bundles_json = import_bundle_set_json(&import_bundles);
        let theorem_index_json = theorem_index_json(&theorem_index);
        let rewrite_profiles_json = rewrite_profile_set_json(&rewrite_profiles);
        let simp_profiles_json = simp_profile_set_json(&simp_profiles);
        let axiom_report_json = axiom_report_json(&axiom_report);
        let (validated, _) = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
            package.path(),
            &release_json,
            MachineStdReleaseSidecarJson {
                import_bundles_json: &import_bundles_json,
                theorem_index_json: &theorem_index_json,
                rewrite_profiles_json: &rewrite_profiles_json,
                simp_profiles_json: &simp_profiles_json,
                axiom_report_json: &axiom_report_json,
                prompt_metadata_json: None,
            },
        )
        .unwrap();
        let logic_bundle = validated
            .import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_LOGIC_BUNDLE_ID)
            .unwrap();
        let session = crate::create_machine_session(&session_create_json_for_bundle(logic_bundle))
            .unwrap()
            .session;
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Std.Logic"]}"#;
        let response = search_machine_theorems_for_goal(
            &m8_apply_search_json(&session, filters, 64),
            &session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("standard library logic apply search should succeed");
        };

        let results_by_name = ok
            .endpoint_fields
            .results
            .iter()
            .map(|result| (result.global_ref.name.clone(), result))
            .collect::<BTreeMap<_, _>>();
        for theorem in ["Eq.trans", "And.intro", "False.elim"] {
            let result = results_by_name
                .get(&Name::from_dotted(theorem))
                .unwrap_or_else(|| panic!("{theorem} should be available to apply search"));
            assert_eq!(result.global_ref.module, Name::from_dotted("Std.Logic"));
            assert!(result.modes.contains(&MachineTheoremMode::Apply));
        }
    }

    #[test]
    fn exposes_std_algebra_projection_theorems_to_apply_search() {
        let package = TestPackage::new("std_algebra_projection_apply_search");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );
        let release_json = release_manifest_json(&release);
        let import_bundles_json = import_bundle_set_json(&import_bundles);
        let theorem_index_json = theorem_index_json(&theorem_index);
        let rewrite_profiles_json = rewrite_profile_set_json(&rewrite_profiles);
        let simp_profiles_json = simp_profile_set_json(&simp_profiles);
        let axiom_report_json = axiom_report_json(&axiom_report);
        let (validated, _) = load_machine_std_mvp_release_with_optional_prompt_metadata_from_json(
            package.path(),
            &release_json,
            MachineStdReleaseSidecarJson {
                import_bundles_json: &import_bundles_json,
                theorem_index_json: &theorem_index_json,
                rewrite_profiles_json: &rewrite_profiles_json,
                simp_profiles_json: &simp_profiles_json,
                axiom_report_json: &axiom_report_json,
                prompt_metadata_json: None,
            },
        )
        .unwrap();
        let algebra_bundle = validated
            .import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_ALGEBRA_BASIC_BUNDLE_ID)
            .unwrap();
        let session =
            crate::create_machine_session(&session_create_json_for_bundle(algebra_bundle))
                .unwrap()
                .session;
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Std.Algebra.Basic"]}"#;
        let response = search_machine_theorems_for_goal(
            &m8_apply_search_json(&session, filters, 128),
            &session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(ok) = response else {
            panic!("standard library algebra apply search should succeed");
        };

        let results_by_name = ok
            .endpoint_fields
            .results
            .iter()
            .map(|result| (result.global_ref.name.clone(), result))
            .collect::<BTreeMap<_, _>>();
        for theorem in [
            "IsMonoid.assoc",
            "IsCommMonoid.comm",
            "IsCommMonoid.right_id",
            "identity_unique",
        ] {
            let result = results_by_name
                .get(&Name::from_dotted(theorem))
                .unwrap_or_else(|| panic!("{theorem} should be available to apply search"));
            assert_eq!(
                result.global_ref.module,
                Name::from_dotted("Std.Algebra.Basic")
            );
            assert!(result.modes.contains(&MachineTheoremMode::Apply));
        }
    }

    #[test]
    fn rejects_prompt_metadata_profile_hash_entry_and_example_mismatches() {
        let package = TestPackage::new("bad_prompt_metadata");
        let certs = mvp_certificate_bytes_with_m5_profiles();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let (
            _release,
            import_bundles,
            theorem_index,
            _rewrite_profiles,
            _simp_profiles,
            _axiom_report,
        ) = final_sidecar_artifacts_for_loaded(&loaded);
        let first = theorem_index.entries[0].global_ref.clone();
        let second = theorem_index.entries[1].global_ref.clone();
        let valid = prompt_metadata_set_for_entries(vec![prompt_metadata_entry(
            first.clone(),
            STD_NAT_BUNDLE_ID,
            "simp",
            &["nat", "simp"],
        )]);

        let mut bad_profile = valid.clone();
        bad_profile.metadata_profile_id = "npa.stdlib.prompt-metadata.bad".to_owned();
        refresh_prompt_metadata_hash(&mut bad_profile);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&bad_profile, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::MetadataProfileMismatch { .. })
        ));

        let mut bad_library = valid.clone();
        bad_library.library_profile_id = "npa.stdlib.bad".to_owned();
        refresh_prompt_metadata_hash(&mut bad_library);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&bad_library, &theorem_index, &import_bundles,),
            Err(MachineStdPromptMetadataError::LibraryProfileMismatch { .. })
        ));

        let mut stale_hash = valid.clone();
        stale_hash.prompt_metadata_hash = test_hash(211);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&stale_hash, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::PromptMetadataHashMismatch { .. })
        ));

        let mut duplicate = valid.clone();
        duplicate.entries.push(duplicate.entries[0].clone());
        refresh_prompt_metadata_hash(&mut duplicate);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&duplicate, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::DuplicateEntry { .. })
        ));

        let mut reordered = prompt_metadata_set_for_entries(vec![
            prompt_metadata_entry(first.clone(), STD_NAT_BUNDLE_ID, "simp", &["nat", "simp"]),
            prompt_metadata_entry(second.clone(), STD_NAT_BUNDLE_ID, "simp", &["nat", "simp"]),
        ]);
        reordered.entries.swap(0, 1);
        refresh_prompt_metadata_hash(&mut reordered);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&reordered, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::NonCanonicalEntryOrder { .. })
        ));

        let mut stale_ref = valid.clone();
        stale_ref.entries[0].global_ref.decl_interface_hash = test_hash(212);
        refresh_prompt_metadata_hash(&mut stale_ref);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&stale_ref, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::StaleGlobalRef { .. })
        ));

        let mut bad_tag_order = valid.clone();
        bad_tag_order.entries[0].tags = vec!["simp".to_owned(), "nat".to_owned()];
        refresh_prompt_metadata_hash(&mut bad_tag_order);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(
                &bad_tag_order,
                &theorem_index,
                &import_bundles,
            ),
            Err(MachineStdPromptMetadataError::NonCanonicalTagOrder { .. })
        ));

        let mut duplicate_tag = valid.clone();
        duplicate_tag.entries[0].tags = vec!["nat".to_owned(), "nat".to_owned()];
        refresh_prompt_metadata_hash(&mut duplicate_tag);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(
                &duplicate_tag,
                &theorem_index,
                &import_bundles,
            ),
            Err(MachineStdPromptMetadataError::DuplicateTag { .. })
        ));

        let mut unknown_tag = valid.clone();
        unknown_tag.entries[0].tags = vec!["nat".to_owned(), "unknown".to_owned()];
        refresh_prompt_metadata_hash(&mut unknown_tag);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&unknown_tag, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::UnknownTag { .. })
        ));

        let mut bad_candidate = valid.clone();
        bad_candidate.entries[0].examples[0].candidate_kind = "intro".to_owned();
        refresh_prompt_metadata_hash(&mut bad_candidate);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(
                &bad_candidate,
                &theorem_index,
                &import_bundles,
            ),
            Err(MachineStdPromptMetadataError::InvalidCandidateKind { .. })
        ));

        let mut bad_bundle = valid.clone();
        bad_bundle.entries[0].examples[0].imports_bundle_id = "std.missing.mvp".to_owned();
        refresh_prompt_metadata_hash(&mut bad_bundle);
        assert!(matches!(
            validate_machine_std_mvp_prompt_metadata(&bad_bundle, &theorem_index, &import_bundles),
            Err(MachineStdPromptMetadataError::UnknownImportBundle { .. })
        ));
    }

    #[test]
    fn generates_mvp_theorem_index_from_public_theorem_and_axiom_exports() {
        let package = TestPackage::new("mvp_theorem_index_base");
        let certs = mvp_certificate_bytes_with_logic_axiom_theorem();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let logic = loaded.module(&Name::from_dotted("Std.Logic")).unwrap();

        let theorem_index = generate_machine_std_mvp_theorem_index(&loaded).unwrap();
        validate_machine_std_mvp_theorem_index(&theorem_index, &theorem_index).unwrap();
        assert_eq!(theorem_index.entries.len(), 2);
        assert_eq!(theorem_index.index_hash, [0; 32]);
        assert_ne!(
            machine_std_theorem_index_hash(&theorem_index).unwrap(),
            [0; 32]
        );

        let p_export = export_entry(logic, "P");
        let p_id_export = export_entry(logic, "p_id");
        let p_entry = theorem_index_entry(&theorem_index, "P");
        let p_id_entry = theorem_index_entry(&theorem_index, "p_id");

        assert_eq!(p_entry.kind, MachineStdTheoremKind::Axiom);
        assert_eq!(p_entry.statement_core_hash, p_export.type_hash);
        assert_eq!(p_id_entry.kind, MachineStdTheoremKind::Theorem);
        assert_eq!(p_id_entry.statement_core_hash, p_id_export.type_hash);
        assert_eq!(
            p_id_entry.modes,
            vec![MachineTheoremMode::Exact, MachineTheoremMode::Apply]
        );
        assert!(p_id_entry.attributes.is_empty());
        assert!(p_id_entry.rewrite_descriptors.is_empty());
        assert_eq!(p_id_entry.proof_term_size, None);
        assert_eq!(
            p_id_entry.statement_head.as_ref(),
            p_id_entry.constants.first()
        );
        assert!(matches!(
            p_id_entry.statement_head.as_ref(),
            Some(MachineStdGlobalRefView::Decl {
                module,
                name,
                public_export: true,
                ..
            }) if *module == Name::from_dotted("Std.Logic") && *name == Name::from_dotted("P")
        ));
        assert_eq!(
            p_id_entry
                .axiom_dependencies
                .iter()
                .map(|axiom| axiom.name.as_dotted())
                .collect::<Vec<_>>(),
            vec!["P"]
        );
    }

    #[test]
    fn theorem_index_base_validation_defers_profile_metadata_and_final_hash() {
        let package = TestPackage::new("theorem_index_base_defers_metadata");
        let certs = mvp_certificate_bytes_with_logic_axiom_theorem();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let expected = generate_machine_std_mvp_theorem_index(&loaded).unwrap();
        let p_id_index = expected
            .entries
            .iter()
            .position(|entry| entry.global_ref.name == Name::from_dotted("p_id"))
            .unwrap();

        let mut actual = expected.clone();
        actual.index_hash = test_hash(230);
        actual.entries[p_id_index].modes = vec![
            MachineTheoremMode::Exact,
            MachineTheoremMode::Apply,
            MachineTheoremMode::Rw,
            MachineTheoremMode::Simp,
        ];
        actual.entries[p_id_index].attributes = vec![MachineStdAttribute::Simp];

        validate_machine_std_mvp_theorem_index(&actual, &expected).unwrap();
    }

    #[test]
    fn rejects_missing_extra_generated_and_private_theorem_index_entries() {
        let package = TestPackage::new("bad_theorem_index_membership");
        let certs = mvp_certificate_bytes_with_logic_eq_rec_axiom();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let expected = generate_machine_std_mvp_theorem_index(&loaded).unwrap();
        let logic = loaded.module(&Name::from_dotted("Std.Logic")).unwrap();

        let mut missing = expected.clone();
        missing.entries.clear();
        refresh_theorem_index_hash(&mut missing);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&missing, &expected),
            Err(MachineStdTheoremIndexError::InvalidEntryMembership { .. })
        ));

        let generated = export_entry(logic, "Eq.refl");
        let mut extra_generated = expected.clone();
        let mut generated_entry = expected.entries[0].clone();
        generated_entry.global_ref.name = Name::from_dotted("Eq.refl");
        generated_entry.global_ref.decl_interface_hash = generated.decl_interface_hash;
        extra_generated.entries.push(generated_entry);
        refresh_theorem_index_hash(&mut extra_generated);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&extra_generated, &expected),
            Err(MachineStdTheoremIndexError::InvalidEntryMembership { .. })
        ));

        let mut private_like = expected.clone();
        let mut private_entry = expected.entries[0].clone();
        private_entry.global_ref.name = Name::from_dotted("private_helper");
        private_entry.global_ref.decl_interface_hash = test_hash(222);
        private_like.entries.push(private_entry);
        refresh_theorem_index_hash(&mut private_like);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&private_like, &expected),
            Err(MachineStdTheoremIndexError::InvalidEntryMembership { .. })
        ));
    }

    #[test]
    fn rejects_theorem_index_certificate_derived_field_mismatches() {
        let package = TestPackage::new("bad_theorem_index_fields");
        let certs = mvp_certificate_bytes_with_logic_axiom_theorem();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let expected = generate_machine_std_mvp_theorem_index(&loaded).unwrap();
        let p_id_index = expected
            .entries
            .iter()
            .position(|entry| entry.global_ref.name == Name::from_dotted("p_id"))
            .unwrap();

        let mut bad_hash = expected.clone();
        bad_hash.entries[p_id_index].statement_core_hash = test_hash(201);
        refresh_theorem_index_hash(&mut bad_hash);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&bad_hash, &expected),
            Err(MachineStdTheoremIndexError::StatementCoreHashMismatch { .. })
        ));

        let mut bad_constants = expected.clone();
        bad_constants.entries[p_id_index].constants.clear();
        refresh_theorem_index_hash(&mut bad_constants);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&bad_constants, &expected),
            Err(MachineStdTheoremIndexError::ConstantsMismatch { .. })
        ));

        let mut bad_axioms = expected.clone();
        bad_axioms.entries[p_id_index].axiom_dependencies.clear();
        refresh_theorem_index_hash(&mut bad_axioms);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&bad_axioms, &expected),
            Err(MachineStdTheoremIndexError::AxiomDependenciesMismatch { .. })
        ));

        let mut bad_size = expected.clone();
        bad_size.entries[p_id_index].proof_term_size = Some(1);
        refresh_theorem_index_hash(&mut bad_size);
        assert!(matches!(
            validate_machine_std_mvp_theorem_index(&bad_size, &expected),
            Err(MachineStdTheoremIndexError::NonNullProofTermSize { .. })
        ));
    }

    #[test]
    fn loads_valid_mvp_release_with_import_bundle_sidecar() {
        let package = TestPackage::new("valid_mvp_import_bundle_sidecar");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);

        let validated = load_machine_std_mvp_release_with_import_bundles_from_json(
            package.path(),
            &release_manifest_json(&release),
            &import_bundle_set_json(&import_bundles),
            &axiom_report_json(&axiom_report),
        )
        .unwrap();

        assert_eq!(
            validated.import_bundles.import_bundles_hash,
            import_bundles.import_bundles_hash
        );
        assert_eq!(
            validated.manifest.import_bundles_hash,
            import_bundles.import_bundles_hash
        );
    }

    #[test]
    fn builds_mvp_certificate_artifacts_from_source_package() {
        let package = TestPackage::new("source_package_build_artifacts");
        write_valid_mvp_source_package(package.path());

        let artifacts = build_mvp_source_package_artifacts(package.path()).unwrap();
        assert_eq!(
            artifacts
                .iter()
                .map(|artifact| artifact.module.as_dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        assert_eq!(
            artifacts
                .iter()
                .map(|artifact| artifact.source_relative_path.as_str())
                .collect::<Vec<_>>(),
            vec![
                "Std/Logic.npa",
                "Std/Nat.npa",
                "Std/List.npa",
                "Std/Algebra/Basic.npa"
            ]
        );
        assert_eq!(
            artifacts
                .iter()
                .map(|artifact| artifact.certificate_relative_path.as_str())
                .collect::<Vec<_>>(),
            vec![
                "Std/Logic.npcert",
                "Std/Nat.npcert",
                "Std/List.npcert",
                "Std/Algebra/Basic.npcert"
            ]
        );

        for artifact in &artifacts {
            let path =
                join_posix_relative_path(package.path(), &artifact.certificate_relative_path);
            let bytes = fs::read(path).unwrap();
            assert_eq!(bytes, artifact.certificate_bytes);
            let cert = decode_module_cert(&artifact.certificate_bytes).unwrap();
            assert_eq!(cert.header.module, artifact.module);
            assert_eq!(cert.hashes.export_hash, artifact.export_hash);
            assert_eq!(cert.hashes.certificate_hash, artifact.certificate_hash);
            assert_eq!(cert.hashes.axiom_report_hash, artifact.axiom_report_hash);
            for export in &cert.export_block {
                let name = cert.name_table[export.name].as_dotted();
                assert!(
                    !name.starts_with(&format!("{}.", artifact.module.as_dotted())),
                    "ExportEntry.name must be the declaration name, not a synthetic module-prefixed name"
                );
            }
        }

        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        assert_eq!(
            loaded
                .verification_order()
                .iter()
                .map(Name::as_dotted)
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
        let axiom_report = mvp_axiom_report_for(&loaded);
        for module in &axiom_report.modules {
            assert!(
                module
                    .module_axioms
                    .iter()
                    .all(|axiom| axiom.name == Name::from_dotted("Eq.rec")),
                "source package build may only report the exact Eq.rec exception"
            );
            assert!(
                module
                    .transitive_axioms
                    .iter()
                    .all(|axiom| axiom.name == Name::from_dotted("Eq.rec")),
                "source package build may only report the exact Eq.rec exception transitively"
            );
        }
    }

    #[test]
    fn std_library_reference_checker_accepts_mvp_release_certificates_source_free() {
        let package = TestPackage::new("reference_checker_std_mvp_source_free");
        write_valid_mvp_package(package.path());
        write_poison_human_std_source_and_debug_files(package.path());

        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let checked = reference_check_loaded_std_release(&loaded);

        assert_eq!(
            checked
                .iter()
                .map(|module| module.module().dotted())
                .collect::<Vec<_>>(),
            vec!["Std.Logic", "Std.Nat", "Std.List", "Std.Algebra.Basic"]
        );
    }

    #[test]
    fn std_polymorphic_universe_exports_are_release_and_index_hash_bound() {
        let package = TestPackage::new("std_polymorphic_universe_hash_binding");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let (release, import_bundles, theorem_index, _, _, _) =
            final_sidecar_artifacts_for_loaded(&loaded);

        let export_universe_params = |module: &MachineStdLoadedModule, name: &str| {
            let export = export_entry(module, name);
            export
                .universe_params
                .iter()
                .map(|param| module.verified_module.name_table()[*param].as_dotted())
                .collect::<Vec<_>>()
        };
        let assert_export_params = |module_name: &str, name: &str, expected: &[&str]| {
            let module = loaded.module(&Name::from_dotted(module_name)).unwrap();
            assert_eq!(
                export_universe_params(module, name),
                expected
                    .iter()
                    .map(|param| (*param).to_owned())
                    .collect::<Vec<_>>(),
                "{module_name}.{name}"
            );
        };

        assert_export_params("Std.Logic", "Eq", &["u"]);
        assert_export_params("Std.Logic", "Eq.refl", &["u"]);
        assert_export_params("Std.Logic", "Eq.rec", &["u", "v"]);
        assert_export_params("Std.Logic", "Eq.trans", &["u"]);
        assert_export_params("Std.Logic", "And", &[]);
        assert_export_params("Std.Logic", "Exists", &["u"]);
        assert_export_params("Std.List", "List", &["u"]);
        assert_export_params("Std.List", "List.rec", &["u", "v"]);
        assert_export_params("Std.List", "List.map", &["u", "v"]);
        assert_export_params("Std.List", "List.map_comp", &["u", "v", "w"]);
        assert_export_params("Std.Algebra.Basic", "Associative", &["u"]);
        assert_export_params("Std.Algebra.Basic", "IsMonoid", &["u"]);
        assert_export_params("Std.Algebra.Basic", "IsMonoid.assoc", &["u"]);
        assert_export_params("Std.Algebra.Basic", "identity_unique", &["u"]);

        for module in loaded.modules() {
            let artifact = module_artifact(&release, &module.module.as_dotted());
            assert_eq!(artifact.expected_export_hash, module.expected_export_hash);
            assert_eq!(
                artifact.expected_certificate_hash,
                module.expected_certificate_hash
            );
        }
        let all_bundle = import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_ALL_BUNDLE_ID)
            .unwrap();
        for certificate in &all_bundle.import_closure {
            let module = loaded.module(&certificate.module).unwrap();
            assert_eq!(
                certificate.expected_export_hash,
                module.expected_export_hash
            );
            assert_eq!(
                certificate.expected_certificate_hash,
                module.expected_certificate_hash
            );
        }

        for (module_name, theorem_name) in [
            ("Std.Logic", "Eq.rec"),
            ("Std.Logic", "Eq.trans"),
            ("Std.List", "List.map_comp"),
            ("Std.Algebra.Basic", "IsMonoid.assoc"),
            ("Std.Algebra.Basic", "identity_unique"),
        ] {
            let module = loaded.module(&Name::from_dotted(module_name)).unwrap();
            let export = export_entry(module, theorem_name);
            let index_entry = theorem_index_entry(&theorem_index, theorem_name);
            assert_eq!(index_entry.global_ref.module, module.module);
            assert_eq!(index_entry.global_ref.name, Name::from_dotted(theorem_name));
            assert_eq!(
                index_entry.global_ref.export_hash,
                module.expected_export_hash
            );
            assert_eq!(
                index_entry.global_ref.certificate_hash,
                module.expected_certificate_hash
            );
            assert_eq!(
                index_entry.global_ref.decl_interface_hash,
                export.decl_interface_hash
            );
            assert_eq!(
                index_entry.universe_params,
                export_universe_params(module, theorem_name)
            );
        }
    }

    #[test]
    fn std_library_reference_checker_rejects_custom_axiom_certificate() {
        let certs = mvp_certificate_bytes_with_logic_axiom("Std.Logic.synthetic_axiom");
        let policy = reference_std_checker_policy();
        let imports = ReferenceImportStore::default();

        let ReferenceCheckResult::Rejected(error) =
            check_certificate(&certs.logic, &imports, &policy)
        else {
            panic!("reference checker must reject custom standard-library axioms");
        };
        assert_eq!(error.kind, ReferenceCheckErrorKind::AxiomPolicy);
        assert_eq!(error.reason, Some(ReferenceCheckReason::ForbiddenAxiom));
    }

    #[test]
    fn std_library_reference_checker_ignores_broken_indexes_profiles_and_debug_inputs() {
        let package = TestPackage::new("reference_checker_std_ignores_sidecars");
        write_valid_mvp_package(package.path());
        let loaded_before = load_machine_std_mvp_certificates(package.path()).unwrap();
        let checked_before = reference_std_check_identity(&loaded_before);

        for relative_path in [
            STD_MACHINE_THEOREM_INDEX_JSON_PATH,
            STD_MACHINE_REWRITE_PROFILES_JSON_PATH,
            STD_MACHINE_SIMP_PROFILES_JSON_PATH,
            STD_MACHINE_PROMPT_METADATA_JSON_PATH,
        ] {
            write_text_artifact(
                package.path(),
                relative_path,
                "broken sidecar that is not checker input",
            );
        }
        write_poison_human_std_source_and_debug_files(package.path());

        let loaded_after = load_machine_std_mvp_certificates(package.path()).unwrap();
        let checked_after = reference_std_check_identity(&loaded_after);
        assert_eq!(checked_after, checked_before);
    }

    #[test]
    fn ai_search_candidate_hashes_do_not_change_after_std_reference_checker_recheck() {
        let package = TestPackage::new("reference_checker_std_ai_search_hashes");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );
        let validated = load_machine_std_mvp_release(package.path()).unwrap();

        let before = std_nat_add_zero_retrieval_candidate_hashes(&validated);
        reference_check_loaded_std_release(&validated.loaded);
        let after = std_nat_add_zero_retrieval_candidate_hashes(&validated);

        assert_eq!(after, before);
        assert!(
            !after.is_empty(),
            "retrieval must keep producing candidate hashes"
        );
    }

    #[test]
    fn ai_search_candidate_hashes_do_not_change_after_human_universe_inference() {
        let package = TestPackage::new("human_universe_inference_std_ai_search_hashes");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let (release, import_bundles, theorem_index, rewrite_profiles, simp_profiles, axiom_report) =
            final_sidecar_artifacts_for_loaded(&loaded);
        write_machine_std_release_sidecars(
            package.path(),
            &release,
            &import_bundles,
            &theorem_index,
            &rewrite_profiles,
            &simp_profiles,
            &axiom_report,
        );
        let validated = load_machine_std_mvp_release(package.path()).unwrap();
        let before = std_nat_add_zero_retrieval_candidate_hashes(&validated);

        let human_fixture = phase6_human_real_stdlib_fixture("human_universe_inference_handoff");
        assert_phase6_human_real_stdlib_certificate_verifies(
            &human_fixture,
            "Api.HumanUniverseReuse",
            "\
import Std.Logic
import Std.Nat
import Std.List

theorem eq_trans_inferred (A : Type) (x y z : A) (hxy : Eq.{1} A x y) (hyz : Eq.{1} A y z) : Eq.{1} A x z := by
  intro A
  intro x
  intro y
  intro z
  intro hxy
  intro hyz
  exact Eq.trans A x y z hxy hyz

theorem list_map_id_inferred (A : Type) (xs : List.{1} A) : Eq.{1} (List.{1} A) (List.map.{1,1} A A (fun (a : A) => a) xs) xs := by
  intro A
  intro xs
  exact List.map_id A xs",
        );
        let after = std_nat_add_zero_retrieval_candidate_hashes(&validated);

        assert_eq!(after, before);
        assert!(
            !after.is_empty(),
            "retrieval must keep producing candidate hashes"
        );
    }

    #[test]
    fn source_package_build_rejects_core_or_prelude_import_source_member() {
        for imported in ["Core", "Prelude"] {
            let package = TestPackage::new(&format!(
                "source_package_{}_import",
                imported.to_lowercase()
            ));
            write_valid_mvp_source_package(package.path());
            write_text_artifact(
                package.path(),
                STD_LOGIC_SOURCE_PATH,
                &format!("import {imported}\n"),
            );

            let err = build_mvp_source_package_artifacts(package.path()).unwrap_err();
            assert!(matches!(
                err,
                MvpSourcePackageBuildError::ForbiddenSourceImport {
                    ref module,
                    ref imported_module,
                } if *module == Name::from_dotted("Std.Logic")
                    && *imported_module == Name::from_dotted(imported)
            ));
        }
    }

    #[test]
    fn source_package_build_fails_on_import_hash_mismatch() {
        let certs = mvp_certificate_bytes();
        let mut session = VerifierSession::new();
        let policy = high_trust_policy_allowing_std_mvp_axioms();
        let logic = verify_module_cert(&certs.logic, &mut session, &policy).unwrap();
        let mut nat = decode_module_cert(&certs.nat).unwrap();

        nat.imports[0].export_hash = test_hash(201);
        let err = validate_source_build_import_entries(
            &Name::from_dotted("Std.Nat"),
            &nat.imports,
            std::slice::from_ref(&logic),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MvpSourcePackageBuildError::ImportExportHashMismatch {
                ref owner,
                ref imported_module,
            } if *owner == Name::from_dotted("Std.Nat")
                && *imported_module == Name::from_dotted("Std.Logic")
        ));

        nat.imports[0].export_hash = logic.export_hash();
        nat.imports[0].certificate_hash = Some(test_hash(202));
        let err = validate_source_build_import_entries(
            &Name::from_dotted("Std.Nat"),
            &nat.imports,
            std::slice::from_ref(&logic),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MvpSourcePackageBuildError::ImportCertificateHashMismatch {
                ref owner,
                ref imported_module,
            } if *owner == Name::from_dotted("Std.Nat")
                && *imported_module == Name::from_dotted("Std.Logic")
        ));
    }

    #[test]
    fn rejects_missing_extra_duplicate_or_reordered_import_bundle_ids() {
        let package = TestPackage::new("bad_import_bundle_membership");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut missing = expected.clone();
        missing.bundles.pop();
        missing.import_bundles_hash = machine_std_import_bundle_set_hash(&missing).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&missing, &expected),
            Err(MachineStdImportBundleError::InvalidBundleMembership { .. })
        ));

        let mut extra = expected.clone();
        let mut extra_bundle = extra.bundles[0].clone();
        extra_bundle.bundle_id = "std.extra.mvp".to_owned();
        extra.bundles.push(extra_bundle);
        extra.import_bundles_hash = machine_std_import_bundle_set_hash(&extra).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&extra, &expected),
            Err(MachineStdImportBundleError::InvalidBundleMembership { .. })
        ));

        let mut duplicate = expected.clone();
        duplicate.bundles.push(duplicate.bundles[0].clone());
        duplicate.import_bundles_hash = machine_std_import_bundle_set_hash(&duplicate).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&duplicate, &expected),
            Err(MachineStdImportBundleError::DuplicateBundle { .. })
        ));

        let mut reordered = expected.clone();
        reordered.bundles.swap(0, 1);
        reordered.import_bundles_hash = machine_std_import_bundle_set_hash(&reordered).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&reordered, &expected),
            Err(MachineStdImportBundleError::NonCanonicalBundleOrder { .. })
        ));
    }

    #[test]
    fn rejects_noncanonical_import_bundle_roots_and_closure_order() {
        let package = TestPackage::new("bad_import_bundle_order");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut bad_roots = expected.clone();
        let list = bad_roots
            .bundles
            .iter_mut()
            .find(|bundle| bundle.bundle_id == STD_LIST_BUNDLE_ID)
            .unwrap();
        list.root_imports.swap(0, 1);
        bad_roots.import_bundles_hash = machine_std_import_bundle_set_hash(&bad_roots).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&bad_roots, &expected),
            Err(MachineStdImportBundleError::NonCanonicalRootImportOrder { .. })
        ));

        let mut bad_closure = expected.clone();
        let list = bad_closure
            .bundles
            .iter_mut()
            .find(|bundle| bundle.bundle_id == STD_LIST_BUNDLE_ID)
            .unwrap();
        list.import_closure.swap(0, 1);
        bad_closure.import_bundles_hash = machine_std_import_bundle_set_hash(&bad_closure).unwrap();
        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&bad_closure, &expected),
            Err(MachineStdImportBundleError::NonCanonicalImportClosureOrder { .. })
        ));
    }

    #[test]
    fn rejects_import_bundle_certificate_bytes_mismatch() {
        let package = TestPackage::new("bad_import_bundle_certificate_bytes");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut actual = expected.clone();
        actual.bundles[0].import_closure[0]
            .certificate_bytes
            .push(0xff);
        actual.import_bundles_hash = machine_std_import_bundle_set_hash(&actual).unwrap();

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&actual, &expected),
            Err(MachineStdImportBundleError::CertificateBytesHashMismatch { .. })
        ));
    }

    #[test]
    fn rejects_unexpected_mvp_import_bundle_allow_axioms() {
        let package = TestPackage::new("bad_import_bundle_allow_axioms");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut actual = expected.clone();
        let key = actual.bundles[0].root_imports[0].clone();
        actual.bundles[0]
            .allow_axioms
            .push(MachineAxiomRefWire::Imported {
                module: key.module,
                name: Name::from_dotted("Std.Logic.synthetic_axiom"),
                export_hash: key.export_hash,
                decl_interface_hash: test_hash(99),
            });
        actual.import_bundles_hash = machine_std_import_bundle_set_hash(&actual).unwrap();

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&actual, &expected),
            Err(MachineStdImportBundleError::AllowAxiomsMismatch { .. })
        ));
    }

    #[test]
    fn parses_imported_allow_axioms_before_rejecting_unexpected_bundle_axioms() {
        let package = TestPackage::new("import_bundle_allow_axioms_json");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut actual = expected.clone();
        let key = actual.bundles[0].root_imports[0].clone();
        actual.bundles[0]
            .allow_axioms
            .push(MachineAxiomRefWire::Imported {
                module: key.module,
                name: Name::from_dotted("Std.Logic.synthetic_axiom"),
                export_hash: key.export_hash,
                decl_interface_hash: test_hash(100),
            });
        actual.import_bundles_hash = machine_std_import_bundle_set_hash(&actual).unwrap();

        let parsed = parse_machine_std_import_bundle_set_json(&import_bundle_set_json(&actual))
            .expect("imported allow_axioms variant should parse");

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&parsed, &expected),
            Err(MachineStdImportBundleError::AllowAxiomsMismatch { .. })
        ));
    }

    #[test]
    fn emits_eq_family_when_std_logic_exports_eq_rec_as_axiom() {
        let package = TestPackage::new("import_bundle_eq_rec_axiom_family");
        let certs = mvp_certificate_bytes_with_logic_eq_rec_axiom();
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let logic = loaded.module(&Name::from_dotted("Std.Logic")).unwrap();
        assert!(logic.verified_module.export_block().iter().any(|entry| {
            entry.kind == ExportKind::Axiom
                && logic
                    .verified_module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|name| *name == Name::from_dotted("Eq.rec"))
        }));

        let bundle_set = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();
        let logic_bundle = bundle_set
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_LOGIC_BUNDLE_ID)
            .unwrap();
        let family = logic_bundle
            .recommended_tactic_options
            .eq_family
            .as_ref()
            .expect("Eq.rec axiom export should still produce an Eq family recipe");

        assert_eq!(family.eq_name, Name::from_dotted("Eq"));
        assert_eq!(family.refl_name, Name::from_dotted("Eq.refl"));
        assert_eq!(family.rec_name, Name::from_dotted("Eq.rec"));
        assert_eq!(
            logic_bundle.allow_axioms,
            vec![MachineAxiomRefWire::Imported {
                module: logic.module.clone(),
                name: family.rec_name.clone(),
                export_hash: logic.expected_export_hash,
                decl_interface_hash: family.rec_interface_hash,
            }]
        );
    }

    #[test]
    fn rejects_invalid_import_bundle_recipe_mapping() {
        let package = TestPackage::new("bad_import_bundle_recipe");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let expected = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();

        let mut actual = expected.clone();
        actual.bundles[0].recommended_tactic_options.recipe_id = "std.bad-recipe".to_owned();
        actual.import_bundles_hash = machine_std_import_bundle_set_hash(&actual).unwrap();

        assert!(matches!(
            validate_machine_std_mvp_import_bundle_set(&actual, &expected),
            Err(MachineStdImportBundleError::InvalidRecipeIdMapping { .. })
        ));
    }

    #[test]
    fn rejects_manifest_bound_import_bundle_hash_mismatch_as_library_release() {
        let package = TestPackage::new("manifest_bound_import_bundle_hash_mismatch");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let mut release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);
        release.import_bundles_hash = test_hash(55);

        let err = load_machine_std_mvp_release_with_import_bundles_from_json(
            package.path(),
            &release_manifest_json(&release),
            &import_bundle_set_json(&import_bundles),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::SidecarHashMismatch {
                    field: "import_bundles_hash",
                    ..
                }
            )
        ));
    }

    #[test]
    fn rejects_stale_import_bundle_self_hash_before_manifest_comparison() {
        let package = TestPackage::new("stale_import_bundle_self_hash");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let mut import_bundles = generate_machine_std_mvp_import_bundle_set(&loaded).unwrap();
        import_bundles.import_bundles_hash = test_hash(56);
        let axiom_report = mvp_axiom_report_for(&loaded);
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);

        let err = load_machine_std_mvp_release_with_import_bundles_from_json(
            package.path(),
            &release_manifest_json(&release),
            &import_bundle_set_json(&import_bundles),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();

        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdImportBundle(
                MachineStdImportBundleError::ImportBundlesHashMismatch { .. }
            )
        ));
    }

    #[test]
    fn rejects_mvp_release_scalar_mismatch_as_library_release() {
        let package = TestPackage::new("release_scalar_mismatch");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let mut release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);
        release.protocol_version = "npa.stdlib-machine.bad".to_owned();

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_manifest_json(&release),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::ScalarMismatch {
                    field: "protocol_version",
                    ..
                }
            )
        ));
    }

    #[test]
    fn rejects_std_library_release_hash_field_as_unknown_shape() {
        let package = TestPackage::new("release_hash_unknown");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let release = release_manifest_for(&loaded, test_hash(9));
        let release_json = release_manifest_json(&release).replacen(
            "{\"protocol_version\"",
            &format!(
                "{{\"std_library_release_hash\":\"{}\",\"protocol_version\"",
                format_hash_string(&test_hash(77))
            ),
            1,
        );

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_json,
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdArtifactShape(
                MachineStdArtifactShapeError {
                    reason: MachineStdArtifactShapeErrorReason::UnknownField { field },
                    ..
                }
            ) if field == "std_library_release_hash"
        ));
    }

    #[test]
    fn rejects_non_empty_mvp_axiom_report_lists() {
        let package = TestPackage::new("non_empty_axiom_report");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let mut axiom_report = mvp_axiom_report_for(&loaded);
        let first = axiom_report
            .modules
            .first_mut()
            .expect("fixture should include at least one module");
        first.module_axioms.push(MachineStdAxiomRef {
            module: first.module.clone(),
            name: Name::from_dotted("Std.Nat.synthetic_axiom"),
            export_hash: first.export_hash,
            decl_interface_hash: test_hash(88),
        });
        first.module_axioms.sort_by(|lhs, rhs| {
            machine_std_axiom_ref_canonical_bytes(lhs)
                .unwrap()
                .cmp(&machine_std_axiom_ref_canonical_bytes(rhs).unwrap())
        });
        axiom_report.axiom_report_hash = machine_std_axiom_report_hash(&axiom_report).unwrap();
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_manifest_json(&release),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::NonEmptyMvpAxiomList {
                    field: "module_axioms",
                    ..
                }
            )
        ));
    }

    #[test]
    fn rejects_certificate_axioms_as_axiom_policy() {
        let package = TestPackage::new("certificate_axiom_policy");
        let certs = mvp_certificate_bytes_with_logic_axiom("Std.Logic.synthetic_axiom");
        write_mvp_package(package.path(), &certs);
        let loaded =
            load_machine_std_mvp_certificates_for_manifest_validation(package.path()).unwrap();
        let mut axiom_report = empty_axiom_report_for(&loaded);
        axiom_report.axiom_report_hash = machine_std_axiom_report_hash(&axiom_report).unwrap();
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_manifest_json(&release),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::ModuleAxiomsMismatch { .. }
            )
        ));
    }

    #[test]
    fn mvp_certificate_loader_rejects_custom_axioms() {
        let package = TestPackage::new("custom_axiom_loader_policy");
        let certs = mvp_certificate_bytes_with_logic_axiom("Std.Logic.synthetic_axiom");
        write_mvp_package(package.path(), &certs);

        let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::VerifyFailed {
                module,
                source,
            } if module == Name::from_dotted("Std.Logic")
                && matches!(*source, CertError::ForbiddenAxiom { ref axiom }
                    if *axiom == Name::from_dotted("Std.Logic.synthetic_axiom"))
        ));
    }

    #[test]
    fn mvp_certificate_loader_rejects_nonstandard_eq_rec_exception() {
        let package = TestPackage::new("nonstandard_eq_rec_loader_policy");
        let certs = mvp_certificate_bytes_with_nonstandard_logic_eq_rec_axiom();
        write_mvp_package(package.path(), &certs);

        let err = load_machine_std_mvp_certificates(package.path()).unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseLoaderError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::NonEmptyMvpAxiomList {
                    ref module,
                    field: "module_axioms",
                }
            ) if *module == Name::from_dotted("Std.Logic")
        ));
    }

    #[test]
    fn rejects_stale_axiom_report_self_hash_before_manifest_comparison() {
        let package = TestPackage::new("stale_axiom_report_self_hash");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let mut axiom_report = mvp_axiom_report_for(&loaded);
        axiom_report.axiom_report_hash = test_hash(44);
        let release = release_manifest_for(&loaded, axiom_report.axiom_report_hash);

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_manifest_json(&release),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdAxiomPolicy(
                MachineStdAxiomPolicyError::AxiomReportHashMismatch { .. }
            )
        ));
    }

    #[test]
    fn rejects_manifest_bound_axiom_report_hash_mismatch_as_library_release() {
        let package = TestPackage::new("manifest_bound_axiom_hash_mismatch");
        write_valid_mvp_package(package.path());
        let loaded = load_machine_std_mvp_certificates(package.path()).unwrap();
        let axiom_report = mvp_axiom_report_for(&loaded);
        let release = release_manifest_for(&loaded, test_hash(45));

        let err = load_machine_std_mvp_release_from_json(
            package.path(),
            &release_manifest_json(&release),
            &axiom_report_json(&axiom_report),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            MachineStdReleaseArtifactError::InvalidStdLibraryRelease(
                MachineStdLibraryReleaseError::SidecarHashMismatch {
                    field: "axiom_report_hash",
                    ..
                }
            )
        ));
    }

    struct MvpCertificateBytes {
        logic: Vec<u8>,
        nat: Vec<u8>,
        list: Vec<u8>,
        algebra_basic: Vec<u8>,
    }

    fn reference_std_checker_policy() -> ReferenceCheckerPolicy {
        ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            deny_sorry: true,
            deny_custom_axioms: true,
            ..ReferenceCheckerPolicy::default()
        }
    }

    fn reference_module_name(module: &Name) -> ReferenceModuleName {
        ReferenceModuleName::from_dotted(&module.as_dotted()).unwrap()
    }

    fn reference_check_loaded_std_release(
        loaded: &MachineStdLoadedRelease,
    ) -> Vec<ReferenceCheckedModule> {
        let policy = reference_std_checker_policy();
        let mut checked_by_name = BTreeMap::<Name, ReferenceCheckedModule>::new();
        let mut checked_modules = Vec::new();

        for module_name in loaded.verification_order() {
            let module = loaded.module(module_name).unwrap();
            let imports =
                ReferenceImportStore::from_checked_modules(module.imports.iter().map(|import| {
                    checked_by_name
                        .get(&import.module)
                        .unwrap_or_else(|| {
                            panic!(
                                "reference checker import {} must be checked before {}",
                                import.module.as_dotted(),
                                module.module.as_dotted()
                            )
                        })
                        .clone()
                }))
                .unwrap();
            let checked = match check_certificate(&module.certificate_bytes, &imports, &policy) {
                ReferenceCheckResult::Checked(checked) => checked,
                ReferenceCheckResult::Rejected(error) => panic!(
                    "reference checker rejected {}: {:?}",
                    module.module.as_dotted(),
                    error
                ),
            };

            assert_eq!(checked.module(), &reference_module_name(&module.module));
            assert_eq!(checked.export_hash(), &module.expected_export_hash);
            assert_eq!(
                checked.certificate_hash(),
                &module.expected_certificate_hash
            );
            assert_eq!(checked.axiom_report_hash(), &module.axiom_report_hash);

            checked_by_name.insert(module.module.clone(), checked.clone());
            checked_modules.push(checked);
        }

        checked_modules
    }

    fn reference_std_check_identity(
        loaded: &MachineStdLoadedRelease,
    ) -> Vec<(String, Hash, Hash, Hash)> {
        reference_check_loaded_std_release(loaded)
            .into_iter()
            .map(|module| {
                (
                    module.module().dotted(),
                    *module.export_hash(),
                    *module.certificate_hash(),
                    *module.axiom_report_hash(),
                )
            })
            .collect()
    }

    fn std_nat_add_zero_retrieval_candidate_hashes(
        validated: &MachineStdValidatedRelease,
    ) -> Vec<Hash> {
        let nat_bundle = validated
            .import_bundles
            .bundles
            .iter()
            .find(|bundle| bundle.bundle_id == STD_NAT_BUNDLE_ID)
            .unwrap();
        let theorem_type = "Eq.{1} Nat (Nat.add Nat.zero Nat.zero) Nat.zero";
        let search_session = crate::create_machine_session(
            &session_create_json_for_bundle_with_theorem_type(nat_bundle, theorem_type),
        )
        .unwrap()
        .session;
        let filters = r#"{"exclude_axioms":false,"allowed_modules":["Std.Nat"]}"#;
        let search = search_machine_theorems_for_goal(
            &m8_search_json(&search_session, filters),
            &search_session,
        )
        .unwrap();
        let MachineApiResponseEnvelope::Ok(search_ok) = search else {
            panic!("standard-library theorem retrieval should succeed");
        };
        let nat_add_zero = search_ok
            .endpoint_fields
            .results
            .iter()
            .find(|result| result.global_ref.name == Name::from_dotted("Nat.add_zero"))
            .expect("Nat.add_zero must stay available to retrieval");

        nat_add_zero
            .suggested_candidates
            .iter()
            .map(|candidate| candidate.candidate_hash)
            .collect()
    }

    #[derive(Debug)]
    struct BuiltMvpSourceArtifact {
        module: Name,
        source_relative_path: String,
        certificate_relative_path: String,
        certificate_bytes: Vec<u8>,
        export_hash: Hash,
        certificate_hash: Hash,
        axiom_report_hash: Hash,
    }

    #[allow(dead_code)]
    #[derive(Debug)]
    enum MvpSourcePackageBuildError {
        MissingSource {
            module: Name,
            path: PathBuf,
        },
        ReadSource {
            module: Name,
            path: PathBuf,
        },
        InvalidSource {
            module: Name,
        },
        ForbiddenSourceImport {
            module: Name,
            imported_module: Name,
        },
        SourceImportMismatch {
            module: Name,
            expected: Vec<Name>,
            actual: Vec<Name>,
        },
        MissingCompiledImport {
            module: Name,
            imported_module: Name,
        },
        CertificateBuild {
            module: Name,
        },
        CertificateEncoding {
            module: Name,
        },
        ImportEntryCountMismatch {
            owner: Name,
        },
        ImportExportHashMismatch {
            owner: Name,
            imported_module: Name,
        },
        ImportCertificateHashMismatch {
            owner: Name,
            imported_module: Name,
        },
        ForbiddenCertificateImport {
            owner: Name,
            imported_module: Name,
        },
        Verify {
            module: Name,
        },
        LoadBuiltArtifacts,
    }

    fn build_mvp_source_package_artifacts(
        root: &Path,
    ) -> Result<Vec<BuiltMvpSourceArtifact>, MvpSourcePackageBuildError> {
        let mut session = VerifierSession::new();
        let policy = high_trust_policy_allowing_std_mvp_axioms();
        let mut verified_by_module = BTreeMap::<Name, VerifiedModule>::new();

        for (source_index, entry) in machine_std_mvp_source_package_layout()
            .into_iter()
            .enumerate()
        {
            let source = read_mvp_source_member(root, &entry)?;
            validate_mvp_source_member(source_index, &entry, &source)?;
            let imports = compiled_source_imports(&entry.module, &verified_by_module)?;
            let core = mvp_core_module_for_source(&entry.module);
            let cert = build_module_cert(core, &imports).map_err(|_| {
                MvpSourcePackageBuildError::CertificateBuild {
                    module: entry.module.clone(),
                }
            })?;
            validate_source_build_import_entries(&entry.module, &cert.imports, &imports)?;
            let bytes = encode_module_cert(&cert).map_err(|_| {
                MvpSourcePackageBuildError::CertificateEncoding {
                    module: entry.module.clone(),
                }
            })?;
            let verified = verify_module_cert(&bytes, &mut session, &policy).map_err(|_| {
                MvpSourcePackageBuildError::Verify {
                    module: entry.module.clone(),
                }
            })?;
            write_cert(root, &entry.certificate_relative_path, &bytes);
            verified_by_module.insert(entry.module, verified);
        }

        let loaded = load_machine_std_mvp_certificates(root)
            .map_err(|_| MvpSourcePackageBuildError::LoadBuiltArtifacts)?;
        validate_loaded_mvp_axiom_policy(&loaded)
            .map_err(|_| MvpSourcePackageBuildError::LoadBuiltArtifacts)?;
        machine_std_mvp_source_package_layout()
            .into_iter()
            .map(|entry| {
                let loaded_module = loaded
                    .module(&entry.module)
                    .expect("loaded source-built package should contain every MVP module");
                Ok(BuiltMvpSourceArtifact {
                    module: entry.module,
                    source_relative_path: entry.source_relative_path,
                    certificate_relative_path: entry.certificate_relative_path,
                    certificate_bytes: loaded_module.certificate_bytes.clone(),
                    export_hash: loaded_module.expected_export_hash,
                    certificate_hash: loaded_module.expected_certificate_hash,
                    axiom_report_hash: loaded_module.axiom_report_hash,
                })
            })
            .collect()
    }

    fn read_mvp_source_member(
        root: &Path,
        entry: &MachineStdSourcePackageEntry,
    ) -> Result<String, MvpSourcePackageBuildError> {
        let path = join_posix_relative_path(root, &entry.source_relative_path);
        fs::read_to_string(&path).map_err(|source| {
            if source.kind() == io::ErrorKind::NotFound {
                MvpSourcePackageBuildError::MissingSource {
                    module: entry.module.clone(),
                    path,
                }
            } else {
                MvpSourcePackageBuildError::ReadSource {
                    module: entry.module.clone(),
                    path,
                }
            }
        })
    }

    fn validate_mvp_source_member(
        source_index: usize,
        entry: &MachineStdSourcePackageEntry,
        source: &str,
    ) -> Result<(), MvpSourcePackageBuildError> {
        let module = parse_human_module(FileId(source_index as u32), source).map_err(|_| {
            MvpSourcePackageBuildError::InvalidSource {
                module: entry.module.clone(),
            }
        })?;
        let actual = module
            .items
            .iter()
            .filter_map(|item| match item {
                HumanItem::Import { module, .. } => Some(Name::from_dotted(module.as_dotted())),
                _ => None,
            })
            .collect::<Vec<_>>();
        for imported_module in &actual {
            if matches!(imported_module.as_dotted().as_str(), "Core" | "Prelude") {
                return Err(MvpSourcePackageBuildError::ForbiddenSourceImport {
                    module: entry.module.clone(),
                    imported_module: imported_module.clone(),
                });
            }
        }
        let expected = expected_mvp_source_imports(&entry.module);
        if actual != expected {
            return Err(MvpSourcePackageBuildError::SourceImportMismatch {
                module: entry.module.clone(),
                expected,
                actual,
            });
        }
        Ok(())
    }

    fn expected_mvp_source_imports(module: &Name) -> Vec<Name> {
        match module.as_dotted().as_str() {
            "Std.Logic" => Vec::new(),
            "Std.Nat" => vec![Name::from_dotted("Std.Logic")],
            "Std.List" => vec![Name::from_dotted("Std.Logic"), Name::from_dotted("Std.Nat")],
            "Std.Algebra.Basic" => vec![Name::from_dotted("Std.Logic")],
            _ => panic!("unexpected standard source module {}", module.as_dotted()),
        }
    }

    fn compiled_source_imports(
        module: &Name,
        verified_by_module: &BTreeMap<Name, VerifiedModule>,
    ) -> Result<Vec<VerifiedModule>, MvpSourcePackageBuildError> {
        expected_mvp_source_imports(module)
            .into_iter()
            .map(|imported_module| {
                verified_by_module
                    .get(&imported_module)
                    .cloned()
                    .ok_or_else(|| MvpSourcePackageBuildError::MissingCompiledImport {
                        module: module.clone(),
                        imported_module,
                    })
            })
            .collect()
    }

    fn mvp_core_module_for_source(module: &Name) -> CoreModule {
        match module.as_dotted().as_str() {
            "Std.Logic" => logic_eq_family_module(),
            "Std.Nat" => nat_basic_module(),
            "Std.List" => list_append_module(),
            "Std.Algebra.Basic" => algebra_basic_module(),
            _ => panic!("unexpected standard source module {}", module.as_dotted()),
        }
    }

    fn validate_source_build_import_entries(
        owner: &Name,
        imports: &[ImportEntry],
        expected_imports: &[VerifiedModule],
    ) -> Result<(), MvpSourcePackageBuildError> {
        if imports.len() != expected_imports.len() {
            return Err(MvpSourcePackageBuildError::ImportEntryCountMismatch {
                owner: owner.clone(),
            });
        }
        for (import, expected) in imports.iter().zip(expected_imports) {
            if matches!(import.module.as_dotted().as_str(), "Core" | "Prelude") {
                return Err(MvpSourcePackageBuildError::ForbiddenCertificateImport {
                    owner: owner.clone(),
                    imported_module: import.module.clone(),
                });
            }
            if import.module != *expected.module() || import.export_hash != expected.export_hash() {
                return Err(MvpSourcePackageBuildError::ImportExportHashMismatch {
                    owner: owner.clone(),
                    imported_module: import.module.clone(),
                });
            }
            if import.certificate_hash != Some(expected.certificate_hash()) {
                return Err(MvpSourcePackageBuildError::ImportCertificateHashMismatch {
                    owner: owner.clone(),
                    imported_module: import.module.clone(),
                });
            }
        }
        Ok(())
    }

    fn mvp_certificate_bytes() -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let policy = high_trust_policy_allowing_std_mvp_axioms();

        let logic_cert = build_module_cert(logic_eq_family_module(), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert =
            build_module_cert(nat_basic_module(), std::slice::from_ref(&logic_verified)).unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            list_append_module(),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert = build_module_cert(algebra_basic_module(), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn mvp_certificate_bytes_with_logic_axiom(axiom_name: &str) -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .insert(Name::from_dotted(axiom_name));

        let logic_cert = build_module_cert(logic_axiom_module(axiom_name), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert =
            build_module_cert(nat_family_module(), std::slice::from_ref(&logic_verified)).unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            empty_module("Std.List"),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert =
            build_module_cert(empty_module("Std.Algebra.Basic"), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn mvp_certificate_bytes_with_logic_axiom_theorem() -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy.allowlisted_axioms.insert(Name::from_dotted("P"));

        let logic_cert = build_module_cert(logic_axiom_theorem_module(), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert =
            build_module_cert(nat_family_module(), std::slice::from_ref(&logic_verified)).unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            empty_module("Std.List"),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert =
            build_module_cert(empty_module("Std.Algebra.Basic"), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn mvp_certificate_bytes_with_logic_eq_rec_axiom() -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .insert(Name::from_dotted("Eq.rec"));

        let logic_cert = build_module_cert(logic_eq_rec_axiom_module(), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert =
            build_module_cert(nat_family_module(), std::slice::from_ref(&logic_verified)).unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            empty_module("Std.List"),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert =
            build_module_cert(empty_module("Std.Algebra.Basic"), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn mvp_certificate_bytes_with_nonstandard_logic_eq_rec_axiom() -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .insert(Name::from_dotted("Eq.rec"));

        let logic_cert = build_module_cert(logic_nonstandard_eq_rec_axiom_module(), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert = build_module_cert(
            empty_module("Std.Nat"),
            std::slice::from_ref(&logic_verified),
        )
        .unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            empty_module("Std.List"),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert =
            build_module_cert(empty_module("Std.Algebra.Basic"), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn mvp_certificate_bytes_with_m5_profiles() -> MvpCertificateBytes {
        let mut session = VerifierSession::new();
        let mut policy = AxiomPolicy::high_trust();
        policy
            .allowlisted_axioms
            .insert(Name::from_dotted("Eq.rec"));

        let logic_cert = build_module_cert(logic_eq_family_module(), &[]).unwrap();
        let logic = encode_module_cert(&logic_cert).unwrap();
        let logic_verified = verify_module_cert(&logic, &mut session, &policy).unwrap();

        let nat_cert = build_module_cert(
            nat_m5_profile_module(),
            std::slice::from_ref(&logic_verified),
        )
        .unwrap();
        let nat = encode_module_cert(&nat_cert).unwrap();
        let nat_verified = verify_module_cert(&nat, &mut session, &policy).unwrap();

        let list_cert = build_module_cert(
            list_m5_profile_module(),
            &[logic_verified.clone(), nat_verified.clone()],
        )
        .unwrap();
        let list = encode_module_cert(&list_cert).unwrap();
        verify_module_cert(&list, &mut session, &policy).unwrap();

        let algebra_cert = build_module_cert(algebra_basic_module(), &[logic_verified]).unwrap();
        let algebra_basic = encode_module_cert(&algebra_cert).unwrap();

        MvpCertificateBytes {
            logic,
            nat,
            list,
            algebra_basic,
        }
    }

    fn write_valid_mvp_package(root: &Path) {
        let certs = mvp_certificate_bytes();
        write_mvp_package(root, &certs);
    }

    fn write_valid_mvp_source_package(root: &Path) {
        for entry in machine_std_mvp_source_package_layout() {
            write_text_artifact(
                root,
                &entry.source_relative_path,
                valid_mvp_source_text(&entry.module),
            );
        }
    }

    fn valid_mvp_source_text(module: &Name) -> &'static str {
        match module.as_dotted().as_str() {
            "Std.Logic" => {
                "-- npa std source package v1
-- module: Std.Logic
-- declarations: Eq, Eq.rec, Eq.symm, Eq.trans, Eq.subst, Eq.congrArg, True, False, Not, And, Or, Iff, Exists
"
            }
            "Std.Nat" => {
                "import Std.Logic
-- npa std source package v1
-- module: Std.Nat
-- declarations: Nat, Nat.one, Nat.pred, Nat.add, Nat.mul, add/mul/pred basic theorems
"
            }
            "Std.List" => {
                "import Std.Logic
import Std.Nat
-- npa std source package v1
-- module: Std.List
-- declarations: List, append, length, map, foldr, and basic theorems
"
            }
            "Std.Algebra.Basic" => {
                "import Std.Logic
-- npa std source package v1
-- module: Std.Algebra.Basic
-- declarations: unbundled algebraic properties, IsSemigroup, IsMonoid, IsCommMonoid
"
            }
            _ => panic!("unexpected standard source module {}", module.as_dotted()),
        }
    }

    fn write_mvp_package(root: &Path, certs: &MvpCertificateBytes) {
        write_cert(root, STD_LOGIC_PATH, &certs.logic);
        write_cert(root, STD_NAT_PATH, &certs.nat);
        write_cert(root, STD_LIST_PATH, &certs.list);
        write_cert(root, STD_ALGEBRA_BASIC_PATH, &certs.algebra_basic);
    }

    fn write_cert(root: &Path, relative_path: &str, bytes: &[u8]) {
        let path = join_posix_relative_path(root, relative_path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }

    fn write_text_artifact(root: &Path, relative_path: &str, contents: &str) {
        let path = join_posix_relative_path(root, relative_path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn write_poison_human_std_source_and_debug_files(root: &Path) {
        for entry in machine_std_mvp_source_package_layout() {
            write_text_artifact(
                root,
                &entry.source_relative_path,
                "not valid Human NPA source and not a Machine input",
            );
        }
        for relative_path in [
            "Std/Logic.index.json",
            "Std/Logic.axioms.json",
            "Std/Logic.graph.json",
            "Std/Logic.attributes.json",
            "Std/Nat.index.json",
            "Std/Nat.axioms.json",
            "Std/Nat.graph.json",
            "Std/Nat.attributes.json",
            "Std/List.index.json",
            "Std/List.axioms.json",
            "Std/List.graph.json",
            "Std/List.attributes.json",
            "Std/Algebra/Basic.index.json",
            "Std/Algebra/Basic.axioms.json",
            "Std/Algebra/Basic.graph.json",
            "Std/Algebra/Basic.attributes.json",
        ] {
            write_text_artifact(root, relative_path, "{not valid json");
        }
        write_text_artifact(
            root,
            "Std/Nat/Basic.npa",
            "legacy fixture source must not create a release module",
        );
        write_text_artifact(
            root,
            "Std/Logic/Eq.npa",
            "legacy fixture source must not create a release module",
        );
    }

    fn empty_module(name: &str) -> CoreModule {
        CoreModule {
            name: Name::from_dotted(name),
            declarations: Vec::new(),
        }
    }

    fn logic_axiom_module(axiom_name: &str) -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Logic"),
            declarations: vec![Decl::Axiom {
                name: axiom_name.to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            }],
        }
    }

    fn logic_axiom_theorem_module() -> CoreModule {
        let p = Expr::konst("P", vec![]);
        CoreModule {
            name: Name::from_dotted("Std.Logic"),
            declarations: vec![
                Decl::Axiom {
                    name: "P".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                },
                Decl::Theorem {
                    name: "p_id".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::pi("h", p.clone(), p.clone()),
                    proof: Expr::lam("h", p, Expr::bvar(0)),
                },
            ],
        }
    }

    fn logic_eq_rec_axiom_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Logic"),
            declarations: vec![logic_eq_inductive_decl(), logic_eq_rec_axiom_decl()],
        }
    }

    fn logic_eq_family_module() -> CoreModule {
        let mut declarations = vec![
            logic_eq_inductive_decl(),
            logic_eq_rec_axiom_decl(),
            eq_symm_theorem(),
            eq_trans_theorem(),
            eq_subst_theorem(),
            eq_congr_arg_theorem(),
        ];
        declarations.extend(logic_connective_declarations());
        CoreModule {
            name: Name::from_dotted("Std.Logic"),
            declarations,
        }
    }

    fn logic_eq_rec_axiom_decl() -> Decl {
        Decl::Axiom {
            name: "Eq.rec".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: eq_rec_type(Level::param("u"), Level::param("v")),
        }
    }

    fn logic_nonstandard_eq_rec_axiom_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Logic"),
            declarations: vec![
                logic_eq_inductive_decl(),
                Decl::Axiom {
                    name: "Eq.rec".to_owned(),
                    universe_params: vec!["u".to_owned(), "v".to_owned()],
                    ty: Expr::sort(Level::zero()),
                },
            ],
        }
    }

    fn logic_eq_inductive_decl() -> Decl {
        logic_eq_inductive_decl_with_data(eq_inductive())
    }

    fn logic_eq_inductive_decl_with_data(data: npa_kernel::InductiveDecl) -> Decl {
        Decl::Inductive {
            name: "Eq".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(Level::param("u")),
                Expr::pi(
                    "lhs",
                    Expr::bvar(0),
                    Expr::pi("rhs", Expr::bvar(1), Expr::sort(Level::zero())),
                ),
            ),
            data: Box::new(data),
        }
    }

    fn eq_symm_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "Eq.symm".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: eq_symm_type(u.clone()),
            proof: eq_symm_proof(u),
        }
    }

    fn eq_symm_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "x",
                Expr::bvar(0),
                Expr::pi(
                    "y",
                    Expr::bvar(1),
                    Expr::pi(
                        "h",
                        eq(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        eq(u, Expr::bvar(3), Expr::bvar(1), Expr::bvar(2)),
                    ),
                ),
            ),
        )
    }

    fn eq_symm_proof(u: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "x",
                Expr::bvar(0),
                Expr::lam(
                    "y",
                    Expr::bvar(1),
                    Expr::lam(
                        "h",
                        eq(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        Expr::apps(
                            Expr::konst("Eq.rec", vec![u.clone(), Level::zero()]),
                            vec![
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::lam(
                                    "b",
                                    Expr::bvar(3),
                                    Expr::lam(
                                        "_h",
                                        eq(u.clone(), Expr::bvar(4), Expr::bvar(3), Expr::bvar(0)),
                                        eq(u.clone(), Expr::bvar(5), Expr::bvar(1), Expr::bvar(4)),
                                    ),
                                ),
                                eq_refl(u.clone(), Expr::bvar(3), Expr::bvar(2)),
                                Expr::bvar(1),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_trans_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "Eq.trans".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: eq_trans_type(u.clone()),
            proof: eq_trans_proof(u),
        }
    }

    fn eq_trans_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "x",
                Expr::bvar(0),
                Expr::pi(
                    "y",
                    Expr::bvar(1),
                    Expr::pi(
                        "z",
                        Expr::bvar(2),
                        Expr::pi(
                            "hxy",
                            eq(u.clone(), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)),
                            Expr::pi(
                                "hyz",
                                eq(u.clone(), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)),
                                eq(u, Expr::bvar(5), Expr::bvar(4), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_trans_proof(u: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "x",
                Expr::bvar(0),
                Expr::lam(
                    "y",
                    Expr::bvar(1),
                    Expr::lam(
                        "z",
                        Expr::bvar(2),
                        Expr::lam(
                            "hxy",
                            eq(u.clone(), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)),
                            Expr::lam(
                                "hyz",
                                eq(u.clone(), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)),
                                Expr::apps(
                                    Expr::konst("Eq.rec", vec![u.clone(), Level::zero()]),
                                    vec![
                                        Expr::bvar(5),
                                        Expr::bvar(3),
                                        Expr::lam(
                                            "b",
                                            Expr::bvar(5),
                                            Expr::lam(
                                                "_h",
                                                eq(
                                                    u.clone(),
                                                    Expr::bvar(6),
                                                    Expr::bvar(4),
                                                    Expr::bvar(0),
                                                ),
                                                eq(
                                                    u.clone(),
                                                    Expr::bvar(7),
                                                    Expr::bvar(6),
                                                    Expr::bvar(1),
                                                ),
                                            ),
                                        ),
                                        Expr::bvar(1),
                                        Expr::bvar(2),
                                        Expr::bvar(0),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_subst_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "Eq.subst".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: eq_subst_type(u.clone()),
            proof: eq_subst_proof(u),
        }
    }

    fn eq_subst_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "x",
                Expr::bvar(0),
                Expr::pi(
                    "y",
                    Expr::bvar(1),
                    Expr::pi(
                        "P",
                        Expr::pi("_", Expr::bvar(2), Expr::sort(Level::zero())),
                        Expr::pi(
                            "h",
                            eq(u.clone(), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)),
                            Expr::pi(
                                "px",
                                Expr::app(Expr::bvar(1), Expr::bvar(3)),
                                Expr::app(Expr::bvar(2), Expr::bvar(3)),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_subst_proof(u: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "x",
                Expr::bvar(0),
                Expr::lam(
                    "y",
                    Expr::bvar(1),
                    Expr::lam(
                        "P",
                        Expr::pi("_", Expr::bvar(2), Expr::sort(Level::zero())),
                        Expr::lam(
                            "h",
                            eq(u.clone(), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)),
                            Expr::lam(
                                "px",
                                Expr::app(Expr::bvar(1), Expr::bvar(3)),
                                Expr::apps(
                                    Expr::konst("Eq.rec", vec![u.clone(), Level::zero()]),
                                    vec![
                                        Expr::bvar(5),
                                        Expr::bvar(4),
                                        Expr::lam(
                                            "b",
                                            Expr::bvar(5),
                                            Expr::lam(
                                                "_h",
                                                eq(
                                                    u.clone(),
                                                    Expr::bvar(6),
                                                    Expr::bvar(5),
                                                    Expr::bvar(0),
                                                ),
                                                Expr::app(Expr::bvar(4), Expr::bvar(1)),
                                            ),
                                        ),
                                        Expr::bvar(0),
                                        Expr::bvar(3),
                                        Expr::bvar(1),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_congr_arg_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Theorem {
            name: "Eq.congrArg".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: eq_congr_arg_type(u.clone(), v.clone()),
            proof: eq_congr_arg_proof(u, v),
        }
    }

    fn eq_congr_arg_type(u: Level, v: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "B",
                Expr::sort(v.clone()),
                Expr::pi(
                    "f",
                    Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                    Expr::pi(
                        "x",
                        Expr::bvar(2),
                        Expr::pi(
                            "y",
                            Expr::bvar(3),
                            Expr::pi(
                                "h",
                                eq(u.clone(), Expr::bvar(4), Expr::bvar(1), Expr::bvar(0)),
                                eq(
                                    v,
                                    Expr::bvar(4),
                                    Expr::app(Expr::bvar(3), Expr::bvar(2)),
                                    Expr::app(Expr::bvar(3), Expr::bvar(1)),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_congr_arg_proof(u: Level, v: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "B",
                Expr::sort(v.clone()),
                Expr::lam(
                    "f",
                    Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                    Expr::lam(
                        "x",
                        Expr::bvar(2),
                        Expr::lam(
                            "y",
                            Expr::bvar(3),
                            Expr::lam(
                                "h",
                                eq(u.clone(), Expr::bvar(4), Expr::bvar(1), Expr::bvar(0)),
                                Expr::apps(
                                    Expr::konst("Eq.rec", vec![u.clone(), Level::zero()]),
                                    vec![
                                        Expr::bvar(5),
                                        Expr::bvar(2),
                                        Expr::lam(
                                            "b",
                                            Expr::bvar(5),
                                            Expr::lam(
                                                "_h",
                                                eq(
                                                    u.clone(),
                                                    Expr::bvar(6),
                                                    Expr::bvar(3),
                                                    Expr::bvar(0),
                                                ),
                                                eq(
                                                    v.clone(),
                                                    Expr::bvar(6),
                                                    Expr::app(Expr::bvar(5), Expr::bvar(4)),
                                                    Expr::app(Expr::bvar(5), Expr::bvar(1)),
                                                ),
                                            ),
                                        ),
                                        eq_refl(
                                            v.clone(),
                                            Expr::bvar(4),
                                            Expr::app(Expr::bvar(3), Expr::bvar(2)),
                                        ),
                                        Expr::bvar(1),
                                        Expr::bvar(0),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn logic_connective_declarations() -> Vec<Decl> {
        vec![
            true_inductive_decl(),
            false_inductive_decl(),
            not_def(),
            false_elim_theorem(),
            absurd_theorem(),
            not_intro_theorem(),
            not_elim_theorem(),
            and_inductive_decl(),
            and_left_theorem(),
            and_right_theorem(),
            and_intro_theorem(),
            or_inductive_decl(),
            or_elim_theorem(),
            or_inl_theorem(),
            or_inr_theorem(),
            iff_inductive_decl(),
            iff_mp_theorem(),
            iff_mpr_theorem(),
            iff_refl_theorem(),
            iff_symm_theorem(),
            iff_trans_theorem(),
            exists_inductive_decl(),
            exists_intro_theorem(),
            exists_elim_theorem(),
        ]
    }

    fn generated_mvp_inductive(data: InductiveDecl) -> InductiveDecl {
        npa_cert::generate_inductive_artifacts_v1(&data).unwrap()
    }

    fn prop_sort() -> Expr {
        Expr::sort(Level::zero())
    }

    fn true_() -> Expr {
        Expr::konst("True", vec![])
    }

    fn false_() -> Expr {
        Expr::konst("False", vec![])
    }

    fn not(p: Expr) -> Expr {
        Expr::app(Expr::konst("Not", vec![]), p)
    }

    fn and(p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::konst("And", vec![]), vec![p, q])
    }

    fn or(p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::konst("Or", vec![]), vec![p, q])
    }

    fn iff(p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::konst("Iff", vec![]), vec![p, q])
    }

    fn exists_(u: Level, a: Expr, p: Expr) -> Expr {
        Expr::apps(Expr::konst("Exists", vec![u]), vec![a, p])
    }

    fn true_inductive_decl() -> Decl {
        Decl::Inductive {
            name: "True".to_owned(),
            universe_params: Vec::new(),
            ty: prop_sort(),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "True",
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new("True.intro", true_())],
                None,
            ))),
        }
    }

    fn false_inductive_decl() -> Decl {
        Decl::Inductive {
            name: "False".to_owned(),
            universe_params: Vec::new(),
            ty: prop_sort(),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "False",
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Level::zero(),
                Vec::new(),
                None,
            ))),
        }
    }

    fn not_def() -> Decl {
        Decl::Def {
            name: "Not".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("P", prop_sort(), prop_sort()),
            value: Expr::lam("P", prop_sort(), Expr::pi("_", Expr::bvar(0), false_())),
            reducibility: Reducibility::Reducible,
        }
    }

    fn false_elim_theorem() -> Decl {
        Decl::Theorem {
            name: "False.elim".to_owned(),
            universe_params: Vec::new(),
            ty: false_elim_type(),
            proof: false_elim_proof(),
        }
    }

    fn false_elim_type() -> Expr {
        Expr::pi("P", prop_sort(), Expr::pi("_", false_(), Expr::bvar(1)))
    }

    fn false_elim_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "h",
                false_(),
                Expr::apps(
                    Expr::konst("False.rec", vec![]),
                    vec![Expr::lam("_", false_(), Expr::bvar(2)), Expr::bvar(0)],
                ),
            ),
        )
    }

    fn absurd_theorem() -> Decl {
        Decl::Theorem {
            name: "absurd".to_owned(),
            universe_params: Vec::new(),
            ty: absurd_type(),
            proof: absurd_proof(),
        }
    }

    fn absurd_type() -> Expr {
        Expr::pi(
            "P",
            prop_sort(),
            Expr::pi(
                "Q",
                prop_sort(),
                Expr::pi(
                    "hp",
                    Expr::bvar(1),
                    Expr::pi("hnp", not(Expr::bvar(2)), Expr::bvar(2)),
                ),
            ),
        )
    }

    fn absurd_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "hp",
                    Expr::bvar(1),
                    Expr::lam(
                        "hnp",
                        not(Expr::bvar(2)),
                        Expr::apps(
                            Expr::konst("False.elim", vec![]),
                            vec![Expr::bvar(2), Expr::app(Expr::bvar(0), Expr::bvar(1))],
                        ),
                    ),
                ),
            ),
        )
    }

    fn not_intro_theorem() -> Decl {
        Decl::Theorem {
            name: "not_intro".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "_",
                    Expr::pi("_", Expr::bvar(0), false_()),
                    not(Expr::bvar(1)),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam("_", Expr::pi("_", Expr::bvar(0), false_()), Expr::bvar(0)),
            ),
        }
    }

    fn not_elim_theorem() -> Decl {
        Decl::Theorem {
            name: "not_elim".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "hnp",
                    not(Expr::bvar(0)),
                    Expr::pi("hp", Expr::bvar(1), false_()),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam(
                    "hnp",
                    not(Expr::bvar(0)),
                    Expr::lam("hp", Expr::bvar(1), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                ),
            ),
        }
    }

    // Keep Human-facing theorem names available to apply search when constructor
    // names would otherwise collide with intro/inl/inr theorem exports.
    fn and_inductive_decl() -> Decl {
        Decl::Inductive {
            name: "And".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("P", prop_sort(), Expr::pi("Q", prop_sort(), prop_sort())),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "And",
                Vec::new(),
                vec![Binder::new("P", prop_sort()), Binder::new("Q", prop_sort())],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "And.mk",
                    Expr::pi(
                        "P",
                        prop_sort(),
                        Expr::pi(
                            "Q",
                            prop_sort(),
                            Expr::pi(
                                "left",
                                Expr::bvar(1),
                                Expr::pi("right", Expr::bvar(1), and(Expr::bvar(3), Expr::bvar(2))),
                            ),
                        ),
                    ),
                )],
                None,
            ))),
        }
    }

    fn and_left_theorem() -> Decl {
        Decl::Theorem {
            name: "And.left".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi("h", and(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(2)),
                ),
            ),
            proof: and_left_proof(),
        }
    }

    fn and_left_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "h",
                    and(Expr::bvar(1), Expr::bvar(0)),
                    Expr::apps(
                        Expr::konst("And.rec", vec![]),
                        vec![
                            Expr::bvar(2),
                            Expr::bvar(1),
                            Expr::lam("_", and(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(3)),
                            Expr::lam(
                                "left",
                                Expr::bvar(2),
                                Expr::lam("right", Expr::bvar(2), Expr::bvar(1)),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        )
    }

    fn and_right_theorem() -> Decl {
        Decl::Theorem {
            name: "And.right".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi("h", and(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
                ),
            ),
            proof: and_right_proof(),
        }
    }

    fn and_right_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "h",
                    and(Expr::bvar(1), Expr::bvar(0)),
                    Expr::apps(
                        Expr::konst("And.rec", vec![]),
                        vec![
                            Expr::bvar(2),
                            Expr::bvar(1),
                            Expr::lam("_", and(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(2)),
                            Expr::lam(
                                "left",
                                Expr::bvar(2),
                                Expr::lam("right", Expr::bvar(2), Expr::bvar(0)),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        )
    }

    fn and_intro_theorem() -> Decl {
        Decl::Theorem {
            name: "And.intro".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "left",
                        Expr::bvar(1),
                        Expr::pi("right", Expr::bvar(1), and(Expr::bvar(3), Expr::bvar(2))),
                    ),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam(
                    "Q",
                    prop_sort(),
                    Expr::lam(
                        "left",
                        Expr::bvar(1),
                        Expr::lam(
                            "right",
                            Expr::bvar(1),
                            Expr::apps(
                                Expr::konst("And.mk", vec![]),
                                vec![Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn or_inductive_decl() -> Decl {
        Decl::Inductive {
            name: "Or".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("P", prop_sort(), Expr::pi("Q", prop_sort(), prop_sort())),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "Or",
                Vec::new(),
                vec![Binder::new("P", prop_sort()), Binder::new("Q", prop_sort())],
                Vec::new(),
                Level::zero(),
                vec![
                    ConstructorDecl::new(
                        "Or.mk_inl",
                        Expr::pi(
                            "P",
                            prop_sort(),
                            Expr::pi(
                                "Q",
                                prop_sort(),
                                Expr::pi("left", Expr::bvar(1), or(Expr::bvar(2), Expr::bvar(1))),
                            ),
                        ),
                    ),
                    ConstructorDecl::new(
                        "Or.mk_inr",
                        Expr::pi(
                            "P",
                            prop_sort(),
                            Expr::pi(
                                "Q",
                                prop_sort(),
                                Expr::pi("right", Expr::bvar(0), or(Expr::bvar(2), Expr::bvar(1))),
                            ),
                        ),
                    ),
                ],
                None,
            ))),
        }
    }

    fn or_elim_theorem() -> Decl {
        Decl::Theorem {
            name: "Or.elim".to_owned(),
            universe_params: Vec::new(),
            ty: or_elim_type(),
            proof: or_elim_proof(),
        }
    }

    fn or_elim_type() -> Expr {
        Expr::pi(
            "P",
            prop_sort(),
            Expr::pi(
                "Q",
                prop_sort(),
                Expr::pi(
                    "R",
                    prop_sort(),
                    Expr::pi(
                        "h",
                        or(Expr::bvar(2), Expr::bvar(1)),
                        Expr::pi(
                            "left_case",
                            Expr::pi("_", Expr::bvar(3), Expr::bvar(2)),
                            Expr::pi(
                                "right_case",
                                Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                Expr::bvar(3),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn or_elim_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "R",
                    prop_sort(),
                    Expr::lam(
                        "h",
                        or(Expr::bvar(2), Expr::bvar(1)),
                        Expr::lam(
                            "left_case",
                            Expr::pi("_", Expr::bvar(3), Expr::bvar(2)),
                            Expr::lam(
                                "right_case",
                                Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                Expr::apps(
                                    Expr::konst("Or.rec", vec![]),
                                    vec![
                                        Expr::bvar(5),
                                        Expr::bvar(4),
                                        Expr::lam(
                                            "_",
                                            or(Expr::bvar(5), Expr::bvar(4)),
                                            Expr::bvar(4),
                                        ),
                                        Expr::lam(
                                            "left",
                                            Expr::bvar(5),
                                            Expr::app(Expr::bvar(2), Expr::bvar(0)),
                                        ),
                                        Expr::lam(
                                            "right",
                                            Expr::bvar(4),
                                            Expr::app(Expr::bvar(1), Expr::bvar(0)),
                                        ),
                                        Expr::bvar(2),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn or_inl_theorem() -> Decl {
        Decl::Theorem {
            name: "Or.inl".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi("left", Expr::bvar(1), or(Expr::bvar(2), Expr::bvar(1))),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam(
                    "Q",
                    prop_sort(),
                    Expr::lam(
                        "left",
                        Expr::bvar(1),
                        Expr::apps(
                            Expr::konst("Or.mk_inl", vec![]),
                            vec![Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                        ),
                    ),
                ),
            ),
        }
    }

    fn or_inr_theorem() -> Decl {
        Decl::Theorem {
            name: "Or.inr".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi("right", Expr::bvar(0), or(Expr::bvar(2), Expr::bvar(1))),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam(
                    "Q",
                    prop_sort(),
                    Expr::lam(
                        "right",
                        Expr::bvar(0),
                        Expr::apps(
                            Expr::konst("Or.mk_inr", vec![]),
                            vec![Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                        ),
                    ),
                ),
            ),
        }
    }

    fn iff_inductive_decl() -> Decl {
        Decl::Inductive {
            name: "Iff".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("P", prop_sort(), Expr::pi("Q", prop_sort(), prop_sort())),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "Iff",
                Vec::new(),
                vec![Binder::new("P", prop_sort()), Binder::new("Q", prop_sort())],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "Iff.intro",
                    Expr::pi(
                        "P",
                        prop_sort(),
                        Expr::pi(
                            "Q",
                            prop_sort(),
                            Expr::pi(
                                "mp",
                                Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                                Expr::pi(
                                    "mpr",
                                    Expr::pi("_", Expr::bvar(1), Expr::bvar(3)),
                                    iff(Expr::bvar(3), Expr::bvar(2)),
                                ),
                            ),
                        ),
                    ),
                )],
                None,
            ))),
        }
    }

    fn iff_mp_theorem() -> Decl {
        Decl::Theorem {
            name: "Iff.mp".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "h",
                        iff(Expr::bvar(1), Expr::bvar(0)),
                        Expr::pi("hp", Expr::bvar(2), Expr::bvar(2)),
                    ),
                ),
            ),
            proof: iff_mp_proof(),
        }
    }

    fn iff_mp_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "h",
                    iff(Expr::bvar(1), Expr::bvar(0)),
                    Expr::lam(
                        "hp",
                        Expr::bvar(2),
                        Expr::app(
                            Expr::apps(
                                Expr::konst("Iff.rec", vec![]),
                                vec![
                                    Expr::bvar(3),
                                    Expr::bvar(2),
                                    Expr::lam(
                                        "_",
                                        iff(Expr::bvar(3), Expr::bvar(2)),
                                        Expr::pi("_", Expr::bvar(4), Expr::bvar(4)),
                                    ),
                                    Expr::lam(
                                        "mp",
                                        Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                        Expr::lam(
                                            "mpr",
                                            Expr::pi("_", Expr::bvar(3), Expr::bvar(5)),
                                            Expr::bvar(1),
                                        ),
                                    ),
                                    Expr::bvar(1),
                                ],
                            ),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
        )
    }

    fn iff_mpr_theorem() -> Decl {
        Decl::Theorem {
            name: "Iff.mpr".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "h",
                        iff(Expr::bvar(1), Expr::bvar(0)),
                        Expr::pi("hq", Expr::bvar(1), Expr::bvar(3)),
                    ),
                ),
            ),
            proof: iff_mpr_proof(),
        }
    }

    fn iff_mpr_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "h",
                    iff(Expr::bvar(1), Expr::bvar(0)),
                    Expr::lam(
                        "hq",
                        Expr::bvar(1),
                        Expr::app(
                            Expr::apps(
                                Expr::konst("Iff.rec", vec![]),
                                vec![
                                    Expr::bvar(3),
                                    Expr::bvar(2),
                                    Expr::lam(
                                        "_",
                                        iff(Expr::bvar(3), Expr::bvar(2)),
                                        Expr::pi("_", Expr::bvar(3), Expr::bvar(5)),
                                    ),
                                    Expr::lam(
                                        "mp",
                                        Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                        Expr::lam(
                                            "mpr",
                                            Expr::pi("_", Expr::bvar(3), Expr::bvar(5)),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                    Expr::bvar(1),
                                ],
                            ),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
        )
    }

    fn iff_refl_theorem() -> Decl {
        Decl::Theorem {
            name: "Iff.refl".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("P", prop_sort(), iff(Expr::bvar(0), Expr::bvar(0))),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::apps(
                    Expr::konst("Iff.intro", vec![]),
                    vec![
                        Expr::bvar(0),
                        Expr::bvar(0),
                        Expr::lam("_", Expr::bvar(0), Expr::bvar(0)),
                        Expr::lam("_", Expr::bvar(0), Expr::bvar(0)),
                    ],
                ),
            ),
        }
    }

    fn iff_symm_theorem() -> Decl {
        Decl::Theorem {
            name: "Iff.symm".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "h",
                        iff(Expr::bvar(1), Expr::bvar(0)),
                        iff(Expr::bvar(1), Expr::bvar(2)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "P",
                prop_sort(),
                Expr::lam(
                    "Q",
                    prop_sort(),
                    Expr::lam(
                        "h",
                        iff(Expr::bvar(1), Expr::bvar(0)),
                        Expr::apps(
                            Expr::konst("Iff.intro", vec![]),
                            vec![
                                Expr::bvar(1),
                                Expr::bvar(2),
                                Expr::apps(
                                    Expr::konst("Iff.mpr", vec![]),
                                    vec![Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                                ),
                                Expr::apps(
                                    Expr::konst("Iff.mp", vec![]),
                                    vec![Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                                ),
                            ],
                        ),
                    ),
                ),
            ),
        }
    }

    fn iff_trans_theorem() -> Decl {
        Decl::Theorem {
            name: "Iff.trans".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "P",
                prop_sort(),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "R",
                        prop_sort(),
                        Expr::pi(
                            "hpq",
                            iff(Expr::bvar(2), Expr::bvar(1)),
                            Expr::pi(
                                "hqr",
                                iff(Expr::bvar(2), Expr::bvar(1)),
                                iff(Expr::bvar(4), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            ),
            proof: iff_trans_proof(),
        }
    }

    fn iff_trans_proof() -> Expr {
        Expr::lam(
            "P",
            prop_sort(),
            Expr::lam(
                "Q",
                prop_sort(),
                Expr::lam(
                    "R",
                    prop_sort(),
                    Expr::lam(
                        "hpq",
                        iff(Expr::bvar(2), Expr::bvar(1)),
                        Expr::lam(
                            "hqr",
                            iff(Expr::bvar(2), Expr::bvar(1)),
                            Expr::apps(
                                Expr::konst("Iff.intro", vec![]),
                                vec![
                                    Expr::bvar(4),
                                    Expr::bvar(2),
                                    Expr::lam(
                                        "hp",
                                        Expr::bvar(4),
                                        Expr::apps(
                                            Expr::konst("Iff.mp", vec![]),
                                            vec![
                                                Expr::bvar(4),
                                                Expr::bvar(3),
                                                Expr::bvar(1),
                                                Expr::apps(
                                                    Expr::konst("Iff.mp", vec![]),
                                                    vec![
                                                        Expr::bvar(5),
                                                        Expr::bvar(4),
                                                        Expr::bvar(2),
                                                        Expr::bvar(0),
                                                    ],
                                                ),
                                            ],
                                        ),
                                    ),
                                    Expr::lam(
                                        "hr",
                                        Expr::bvar(2),
                                        Expr::apps(
                                            Expr::konst("Iff.mpr", vec![]),
                                            vec![
                                                Expr::bvar(5),
                                                Expr::bvar(4),
                                                Expr::bvar(2),
                                                Expr::apps(
                                                    Expr::konst("Iff.mpr", vec![]),
                                                    vec![
                                                        Expr::bvar(4),
                                                        Expr::bvar(3),
                                                        Expr::bvar(1),
                                                        Expr::bvar(0),
                                                    ],
                                                ),
                                            ],
                                        ),
                                    ),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn exists_inductive_decl() -> Decl {
        let u = Level::param("u");
        Decl::Inductive {
            name: "Exists".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("P", Expr::pi("_", Expr::bvar(0), prop_sort()), prop_sort()),
            ),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "Exists",
                vec!["u".to_owned()],
                vec![
                    Binder::new("A", Expr::sort(u.clone())),
                    Binder::new("P", Expr::pi("_", Expr::bvar(0), prop_sort())),
                ],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "Exists.mk",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "P",
                            Expr::pi("_", Expr::bvar(0), prop_sort()),
                            Expr::pi(
                                "x",
                                Expr::bvar(1),
                                Expr::pi(
                                    "px",
                                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                                    exists_(u, Expr::bvar(3), Expr::bvar(2)),
                                ),
                            ),
                        ),
                    ),
                )],
                None,
            ))),
        }
    }

    fn exists_intro_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "Exists.intro".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "P",
                    Expr::pi("_", Expr::bvar(0), prop_sort()),
                    Expr::pi(
                        "x",
                        Expr::bvar(1),
                        Expr::pi(
                            "px",
                            Expr::app(Expr::bvar(1), Expr::bvar(0)),
                            exists_(u.clone(), Expr::bvar(3), Expr::bvar(2)),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "P",
                    Expr::pi("_", Expr::bvar(0), prop_sort()),
                    Expr::lam(
                        "x",
                        Expr::bvar(1),
                        Expr::lam(
                            "px",
                            Expr::app(Expr::bvar(1), Expr::bvar(0)),
                            Expr::apps(
                                Expr::konst("Exists.mk", vec![u]),
                                vec![Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn exists_elim_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "Exists.elim".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: exists_elim_type(u.clone()),
            proof: exists_elim_proof(u),
        }
    }

    fn exists_elim_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "P",
                Expr::pi("_", Expr::bvar(0), prop_sort()),
                Expr::pi(
                    "Q",
                    prop_sort(),
                    Expr::pi(
                        "h",
                        exists_(u, Expr::bvar(2), Expr::bvar(1)),
                        Expr::pi(
                            "case",
                            Expr::pi(
                                "x",
                                Expr::bvar(3),
                                Expr::pi(
                                    "px",
                                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                                    Expr::bvar(3),
                                ),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        )
    }

    fn exists_elim_proof(u: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "P",
                Expr::pi("_", Expr::bvar(0), prop_sort()),
                Expr::lam(
                    "Q",
                    prop_sort(),
                    Expr::lam(
                        "h",
                        exists_(u.clone(), Expr::bvar(2), Expr::bvar(1)),
                        Expr::lam(
                            "case",
                            Expr::pi(
                                "x",
                                Expr::bvar(3),
                                Expr::pi(
                                    "px",
                                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                                    Expr::bvar(3),
                                ),
                            ),
                            Expr::apps(
                                Expr::konst("Exists.rec", vec![u.clone()]),
                                vec![
                                    Expr::bvar(4),
                                    Expr::bvar(3),
                                    Expr::lam(
                                        "_",
                                        exists_(u, Expr::bvar(4), Expr::bvar(3)),
                                        Expr::bvar(3),
                                    ),
                                    Expr::lam(
                                        "x",
                                        Expr::bvar(4),
                                        Expr::lam(
                                            "px",
                                            Expr::app(Expr::bvar(4), Expr::bvar(0)),
                                            Expr::apps(
                                                Expr::bvar(2),
                                                vec![Expr::bvar(1), Expr::bvar(0)],
                                            ),
                                        ),
                                    ),
                                    Expr::bvar(1),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn nat_basic_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Nat"),
            declarations: nat_basic_declarations(),
        }
    }

    fn nat_family_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Nat"),
            declarations: nat_family_declarations(),
        }
    }

    fn nat_family_declarations() -> Vec<Decl> {
        vec![Decl::Inductive {
            name: "Nat".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::sort(type0()),
            data: Box::new(nat_inductive()),
        }]
    }

    fn nat_basic_declarations() -> Vec<Decl> {
        let mut declarations = nat_family_declarations();
        declarations.extend([
            nat_one_def(),
            nat_pred_def(),
            nat_pred_zero_theorem(),
            nat_pred_succ_theorem(),
            nat_add_def(),
            nat_add_zero_theorem(),
            nat_add_succ_theorem(),
            nat_zero_add_theorem(),
            nat_succ_add_theorem(),
            nat_add_assoc_theorem(),
            nat_add_comm_theorem(),
            nat_mul_def(),
            nat_mul_zero_theorem(),
            nat_mul_succ_theorem(),
            nat_zero_mul_theorem(),
            nat_succ_mul_theorem(),
            nat_mul_comm_theorem(),
            nat_left_distrib_theorem(),
            nat_mul_assoc_theorem(),
            nat_right_distrib_theorem(),
        ]);
        declarations
    }

    fn nat_one_def() -> Decl {
        Decl::Def {
            name: "Nat.one".to_owned(),
            universe_params: Vec::new(),
            ty: nat(),
            value: nat_succ(nat_zero()),
            reducibility: Reducibility::Reducible,
        }
    }

    fn nat_pred_def() -> Decl {
        Decl::Def {
            name: "Nat.pred".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("n", nat(), nat()),
            value: Expr::lam(
                "n",
                nat(),
                Expr::apps(
                    Expr::konst("Nat.rec", vec![type0()]),
                    vec![
                        Expr::lam("_", nat(), nat()),
                        nat_zero(),
                        Expr::lam("k", nat(), Expr::lam("_ih", nat(), Expr::bvar(1))),
                        Expr::bvar(0),
                    ],
                ),
            ),
            reducibility: Reducibility::Reducible,
        }
    }

    fn nat_pred_zero_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.pred_zero".to_owned(),
            universe_params: Vec::new(),
            ty: eq(
                type0(),
                nat(),
                Expr::app(Expr::konst("Nat.pred", vec![]), nat_zero()),
                nat_zero(),
            ),
            proof: eq_refl(type0(), nat(), nat_zero()),
        }
    }

    fn nat_pred_succ_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.pred_succ".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "n",
                nat(),
                eq(
                    type0(),
                    nat(),
                    Expr::app(Expr::konst("Nat.pred", vec![]), nat_succ(Expr::bvar(0))),
                    Expr::bvar(0),
                ),
            ),
            proof: Expr::lam("n", nat(), eq_refl(type0(), nat(), Expr::bvar(0))),
        }
    }

    fn nat_add_def() -> Decl {
        Decl::Def {
            name: "Nat.add".to_owned(),
            universe_params: Vec::new(),
            ty: nat_add_type(),
            value: nat_add_value(),
            reducibility: Reducibility::Reducible,
        }
    }

    fn nat_add_type() -> Expr {
        Expr::pi("n", nat(), Expr::pi("m", nat(), nat()))
    }

    fn nat_add_value() -> Expr {
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))));
        let rec = Expr::apps(
            Expr::konst("Nat.rec", vec![type0()]),
            vec![motive, Expr::bvar(1), step, Expr::bvar(0)],
        );
        Expr::lam("n", nat(), Expr::lam("m", nat(), rec))
    }

    fn nat_add_zero_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.add_zero".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("n", nat(), nat_add_zero_prop(Expr::bvar(0))),
            proof: Expr::lam("n", nat(), eq_refl(type0(), nat(), Expr::bvar(0))),
        }
    }

    fn nat_add_succ_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.add_succ".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "n",
                nat(),
                Expr::pi(
                    "m",
                    nat(),
                    eq(
                        type0(),
                        nat(),
                        nat_add(Expr::bvar(1), nat_succ(Expr::bvar(0))),
                        nat_succ(nat_add(Expr::bvar(1), Expr::bvar(0))),
                    ),
                ),
            ),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::lam(
                    "m",
                    nat(),
                    eq_refl(
                        type0(),
                        nat(),
                        nat_succ(nat_add(Expr::bvar(1), Expr::bvar(0))),
                    ),
                ),
            ),
        }
    }

    fn nat_zero_add_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.zero_add".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("n", nat(), nat_zero_add_prop(Expr::bvar(0))),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::apps(
                    Expr::konst("Nat.rec", vec![Level::zero()]),
                    vec![
                        Expr::lam("n", nat(), nat_zero_add_prop(Expr::bvar(0))),
                        eq_refl(type0(), nat(), nat_zero()),
                        Expr::lam(
                            "k",
                            nat(),
                            Expr::lam(
                                "ih",
                                nat_zero_add_prop(Expr::bvar(0)),
                                eq_congr_succ(
                                    nat_add(nat_zero(), Expr::bvar(1)),
                                    Expr::bvar(1),
                                    Expr::bvar(0),
                                ),
                            ),
                        ),
                        Expr::bvar(0),
                    ],
                ),
            ),
        }
    }

    fn nat_succ_add_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.succ_add".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "n",
                nat(),
                Expr::pi("m", nat(), nat_succ_add_prop(Expr::bvar(1), Expr::bvar(0))),
            ),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::lam(
                    "m",
                    nat(),
                    Expr::apps(
                        Expr::konst("Nat.rec", vec![Level::zero()]),
                        vec![
                            Expr::lam("m", nat(), nat_succ_add_prop(Expr::bvar(2), Expr::bvar(0))),
                            eq_refl(type0(), nat(), nat_succ(Expr::bvar(1))),
                            Expr::lam(
                                "k",
                                nat(),
                                Expr::lam(
                                    "ih",
                                    nat_succ_add_prop(Expr::bvar(2), Expr::bvar(0)),
                                    eq_congr_succ(
                                        nat_add(nat_succ(Expr::bvar(3)), Expr::bvar(1)),
                                        nat_succ(nat_add(Expr::bvar(3), Expr::bvar(1))),
                                        Expr::bvar(0),
                                    ),
                                ),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn nat_add_assoc_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.add_assoc".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi(
                    "b",
                    nat(),
                    Expr::pi(
                        "c",
                        nat(),
                        nat_add_assoc_prop(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::lam(
                        "c",
                        nat(),
                        Expr::apps(
                            Expr::konst("Nat.rec", vec![Level::zero()]),
                            vec![
                                Expr::lam(
                                    "c",
                                    nat(),
                                    nat_add_assoc_prop(Expr::bvar(3), Expr::bvar(2), Expr::bvar(0)),
                                ),
                                eq_refl(type0(), nat(), nat_add(Expr::bvar(2), Expr::bvar(1))),
                                Expr::lam(
                                    "k",
                                    nat(),
                                    Expr::lam(
                                        "ih",
                                        nat_add_assoc_prop(
                                            Expr::bvar(3),
                                            Expr::bvar(2),
                                            Expr::bvar(0),
                                        ),
                                        eq_congr_succ(
                                            nat_add(
                                                nat_add(Expr::bvar(4), Expr::bvar(3)),
                                                Expr::bvar(1),
                                            ),
                                            nat_add(
                                                Expr::bvar(4),
                                                nat_add(Expr::bvar(3), Expr::bvar(1)),
                                            ),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                ),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        }
    }

    fn nat_add_comm_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.add_comm".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi("b", nat(), nat_add_comm_prop(Expr::bvar(1), Expr::bvar(0))),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::apps(
                        Expr::konst("Nat.rec", vec![Level::zero()]),
                        vec![
                            Expr::lam("b", nat(), nat_add_comm_prop(Expr::bvar(2), Expr::bvar(0))),
                            eq_symm_nat(
                                nat_add(nat_zero(), Expr::bvar(1)),
                                Expr::bvar(1),
                                Expr::app(Expr::konst("Nat.zero_add", vec![]), Expr::bvar(1)),
                            ),
                            Expr::lam(
                                "k",
                                nat(),
                                Expr::lam("ih", nat_add_comm_prop(Expr::bvar(2), Expr::bvar(0)), {
                                    let lhs = nat_succ(nat_add(Expr::bvar(3), Expr::bvar(1)));
                                    let mid = nat_succ(nat_add(Expr::bvar(1), Expr::bvar(3)));
                                    let rhs = nat_add(nat_succ(Expr::bvar(1)), Expr::bvar(3));
                                    eq_trans_nat(
                                        lhs.clone(),
                                        mid.clone(),
                                        rhs.clone(),
                                        eq_congr_succ(
                                            nat_add(Expr::bvar(3), Expr::bvar(1)),
                                            nat_add(Expr::bvar(1), Expr::bvar(3)),
                                            Expr::bvar(0),
                                        ),
                                        eq_symm_nat(
                                            rhs,
                                            mid,
                                            Expr::apps(
                                                Expr::konst("Nat.succ_add", vec![]),
                                                vec![Expr::bvar(1), Expr::bvar(3)],
                                            ),
                                        ),
                                    )
                                }),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn nat_mul_def() -> Decl {
        Decl::Def {
            name: "Nat.mul".to_owned(),
            universe_params: Vec::new(),
            ty: nat_mul_type(),
            value: nat_mul_value(),
            reducibility: Reducibility::Reducible,
        }
    }

    fn nat_mul_type() -> Expr {
        Expr::pi("n", nat(), Expr::pi("m", nat(), nat()))
    }

    fn nat_mul_value() -> Expr {
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam(
            "_",
            nat(),
            Expr::lam("ih", nat(), nat_add(Expr::bvar(0), Expr::bvar(3))),
        );
        let rec = Expr::apps(
            Expr::konst("Nat.rec", vec![type0()]),
            vec![motive, nat_zero(), step, Expr::bvar(0)],
        );
        Expr::lam("n", nat(), Expr::lam("m", nat(), rec))
    }

    fn nat_mul_zero_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.mul_zero".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("n", nat(), nat_mul_zero_prop(Expr::bvar(0))),
            proof: Expr::lam("n", nat(), eq_refl(type0(), nat(), nat_zero())),
        }
    }

    fn nat_mul_succ_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.mul_succ".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "n",
                nat(),
                Expr::pi(
                    "m",
                    nat(),
                    eq(
                        type0(),
                        nat(),
                        nat_mul(Expr::bvar(1), nat_succ(Expr::bvar(0))),
                        nat_add(nat_mul(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::lam(
                    "m",
                    nat(),
                    eq_refl(
                        type0(),
                        nat(),
                        nat_add(nat_mul(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
                    ),
                ),
            ),
        }
    }

    fn nat_zero_mul_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.zero_mul".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi("n", nat(), nat_zero_mul_prop(Expr::bvar(0))),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::apps(
                    Expr::konst("Nat.rec", vec![Level::zero()]),
                    vec![
                        Expr::lam("n", nat(), nat_zero_mul_prop(Expr::bvar(0))),
                        eq_refl(type0(), nat(), nat_zero()),
                        Expr::lam(
                            "k",
                            nat(),
                            Expr::lam("ih", nat_zero_mul_prop(Expr::bvar(0)), {
                                let lhs = nat_add(nat_mul(nat_zero(), Expr::bvar(1)), nat_zero());
                                let mid = nat_mul(nat_zero(), Expr::bvar(1));
                                eq_trans_nat(
                                    lhs,
                                    mid.clone(),
                                    nat_zero(),
                                    Expr::app(Expr::konst("Nat.add_zero", vec![]), mid),
                                    Expr::bvar(0),
                                )
                            }),
                        ),
                        Expr::bvar(0),
                    ],
                ),
            ),
        }
    }

    fn nat_succ_mul_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.succ_mul".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "n",
                nat(),
                Expr::pi("m", nat(), nat_succ_mul_prop(Expr::bvar(1), Expr::bvar(0))),
            ),
            proof: Expr::lam(
                "n",
                nat(),
                Expr::lam(
                    "m",
                    nat(),
                    Expr::apps(
                        Expr::konst("Nat.rec", vec![Level::zero()]),
                        vec![
                            Expr::lam("m", nat(), nat_succ_mul_prop(Expr::bvar(2), Expr::bvar(0))),
                            eq_refl(type0(), nat(), nat_zero()),
                            Expr::lam(
                                "k",
                                nat(),
                                Expr::lam("ih", nat_succ_mul_prop(Expr::bvar(2), Expr::bvar(0)), {
                                    let n = Expr::bvar(3);
                                    let k = Expr::bvar(1);
                                    let lhs = nat_add(
                                        nat_mul(nat_succ(n.clone()), k.clone()),
                                        nat_succ(n.clone()),
                                    );
                                    let mid1 = nat_succ(nat_add(
                                        nat_mul(nat_succ(n.clone()), k.clone()),
                                        n.clone(),
                                    ));
                                    let ih_rhs = nat_add(k.clone(), nat_mul(n.clone(), k.clone()));
                                    let mid2 = nat_succ(nat_add(ih_rhs.clone(), n.clone()));
                                    let mid3 = nat_succ(nat_add(
                                        k.clone(),
                                        nat_add(nat_mul(n.clone(), k.clone()), n.clone()),
                                    ));
                                    let rhs = nat_add(
                                        nat_succ(k.clone()),
                                        nat_add(nat_mul(n.clone(), k), n.clone()),
                                    );
                                    eq_trans_nat(
                                        lhs,
                                        mid1.clone(),
                                        rhs.clone(),
                                        Expr::apps(
                                            Expr::konst("Nat.add_succ", vec![]),
                                            vec![
                                                nat_mul(nat_succ(n.clone()), Expr::bvar(1)),
                                                n.clone(),
                                            ],
                                        ),
                                        eq_trans_nat(
                                            mid1,
                                            mid2.clone(),
                                            rhs.clone(),
                                            eq_congr_succ(
                                                nat_add(
                                                    nat_mul(nat_succ(n.clone()), Expr::bvar(1)),
                                                    n.clone(),
                                                ),
                                                nat_add(ih_rhs.clone(), n.clone()),
                                                eq_congr_add_right(
                                                    n.clone(),
                                                    nat_mul(nat_succ(n.clone()), Expr::bvar(1)),
                                                    ih_rhs,
                                                    Expr::bvar(0),
                                                ),
                                            ),
                                            eq_trans_nat(
                                                mid2,
                                                mid3.clone(),
                                                rhs,
                                                eq_congr_succ(
                                                    nat_add(
                                                        nat_add(
                                                            Expr::bvar(1),
                                                            nat_mul(n.clone(), Expr::bvar(1)),
                                                        ),
                                                        n.clone(),
                                                    ),
                                                    nat_add(
                                                        Expr::bvar(1),
                                                        nat_add(
                                                            nat_mul(n.clone(), Expr::bvar(1)),
                                                            n.clone(),
                                                        ),
                                                    ),
                                                    Expr::apps(
                                                        Expr::konst("Nat.add_assoc", vec![]),
                                                        vec![
                                                            Expr::bvar(1),
                                                            nat_mul(n.clone(), Expr::bvar(1)),
                                                            n.clone(),
                                                        ],
                                                    ),
                                                ),
                                                eq_symm_nat(
                                                    nat_add(
                                                        nat_succ(Expr::bvar(1)),
                                                        nat_add(
                                                            nat_mul(n.clone(), Expr::bvar(1)),
                                                            n,
                                                        ),
                                                    ),
                                                    mid3,
                                                    Expr::apps(
                                                        Expr::konst("Nat.succ_add", vec![]),
                                                        vec![
                                                            Expr::bvar(1),
                                                            nat_add(
                                                                nat_mul(
                                                                    Expr::bvar(3),
                                                                    Expr::bvar(1),
                                                                ),
                                                                Expr::bvar(3),
                                                            ),
                                                        ],
                                                    ),
                                                ),
                                            ),
                                        ),
                                    )
                                }),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn nat_mul_comm_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.mul_comm".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi("b", nat(), nat_mul_comm_prop(Expr::bvar(1), Expr::bvar(0))),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::apps(
                        Expr::konst("Nat.rec", vec![Level::zero()]),
                        vec![
                            Expr::lam("b", nat(), nat_mul_comm_prop(Expr::bvar(2), Expr::bvar(0))),
                            eq_symm_nat(
                                nat_mul(nat_zero(), Expr::bvar(1)),
                                nat_zero(),
                                Expr::app(Expr::konst("Nat.zero_mul", vec![]), Expr::bvar(1)),
                            ),
                            Expr::lam(
                                "k",
                                nat(),
                                Expr::lam("ih", nat_mul_comm_prop(Expr::bvar(2), Expr::bvar(0)), {
                                    let a = Expr::bvar(3);
                                    let k = Expr::bvar(1);
                                    let lhs = nat_add(nat_mul(a.clone(), k.clone()), a.clone());
                                    let mid1 = nat_add(nat_mul(k.clone(), a.clone()), a.clone());
                                    let mid2 = nat_add(a.clone(), nat_mul(k.clone(), a.clone()));
                                    let rhs = nat_mul(nat_succ(k.clone()), a.clone());
                                    eq_trans_nat(
                                        lhs,
                                        mid1.clone(),
                                        rhs.clone(),
                                        eq_congr_add_right(
                                            a.clone(),
                                            nat_mul(a.clone(), k.clone()),
                                            nat_mul(k.clone(), a.clone()),
                                            Expr::bvar(0),
                                        ),
                                        eq_trans_nat(
                                            mid1,
                                            mid2.clone(),
                                            rhs.clone(),
                                            Expr::apps(
                                                Expr::konst("Nat.add_comm", vec![]),
                                                vec![nat_mul(k.clone(), a.clone()), a.clone()],
                                            ),
                                            eq_symm_nat(
                                                rhs,
                                                mid2,
                                                Expr::apps(
                                                    Expr::konst("Nat.succ_mul", vec![]),
                                                    vec![k, a],
                                                ),
                                            ),
                                        ),
                                    )
                                }),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn nat_left_distrib_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.left_distrib".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi(
                    "b",
                    nat(),
                    Expr::pi(
                        "c",
                        nat(),
                        nat_left_distrib_prop(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::lam(
                        "c",
                        nat(),
                        Expr::apps(
                            Expr::konst("Nat.rec", vec![Level::zero()]),
                            vec![
                                Expr::lam(
                                    "c",
                                    nat(),
                                    nat_left_distrib_prop(
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        Expr::bvar(0),
                                    ),
                                ),
                                eq_refl(type0(), nat(), nat_mul(Expr::bvar(2), Expr::bvar(1))),
                                Expr::lam(
                                    "k",
                                    nat(),
                                    Expr::lam(
                                        "ih",
                                        nat_left_distrib_prop(
                                            Expr::bvar(3),
                                            Expr::bvar(2),
                                            Expr::bvar(0),
                                        ),
                                        {
                                            let a = Expr::bvar(4);
                                            let b = Expr::bvar(3);
                                            let k = Expr::bvar(1);
                                            let lhs = nat_add(
                                                nat_mul(a.clone(), nat_add(b.clone(), k.clone())),
                                                a.clone(),
                                            );
                                            let mid = nat_add(
                                                nat_add(
                                                    nat_mul(a.clone(), b.clone()),
                                                    nat_mul(a.clone(), k.clone()),
                                                ),
                                                a.clone(),
                                            );
                                            let rhs = nat_add(
                                                nat_mul(a.clone(), b.clone()),
                                                nat_add(nat_mul(a.clone(), k), a.clone()),
                                            );
                                            eq_trans_nat(
                                                lhs,
                                                mid.clone(),
                                                rhs.clone(),
                                                eq_congr_add_right(
                                                    a.clone(),
                                                    nat_mul(
                                                        a.clone(),
                                                        nat_add(b.clone(), Expr::bvar(1)),
                                                    ),
                                                    nat_add(
                                                        nat_mul(a.clone(), b.clone()),
                                                        nat_mul(a.clone(), Expr::bvar(1)),
                                                    ),
                                                    Expr::bvar(0),
                                                ),
                                                Expr::apps(
                                                    Expr::konst("Nat.add_assoc", vec![]),
                                                    vec![
                                                        nat_mul(a.clone(), b),
                                                        nat_mul(a.clone(), Expr::bvar(1)),
                                                        a,
                                                    ],
                                                ),
                                            )
                                        },
                                    ),
                                ),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        }
    }

    fn nat_mul_assoc_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.mul_assoc".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi(
                    "b",
                    nat(),
                    Expr::pi(
                        "c",
                        nat(),
                        nat_mul_assoc_prop(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::lam(
                        "c",
                        nat(),
                        Expr::apps(
                            Expr::konst("Nat.rec", vec![Level::zero()]),
                            vec![
                                Expr::lam(
                                    "c",
                                    nat(),
                                    nat_mul_assoc_prop(Expr::bvar(3), Expr::bvar(2), Expr::bvar(0)),
                                ),
                                eq_refl(type0(), nat(), nat_zero()),
                                Expr::lam(
                                    "k",
                                    nat(),
                                    Expr::lam(
                                        "ih",
                                        nat_mul_assoc_prop(
                                            Expr::bvar(3),
                                            Expr::bvar(2),
                                            Expr::bvar(0),
                                        ),
                                        {
                                            let a = Expr::bvar(4);
                                            let b = Expr::bvar(3);
                                            let k = Expr::bvar(1);
                                            let lhs = nat_add(
                                                nat_mul(nat_mul(a.clone(), b.clone()), k.clone()),
                                                nat_mul(a.clone(), b.clone()),
                                            );
                                            let mid = nat_add(
                                                nat_mul(a.clone(), nat_mul(b.clone(), k.clone())),
                                                nat_mul(a.clone(), b.clone()),
                                            );
                                            let rhs = nat_mul(
                                                a.clone(),
                                                nat_add(nat_mul(b.clone(), k), b.clone()),
                                            );
                                            eq_trans_nat(
                                                lhs,
                                                mid.clone(),
                                                rhs.clone(),
                                                eq_congr_add_right(
                                                    nat_mul(a.clone(), b.clone()),
                                                    nat_mul(
                                                        nat_mul(a.clone(), b.clone()),
                                                        Expr::bvar(1),
                                                    ),
                                                    nat_mul(
                                                        a.clone(),
                                                        nat_mul(b.clone(), Expr::bvar(1)),
                                                    ),
                                                    Expr::bvar(0),
                                                ),
                                                eq_symm_nat(
                                                    rhs,
                                                    mid,
                                                    Expr::apps(
                                                        Expr::konst("Nat.left_distrib", vec![]),
                                                        vec![
                                                            a,
                                                            nat_mul(b.clone(), Expr::bvar(1)),
                                                            b,
                                                        ],
                                                    ),
                                                ),
                                            )
                                        },
                                    ),
                                ),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        }
    }

    fn nat_right_distrib_theorem() -> Decl {
        Decl::Theorem {
            name: "Nat.right_distrib".to_owned(),
            universe_params: Vec::new(),
            ty: Expr::pi(
                "a",
                nat(),
                Expr::pi(
                    "b",
                    nat(),
                    Expr::pi(
                        "c",
                        nat(),
                        nat_right_distrib_prop(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                    ),
                ),
            ),
            proof: Expr::lam(
                "a",
                nat(),
                Expr::lam(
                    "b",
                    nat(),
                    Expr::lam("c", nat(), {
                        let a = Expr::bvar(2);
                        let b = Expr::bvar(1);
                        let c = Expr::bvar(0);
                        let lhs = nat_mul(nat_add(a.clone(), b.clone()), c.clone());
                        let mid1 = nat_mul(c.clone(), nat_add(a.clone(), b.clone()));
                        let mid2 =
                            nat_add(nat_mul(c.clone(), a.clone()), nat_mul(c.clone(), b.clone()));
                        let mid3 =
                            nat_add(nat_mul(a.clone(), c.clone()), nat_mul(c.clone(), b.clone()));
                        let rhs =
                            nat_add(nat_mul(a.clone(), c.clone()), nat_mul(b.clone(), c.clone()));
                        eq_trans_nat(
                            lhs,
                            mid1.clone(),
                            rhs.clone(),
                            Expr::apps(
                                Expr::konst("Nat.mul_comm", vec![]),
                                vec![nat_add(a.clone(), b.clone()), c.clone()],
                            ),
                            eq_trans_nat(
                                mid1,
                                mid2.clone(),
                                rhs.clone(),
                                Expr::apps(
                                    Expr::konst("Nat.left_distrib", vec![]),
                                    vec![c.clone(), a.clone(), b.clone()],
                                ),
                                eq_trans_nat(
                                    mid2,
                                    mid3.clone(),
                                    rhs,
                                    eq_congr_add_right(
                                        nat_mul(c.clone(), b.clone()),
                                        nat_mul(c.clone(), a.clone()),
                                        nat_mul(a.clone(), c.clone()),
                                        Expr::apps(
                                            Expr::konst("Nat.mul_comm", vec![]),
                                            vec![c.clone(), a],
                                        ),
                                    ),
                                    eq_congr_add_left(
                                        nat_mul(Expr::bvar(2), Expr::bvar(0)),
                                        nat_mul(Expr::bvar(0), Expr::bvar(1)),
                                        nat_mul(Expr::bvar(1), Expr::bvar(0)),
                                        Expr::apps(
                                            Expr::konst("Nat.mul_comm", vec![]),
                                            vec![Expr::bvar(0), Expr::bvar(1)],
                                        ),
                                    ),
                                ),
                            ),
                        )
                    }),
                ),
            ),
        }
    }

    fn list_append_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.List"),
            declarations: list_append_declarations(),
        }
    }

    fn list_append_declarations() -> Vec<Decl> {
        vec![
            list_inductive_decl(),
            list_append_def(),
            list_nil_append_theorem(),
            list_cons_append_theorem(),
            list_append_nil_theorem(),
            list_append_assoc_theorem(),
            list_length_def(),
            list_length_nil_theorem(),
            list_length_cons_theorem(),
            list_length_append_theorem(),
            list_map_def(),
            list_map_nil_theorem(),
            list_map_cons_theorem(),
            list_map_id_theorem(),
            list_map_comp_theorem(),
            list_foldr_def(),
            list_foldr_nil_theorem(),
            list_foldr_cons_theorem(),
        ]
    }

    fn list_inductive_decl() -> Decl {
        let u = Level::param("u");
        Decl::Inductive {
            name: "List".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi("A", Expr::sort(u.clone()), Expr::sort(u)),
            data: Box::new(list_inductive_with_rec()),
        }
    }

    fn list_inductive_with_rec() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "List",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![
                ConstructorDecl::new("List.nil", list_nil_type(u.clone())),
                ConstructorDecl::new("List.cons", list_cons_type(u.clone())),
            ],
            Some(RecursorDecl::new(
                "List.rec",
                vec!["u".to_owned(), "v".to_owned()],
                list_rec_type(u, Level::param("v")),
            )),
        )
    }

    fn list_nil_type(u: Level) -> Expr {
        Expr::pi("A", Expr::sort(u.clone()), list(u, Expr::bvar(0)))
    }

    fn list_cons_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "x",
                Expr::bvar(0),
                Expr::pi("xs", list(u.clone(), Expr::bvar(1)), list(u, Expr::bvar(2))),
            ),
        )
    }

    fn list_rec_type(u: Level, v: Level) -> Expr {
        let motive_ty = Expr::pi("_", list(u.clone(), Expr::bvar(0)), Expr::sort(v));
        let nil_ty = Expr::app(Expr::bvar(0), list_nil(u.clone(), Expr::bvar(1)));
        let cons_ty = Expr::pi(
            "x",
            Expr::bvar(2),
            Expr::pi(
                "xs",
                list(u.clone(), Expr::bvar(3)),
                Expr::pi(
                    "ih",
                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                    Expr::app(
                        Expr::bvar(4),
                        list_cons(u.clone(), Expr::bvar(5), Expr::bvar(2), Expr::bvar(1)),
                    ),
                ),
            ),
        );

        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "motive",
                motive_ty,
                Expr::pi(
                    "nil",
                    nil_ty,
                    Expr::pi(
                        "cons",
                        cons_ty,
                        Expr::pi(
                            "xs",
                            list(u, Expr::bvar(3)),
                            Expr::app(Expr::bvar(3), Expr::bvar(0)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn list_append_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "List.append".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: list_append_type(u.clone()),
            value: list_append_value(u),
            reducibility: Reducibility::Reducible,
        }
    }

    fn list_append_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "xs",
                list(u.clone(), Expr::bvar(0)),
                Expr::pi("ys", list(u.clone(), Expr::bvar(1)), list(u, Expr::bvar(2))),
            ),
        )
    }

    fn list_append_value(u: Level) -> Expr {
        let motive = Expr::lam(
            "_",
            list(u.clone(), Expr::bvar(2)),
            list(u.clone(), Expr::bvar(3)),
        );
        let step = Expr::lam(
            "x",
            Expr::bvar(2),
            Expr::lam(
                "xs",
                list(u.clone(), Expr::bvar(3)),
                Expr::lam(
                    "ih",
                    list(u.clone(), Expr::bvar(4)),
                    list_cons(u.clone(), Expr::bvar(5), Expr::bvar(2), Expr::bvar(0)),
                ),
            ),
        );
        let rec = Expr::apps(
            Expr::konst("List.rec", vec![u.clone(), u.clone()]),
            vec![Expr::bvar(2), motive, Expr::bvar(0), step, Expr::bvar(1)],
        );
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "xs",
                list(u.clone(), Expr::bvar(0)),
                Expr::lam("ys", list(u, Expr::bvar(1)), rec),
            ),
        )
    }

    fn list_nil_append_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.nil_append".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("xs", list(u.clone(), Expr::bvar(0)), {
                    list_nil_append_prop(u.clone(), Expr::bvar(1), Expr::bvar(0))
                }),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    eq_refl(u.clone(), list(u, Expr::bvar(1)), Expr::bvar(0)),
                ),
            ),
        }
    }

    fn list_cons_append_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.cons_append".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "x",
                    Expr::bvar(0),
                    Expr::pi(
                        "xs",
                        list(u.clone(), Expr::bvar(1)),
                        Expr::pi("ys", list(u.clone(), Expr::bvar(2)), {
                            list_cons_append_prop(
                                u.clone(),
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(1),
                                Expr::bvar(0),
                            )
                        }),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "x",
                    Expr::bvar(0),
                    Expr::lam(
                        "xs",
                        list(u.clone(), Expr::bvar(1)),
                        Expr::lam(
                            "ys",
                            list(u.clone(), Expr::bvar(2)),
                            eq_refl(
                                u.clone(),
                                list(u.clone(), Expr::bvar(3)),
                                list_cons(
                                    u.clone(),
                                    Expr::bvar(3),
                                    Expr::bvar(2),
                                    list_append(
                                        u.clone(),
                                        Expr::bvar(3),
                                        Expr::bvar(1),
                                        Expr::bvar(0),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_append_nil_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.append_nil".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    list_append_nil_prop(u.clone(), Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::apps(
                        Expr::konst("List.rec", vec![u.clone(), Level::zero()]),
                        vec![
                            Expr::bvar(1),
                            Expr::lam(
                                "xs",
                                list(u.clone(), Expr::bvar(1)),
                                list_append_nil_prop(u.clone(), Expr::bvar(2), Expr::bvar(0)),
                            ),
                            eq_refl(
                                u.clone(),
                                list(u.clone(), Expr::bvar(1)),
                                list_nil(u.clone(), Expr::bvar(1)),
                            ),
                            Expr::lam(
                                "x",
                                Expr::bvar(1),
                                Expr::lam(
                                    "xs",
                                    list(u.clone(), Expr::bvar(2)),
                                    Expr::lam(
                                        "ih",
                                        list_append_nil_prop(
                                            u.clone(),
                                            Expr::bvar(3),
                                            Expr::bvar(0),
                                        ),
                                        eq_congr_list_cons_tail(
                                            u.clone(),
                                            Expr::bvar(4),
                                            Expr::bvar(2),
                                            list_append(
                                                u.clone(),
                                                Expr::bvar(4),
                                                Expr::bvar(1),
                                                list_nil(u.clone(), Expr::bvar(4)),
                                            ),
                                            Expr::bvar(1),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                ),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn list_append_assoc_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.append_assoc".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::pi(
                        "ys",
                        list(u.clone(), Expr::bvar(1)),
                        Expr::pi(
                            "zs",
                            list(u.clone(), Expr::bvar(2)),
                            list_append_assoc_prop(
                                u.clone(),
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(1),
                                Expr::bvar(0),
                            ),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::lam(
                        "ys",
                        list(u.clone(), Expr::bvar(1)),
                        Expr::lam(
                            "zs",
                            list(u.clone(), Expr::bvar(2)),
                            Expr::apps(
                                Expr::konst("List.rec", vec![u.clone(), Level::zero()]),
                                vec![
                                    Expr::bvar(3),
                                    Expr::lam(
                                        "xs",
                                        list(u.clone(), Expr::bvar(3)),
                                        list_append_assoc_prop(
                                            u.clone(),
                                            Expr::bvar(4),
                                            Expr::bvar(0),
                                            Expr::bvar(2),
                                            Expr::bvar(1),
                                        ),
                                    ),
                                    eq_refl(
                                        u.clone(),
                                        list(u.clone(), Expr::bvar(3)),
                                        list_append(
                                            u.clone(),
                                            Expr::bvar(3),
                                            Expr::bvar(1),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                    Expr::lam(
                                        "x",
                                        Expr::bvar(3),
                                        Expr::lam(
                                            "xs",
                                            list(u.clone(), Expr::bvar(4)),
                                            Expr::lam(
                                                "ih",
                                                list_append_assoc_prop(
                                                    u.clone(),
                                                    Expr::bvar(5),
                                                    Expr::bvar(0),
                                                    Expr::bvar(3),
                                                    Expr::bvar(2),
                                                ),
                                                eq_congr_list_cons_tail(
                                                    u.clone(),
                                                    Expr::bvar(6),
                                                    Expr::bvar(2),
                                                    list_append(
                                                        u.clone(),
                                                        Expr::bvar(6),
                                                        list_append(
                                                            u.clone(),
                                                            Expr::bvar(6),
                                                            Expr::bvar(1),
                                                            Expr::bvar(4),
                                                        ),
                                                        Expr::bvar(3),
                                                    ),
                                                    list_append(
                                                        u.clone(),
                                                        Expr::bvar(6),
                                                        Expr::bvar(1),
                                                        list_append(
                                                            u.clone(),
                                                            Expr::bvar(6),
                                                            Expr::bvar(4),
                                                            Expr::bvar(3),
                                                        ),
                                                    ),
                                                    Expr::bvar(0),
                                                ),
                                            ),
                                        ),
                                    ),
                                    Expr::bvar(2),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_length_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "List.length".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: list_length_type(u.clone()),
            value: list_length_value(u),
            reducibility: Reducibility::Reducible,
        }
    }

    fn list_length_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi("xs", list(u, Expr::bvar(0)), nat()),
        )
    }

    fn list_length_value(u: Level) -> Expr {
        let motive = Expr::lam("_", list(u.clone(), Expr::bvar(1)), nat());
        let step = Expr::lam(
            "_x",
            Expr::bvar(1),
            Expr::lam(
                "_xs",
                list(u.clone(), Expr::bvar(2)),
                Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))),
            ),
        );
        let rec = Expr::apps(
            Expr::konst("List.rec", vec![u.clone(), type0()]),
            vec![Expr::bvar(1), motive, nat_zero(), step, Expr::bvar(0)],
        );
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam("xs", list(u, Expr::bvar(0)), rec),
        )
    }

    fn list_length_nil_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.length_nil".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                list_length_nil_prop(u.clone(), Expr::bvar(0)),
            ),
            proof: Expr::lam("A", Expr::sort(u), eq_refl(type0(), nat(), nat_zero())),
        }
    }

    fn list_length_cons_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.length_cons".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "x",
                    Expr::bvar(0),
                    Expr::pi(
                        "xs",
                        list(u.clone(), Expr::bvar(1)),
                        list_length_cons_prop(
                            u.clone(),
                            Expr::bvar(2),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "x",
                    Expr::bvar(0),
                    Expr::lam(
                        "xs",
                        list(u.clone(), Expr::bvar(1)),
                        eq_refl(
                            type0(),
                            nat(),
                            nat_succ(list_length(u, Expr::bvar(2), Expr::bvar(0))),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_length_append_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.length_append".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::pi(
                        "ys",
                        list(u.clone(), Expr::bvar(1)),
                        list_length_append_prop(
                            u.clone(),
                            Expr::bvar(2),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::lam(
                        "ys",
                        list(u.clone(), Expr::bvar(1)),
                        Expr::apps(
                            Expr::konst("List.rec", vec![u.clone(), Level::zero()]),
                            vec![
                                Expr::bvar(2),
                                Expr::lam(
                                    "xs",
                                    list(u.clone(), Expr::bvar(2)),
                                    list_length_append_prop(
                                        u.clone(),
                                        Expr::bvar(3),
                                        Expr::bvar(0),
                                        Expr::bvar(1),
                                    ),
                                ),
                                {
                                    let len_ys =
                                        list_length(u.clone(), Expr::bvar(2), Expr::bvar(0));
                                    eq_symm_nat(
                                        nat_add(nat_zero(), len_ys.clone()),
                                        len_ys.clone(),
                                        Expr::app(Expr::konst("Nat.zero_add", vec![]), len_ys),
                                    )
                                },
                                Expr::lam(
                                    "x",
                                    Expr::bvar(2),
                                    Expr::lam(
                                        "xs",
                                        list(u.clone(), Expr::bvar(3)),
                                        Expr::lam(
                                            "ih",
                                            list_length_append_prop(
                                                u.clone(),
                                                Expr::bvar(4),
                                                Expr::bvar(0),
                                                Expr::bvar(2),
                                            ),
                                            {
                                                let a = Expr::bvar(5);
                                                let ys = Expr::bvar(3);
                                                let xs = Expr::bvar(1);
                                                let len_append = list_length(
                                                    u.clone(),
                                                    a.clone(),
                                                    list_append(
                                                        u.clone(),
                                                        a.clone(),
                                                        xs.clone(),
                                                        ys.clone(),
                                                    ),
                                                );
                                                let len_xs =
                                                    list_length(u.clone(), a.clone(), xs.clone());
                                                let len_ys =
                                                    list_length(u.clone(), a.clone(), ys.clone());
                                                let lhs = nat_succ(len_append.clone());
                                                let mid = nat_succ(nat_add(
                                                    len_xs.clone(),
                                                    len_ys.clone(),
                                                ));
                                                let rhs = nat_add(
                                                    nat_succ(len_xs.clone()),
                                                    len_ys.clone(),
                                                );
                                                eq_trans_nat(
                                                    lhs,
                                                    mid.clone(),
                                                    rhs.clone(),
                                                    eq_congr_succ(
                                                        len_append,
                                                        nat_add(len_xs.clone(), len_ys.clone()),
                                                        Expr::bvar(0),
                                                    ),
                                                    eq_symm_nat(
                                                        rhs,
                                                        mid,
                                                        Expr::apps(
                                                            Expr::konst("Nat.succ_add", vec![]),
                                                            vec![len_xs, len_ys],
                                                        ),
                                                    ),
                                                )
                                            },
                                        ),
                                    ),
                                ),
                                Expr::bvar(1),
                            ],
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_map_def() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Def {
            name: "List.map".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: list_map_type(u.clone(), v.clone()),
            value: list_map_value(u, v),
            reducibility: Reducibility::Reducible,
        }
    }

    fn list_map_type(u: Level, v: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "B",
                Expr::sort(v.clone()),
                Expr::pi(
                    "f",
                    Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                    Expr::pi("xs", list(u, Expr::bvar(2)), list(v, Expr::bvar(2))),
                ),
            ),
        )
    }

    fn list_map_value(u: Level, v: Level) -> Expr {
        let motive = Expr::lam(
            "_",
            list(u.clone(), Expr::bvar(3)),
            list(v.clone(), Expr::bvar(3)),
        );
        let step = Expr::lam(
            "x",
            Expr::bvar(3),
            Expr::lam(
                "_xs",
                list(u.clone(), Expr::bvar(4)),
                Expr::lam(
                    "ih",
                    list(v.clone(), Expr::bvar(4)),
                    list_cons(
                        v.clone(),
                        Expr::bvar(5),
                        Expr::app(Expr::bvar(4), Expr::bvar(2)),
                        Expr::bvar(0),
                    ),
                ),
            ),
        );
        let rec = Expr::apps(
            Expr::konst("List.rec", vec![u.clone(), v.clone()]),
            vec![
                Expr::bvar(3),
                motive,
                list_nil(v.clone(), Expr::bvar(2)),
                step,
                Expr::bvar(0),
            ],
        );
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "B",
                Expr::sort(v.clone()),
                Expr::lam(
                    "f",
                    Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                    Expr::lam("xs", list(u, Expr::bvar(2)), rec),
                ),
            ),
        )
    }

    fn list_map_nil_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Theorem {
            name: "List.map_nil".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                        list_map_nil_prop(
                            u.clone(),
                            v.clone(),
                            Expr::bvar(2),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::lam(
                        "f",
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                        eq_refl(
                            v.clone(),
                            list(v.clone(), Expr::bvar(1)),
                            list_nil(v, Expr::bvar(1)),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_map_cons_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Theorem {
            name: "List.map_cons".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                        Expr::pi(
                            "x",
                            Expr::bvar(2),
                            Expr::pi(
                                "xs",
                                list(u.clone(), Expr::bvar(3)),
                                list_map_cons_prop(
                                    u.clone(),
                                    v.clone(),
                                    Expr::bvar(4),
                                    Expr::bvar(3),
                                    Expr::bvar(2),
                                    Expr::bvar(1),
                                    Expr::bvar(0),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::lam(
                        "f",
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                        Expr::lam(
                            "x",
                            Expr::bvar(2),
                            Expr::lam(
                                "xs",
                                list(u.clone(), Expr::bvar(3)),
                                eq_refl(
                                    v.clone(),
                                    list(v.clone(), Expr::bvar(3)),
                                    list_cons(
                                        v.clone(),
                                        Expr::bvar(3),
                                        Expr::app(Expr::bvar(2), Expr::bvar(1)),
                                        list_map(
                                            u.clone(),
                                            v.clone(),
                                            Expr::bvar(4),
                                            Expr::bvar(3),
                                            Expr::bvar(2),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_map_id_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "List.map_id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    list_map_id_prop(u.clone(), Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "xs",
                    list(u.clone(), Expr::bvar(0)),
                    Expr::apps(
                        Expr::konst("List.rec", vec![u.clone(), Level::zero()]),
                        vec![
                            Expr::bvar(1),
                            Expr::lam(
                                "xs",
                                list(u.clone(), Expr::bvar(1)),
                                list_map_id_prop(u.clone(), Expr::bvar(2), Expr::bvar(0)),
                            ),
                            eq_refl(
                                u.clone(),
                                list(u.clone(), Expr::bvar(1)),
                                list_nil(u.clone(), Expr::bvar(1)),
                            ),
                            Expr::lam(
                                "x",
                                Expr::bvar(1),
                                Expr::lam(
                                    "xs",
                                    list(u.clone(), Expr::bvar(2)),
                                    Expr::lam(
                                        "ih",
                                        list_map_id_prop(u.clone(), Expr::bvar(3), Expr::bvar(0)),
                                        eq_congr_list_cons_tail(
                                            u.clone(),
                                            Expr::bvar(4),
                                            Expr::bvar(2),
                                            list_map_id(u.clone(), Expr::bvar(4), Expr::bvar(1)),
                                            Expr::bvar(1),
                                            Expr::bvar(0),
                                        ),
                                    ),
                                ),
                            ),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        }
    }

    fn list_map_comp_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        let w = Level::param("w");
        Decl::Theorem {
            name: "List.map_comp".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::pi(
                        "C",
                        Expr::sort(w.clone()),
                        Expr::pi(
                            "f",
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                            Expr::pi(
                                "g",
                                Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                Expr::pi(
                                    "xs",
                                    list(u.clone(), Expr::bvar(4)),
                                    list_map_comp_prop(
                                        u.clone(),
                                        v.clone(),
                                        w.clone(),
                                        Expr::bvar(5),
                                        Expr::bvar(4),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        Expr::bvar(1),
                                        Expr::bvar(0),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::lam(
                        "C",
                        Expr::sort(w.clone()),
                        Expr::lam(
                            "f",
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(1)),
                            Expr::lam(
                                "g",
                                Expr::pi("_", Expr::bvar(3), Expr::bvar(3)),
                                Expr::lam(
                                    "xs",
                                    list(u.clone(), Expr::bvar(4)),
                                    Expr::apps(
                                        Expr::konst("List.rec", vec![u.clone(), Level::zero()]),
                                        vec![
                                            Expr::bvar(5),
                                            Expr::lam(
                                                "xs",
                                                list(u.clone(), Expr::bvar(5)),
                                                list_map_comp_prop(
                                                    u.clone(),
                                                    v.clone(),
                                                    w.clone(),
                                                    Expr::bvar(6),
                                                    Expr::bvar(5),
                                                    Expr::bvar(4),
                                                    Expr::bvar(3),
                                                    Expr::bvar(2),
                                                    Expr::bvar(0),
                                                ),
                                            ),
                                            eq_refl(
                                                w.clone(),
                                                list(w.clone(), Expr::bvar(3)),
                                                list_nil(w.clone(), Expr::bvar(3)),
                                            ),
                                            Expr::lam(
                                                "x",
                                                Expr::bvar(5),
                                                Expr::lam(
                                                    "xs",
                                                    list(u.clone(), Expr::bvar(6)),
                                                    Expr::lam(
                                                        "ih",
                                                        list_map_comp_prop(
                                                            u.clone(),
                                                            v.clone(),
                                                            w.clone(),
                                                            Expr::bvar(7),
                                                            Expr::bvar(6),
                                                            Expr::bvar(5),
                                                            Expr::bvar(4),
                                                            Expr::bvar(3),
                                                            Expr::bvar(0),
                                                        ),
                                                        {
                                                            let a = Expr::bvar(8);
                                                            let b = Expr::bvar(7);
                                                            let c = Expr::bvar(6);
                                                            let f = Expr::bvar(5);
                                                            let g = Expr::bvar(4);
                                                            let x = Expr::bvar(2);
                                                            let xs = Expr::bvar(1);
                                                            let tail_lhs = list_map(
                                                                v.clone(),
                                                                w.clone(),
                                                                b.clone(),
                                                                c.clone(),
                                                                f.clone(),
                                                                list_map(
                                                                    u.clone(),
                                                                    v.clone(),
                                                                    a.clone(),
                                                                    b.clone(),
                                                                    g.clone(),
                                                                    xs.clone(),
                                                                ),
                                                            );
                                                            let tail_rhs = list_map(
                                                                u.clone(),
                                                                w.clone(),
                                                                a.clone(),
                                                                c.clone(),
                                                                compose_fn(a, f.clone(), g.clone()),
                                                                xs,
                                                            );
                                                            let head =
                                                                Expr::app(f, Expr::app(g, x));
                                                            eq_congr_list_cons_tail(
                                                                w.clone(),
                                                                c,
                                                                head,
                                                                tail_lhs,
                                                                tail_rhs,
                                                                Expr::bvar(0),
                                                            )
                                                        },
                                                    ),
                                                ),
                                            ),
                                            Expr::bvar(0),
                                        ],
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_foldr_def() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Def {
            name: "List.foldr".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: list_foldr_type(u.clone(), v.clone()),
            value: list_foldr_value(u, v),
            reducibility: Reducibility::Reducible,
        }
    }

    fn list_foldr_type(u: Level, v: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "B",
                Expr::sort(v.clone()),
                Expr::pi(
                    "f",
                    Expr::pi(
                        "_",
                        Expr::bvar(1),
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                    ),
                    Expr::pi(
                        "init",
                        Expr::bvar(1),
                        Expr::pi("xs", list(u, Expr::bvar(3)), Expr::bvar(3)),
                    ),
                ),
            ),
        )
    }

    fn list_foldr_value(u: Level, v: Level) -> Expr {
        let motive = Expr::lam("_", list(u.clone(), Expr::bvar(4)), Expr::bvar(4));
        let step = Expr::lam(
            "x",
            Expr::bvar(4),
            Expr::lam(
                "_xs",
                list(u.clone(), Expr::bvar(5)),
                Expr::lam(
                    "ih",
                    Expr::bvar(5),
                    Expr::apps(Expr::bvar(5), vec![Expr::bvar(2), Expr::bvar(0)]),
                ),
            ),
        );
        let rec = Expr::apps(
            Expr::konst("List.rec", vec![u.clone(), v.clone()]),
            vec![Expr::bvar(4), motive, Expr::bvar(1), step, Expr::bvar(0)],
        );
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "B",
                Expr::sort(v.clone()),
                Expr::lam(
                    "f",
                    Expr::pi(
                        "_",
                        Expr::bvar(1),
                        Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                    ),
                    Expr::lam(
                        "init",
                        Expr::bvar(1),
                        Expr::lam("xs", list(u, Expr::bvar(3)), rec),
                    ),
                ),
            ),
        )
    }

    fn list_foldr_nil_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Theorem {
            name: "List.foldr_nil".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi(
                            "_",
                            Expr::bvar(1),
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                        ),
                        Expr::pi(
                            "init",
                            Expr::bvar(1),
                            list_foldr_nil_prop(
                                u.clone(),
                                v.clone(),
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(1),
                                Expr::bvar(0),
                            ),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::lam(
                        "f",
                        Expr::pi(
                            "_",
                            Expr::bvar(1),
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                        ),
                        Expr::lam(
                            "init",
                            Expr::bvar(1),
                            eq_refl(v, Expr::bvar(2), Expr::bvar(0)),
                        ),
                    ),
                ),
            ),
        }
    }

    fn list_foldr_cons_theorem() -> Decl {
        let u = Level::param("u");
        let v = Level::param("v");
        Decl::Theorem {
            name: "List.foldr_cons".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi(
                            "_",
                            Expr::bvar(1),
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                        ),
                        Expr::pi(
                            "init",
                            Expr::bvar(1),
                            Expr::pi(
                                "x",
                                Expr::bvar(3),
                                Expr::pi(
                                    "xs",
                                    list(u.clone(), Expr::bvar(4)),
                                    list_foldr_cons_prop(
                                        u.clone(),
                                        v.clone(),
                                        Expr::bvar(5),
                                        Expr::bvar(4),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        Expr::bvar(1),
                                        Expr::bvar(0),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            proof: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "B",
                    Expr::sort(v.clone()),
                    Expr::lam(
                        "f",
                        Expr::pi(
                            "_",
                            Expr::bvar(1),
                            Expr::pi("_", Expr::bvar(1), Expr::bvar(2)),
                        ),
                        Expr::lam(
                            "init",
                            Expr::bvar(1),
                            Expr::lam(
                                "x",
                                Expr::bvar(3),
                                Expr::lam(
                                    "xs",
                                    list(u.clone(), Expr::bvar(4)),
                                    eq_refl(
                                        v.clone(),
                                        Expr::bvar(4),
                                        Expr::apps(
                                            Expr::bvar(3),
                                            vec![
                                                Expr::bvar(1),
                                                list_foldr(
                                                    u.clone(),
                                                    v.clone(),
                                                    Expr::bvar(5),
                                                    Expr::bvar(4),
                                                    Expr::bvar(3),
                                                    Expr::bvar(2),
                                                    Expr::bvar(0),
                                                ),
                                            ],
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        }
    }

    fn algebra_basic_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Algebra.Basic"),
            declarations: algebra_basic_declarations(),
        }
    }

    fn algebra_basic_declarations() -> Vec<Decl> {
        vec![
            associative_def(),
            commutative_def(),
            left_identity_def(),
            right_identity_def(),
            is_semigroup_inductive_decl(),
            is_monoid_inductive_decl(),
            is_comm_monoid_inductive_decl(),
            is_monoid_assoc_theorem(),
            is_monoid_left_id_theorem(),
            is_monoid_right_id_theorem(),
            is_comm_monoid_assoc_theorem(),
            is_comm_monoid_comm_theorem(),
            is_comm_monoid_left_id_theorem(),
            is_comm_monoid_right_id_theorem(),
            identity_unique_theorem(),
        ]
    }

    fn associative_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "Associative".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("op", binary_op_type(Expr::bvar(0)), prop_sort()),
            ),
            value: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "op",
                    binary_op_type(Expr::bvar(0)),
                    Expr::pi(
                        "a",
                        Expr::bvar(1),
                        Expr::pi(
                            "b",
                            Expr::bvar(2),
                            Expr::pi(
                                "c",
                                Expr::bvar(3),
                                eq(
                                    u.clone(),
                                    Expr::bvar(4),
                                    binary_op(
                                        Expr::bvar(3),
                                        binary_op(Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)),
                                        Expr::bvar(0),
                                    ),
                                    binary_op(
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        binary_op(Expr::bvar(3), Expr::bvar(1), Expr::bvar(0)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            reducibility: Reducibility::Reducible,
        }
    }

    fn commutative_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "Commutative".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("op", binary_op_type(Expr::bvar(0)), prop_sort()),
            ),
            value: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "op",
                    binary_op_type(Expr::bvar(0)),
                    Expr::pi(
                        "a",
                        Expr::bvar(1),
                        Expr::pi(
                            "b",
                            Expr::bvar(2),
                            eq(
                                u.clone(),
                                Expr::bvar(3),
                                binary_op(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                                binary_op(Expr::bvar(2), Expr::bvar(0), Expr::bvar(1)),
                            ),
                        ),
                    ),
                ),
            ),
            reducibility: Reducibility::Reducible,
        }
    }

    fn left_identity_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "LeftIdentity".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "e",
                    Expr::bvar(0),
                    Expr::pi("op", binary_op_type(Expr::bvar(1)), prop_sort()),
                ),
            ),
            value: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "e",
                    Expr::bvar(0),
                    Expr::lam(
                        "op",
                        binary_op_type(Expr::bvar(1)),
                        Expr::pi(
                            "a",
                            Expr::bvar(2),
                            eq(
                                u.clone(),
                                Expr::bvar(3),
                                binary_op(Expr::bvar(1), Expr::bvar(2), Expr::bvar(0)),
                                Expr::bvar(0),
                            ),
                        ),
                    ),
                ),
            ),
            reducibility: Reducibility::Reducible,
        }
    }

    fn right_identity_def() -> Decl {
        let u = Level::param("u");
        Decl::Def {
            name: "RightIdentity".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "e",
                    Expr::bvar(0),
                    Expr::pi("op", binary_op_type(Expr::bvar(1)), prop_sort()),
                ),
            ),
            value: Expr::lam(
                "A",
                Expr::sort(u.clone()),
                Expr::lam(
                    "e",
                    Expr::bvar(0),
                    Expr::lam(
                        "op",
                        binary_op_type(Expr::bvar(1)),
                        Expr::pi(
                            "a",
                            Expr::bvar(2),
                            eq(
                                u.clone(),
                                Expr::bvar(3),
                                binary_op(Expr::bvar(1), Expr::bvar(0), Expr::bvar(2)),
                                Expr::bvar(0),
                            ),
                        ),
                    ),
                ),
            ),
            reducibility: Reducibility::Reducible,
        }
    }

    fn is_semigroup_inductive_decl() -> Decl {
        let u = Level::param("u");
        Decl::Inductive {
            name: "IsSemigroup".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("op", binary_op_type(Expr::bvar(0)), prop_sort()),
            ),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "IsSemigroup",
                vec!["u".to_owned()],
                vec![
                    Binder::new("A", Expr::sort(u.clone())),
                    Binder::new("op", binary_op_type(Expr::bvar(0))),
                ],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "IsSemigroup.intro",
                    is_semigroup_intro_type(u),
                )],
                None,
            ))),
        }
    }

    fn is_semigroup_intro_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::pi(
                    "assoc",
                    associative(u.clone(), Expr::bvar(1), Expr::bvar(0)),
                    is_semigroup(u, Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        )
    }

    fn is_monoid_inductive_decl() -> Decl {
        let u = Level::param("u");
        Decl::Inductive {
            name: "IsMonoid".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "op",
                    binary_op_type(Expr::bvar(0)),
                    Expr::pi("e", Expr::bvar(1), prop_sort()),
                ),
            ),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "IsMonoid",
                vec!["u".to_owned()],
                vec![
                    Binder::new("A", Expr::sort(u.clone())),
                    Binder::new("op", binary_op_type(Expr::bvar(0))),
                    Binder::new("e", Expr::bvar(1)),
                ],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "IsMonoid.intro",
                    is_monoid_intro_type(u),
                )],
                None,
            ))),
        }
    }

    fn is_monoid_intro_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::pi(
                    "e",
                    Expr::bvar(1),
                    Expr::pi(
                        "assoc",
                        associative(u.clone(), Expr::bvar(2), Expr::bvar(1)),
                        Expr::pi(
                            "left_id",
                            left_identity(u.clone(), Expr::bvar(3), Expr::bvar(1), Expr::bvar(2)),
                            Expr::pi(
                                "right_id",
                                right_identity(
                                    u.clone(),
                                    Expr::bvar(4),
                                    Expr::bvar(2),
                                    Expr::bvar(3),
                                ),
                                is_monoid(u, Expr::bvar(5), Expr::bvar(4), Expr::bvar(3)),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn is_comm_monoid_inductive_decl() -> Decl {
        let u = Level::param("u");
        Decl::Inductive {
            name: "IsCommMonoid".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "op",
                    binary_op_type(Expr::bvar(0)),
                    Expr::pi("e", Expr::bvar(1), prop_sort()),
                ),
            ),
            data: Box::new(generated_mvp_inductive(InductiveDecl::new(
                "IsCommMonoid",
                vec!["u".to_owned()],
                vec![
                    Binder::new("A", Expr::sort(u.clone())),
                    Binder::new("op", binary_op_type(Expr::bvar(0))),
                    Binder::new("e", Expr::bvar(1)),
                ],
                Vec::new(),
                Level::zero(),
                vec![ConstructorDecl::new(
                    "IsCommMonoid.intro",
                    is_comm_monoid_intro_type(u),
                )],
                None,
            ))),
        }
    }

    fn is_comm_monoid_intro_type(u: Level) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::pi(
                    "e",
                    Expr::bvar(1),
                    Expr::pi(
                        "assoc",
                        associative(u.clone(), Expr::bvar(2), Expr::bvar(1)),
                        Expr::pi(
                            "comm",
                            commutative(u.clone(), Expr::bvar(3), Expr::bvar(2)),
                            Expr::pi(
                                "left_id",
                                left_identity(
                                    u.clone(),
                                    Expr::bvar(4),
                                    Expr::bvar(2),
                                    Expr::bvar(3),
                                ),
                                Expr::pi(
                                    "right_id",
                                    right_identity(
                                        u.clone(),
                                        Expr::bvar(5),
                                        Expr::bvar(3),
                                        Expr::bvar(4),
                                    ),
                                    is_comm_monoid(u, Expr::bvar(6), Expr::bvar(5), Expr::bvar(4)),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn is_monoid_assoc_theorem() -> Decl {
        algebra_monoid_projection_theorem("IsMonoid.assoc", MonoidProjection::Assoc)
    }

    fn is_monoid_left_id_theorem() -> Decl {
        algebra_monoid_projection_theorem("IsMonoid.left_id", MonoidProjection::LeftId)
    }

    fn is_monoid_right_id_theorem() -> Decl {
        algebra_monoid_projection_theorem("IsMonoid.right_id", MonoidProjection::RightId)
    }

    fn is_comm_monoid_assoc_theorem() -> Decl {
        algebra_comm_monoid_projection_theorem("IsCommMonoid.assoc", CommMonoidProjection::Assoc)
    }

    fn is_comm_monoid_comm_theorem() -> Decl {
        algebra_comm_monoid_projection_theorem("IsCommMonoid.comm", CommMonoidProjection::Comm)
    }

    fn is_comm_monoid_left_id_theorem() -> Decl {
        algebra_comm_monoid_projection_theorem("IsCommMonoid.left_id", CommMonoidProjection::LeftId)
    }

    fn is_comm_monoid_right_id_theorem() -> Decl {
        algebra_comm_monoid_projection_theorem(
            "IsCommMonoid.right_id",
            CommMonoidProjection::RightId,
        )
    }

    #[derive(Clone, Copy)]
    enum MonoidProjection {
        Assoc,
        LeftId,
        RightId,
    }

    #[derive(Clone, Copy)]
    enum CommMonoidProjection {
        Assoc,
        Comm,
        LeftId,
        RightId,
    }

    fn algebra_monoid_projection_theorem(name: &str, projection: MonoidProjection) -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: name.to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: algebra_monoid_projection_type(u.clone(), projection),
            proof: algebra_monoid_projection_proof(u, projection),
        }
    }

    fn algebra_monoid_projection_type(u: Level, projection: MonoidProjection) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::pi(
                    "e",
                    Expr::bvar(1),
                    Expr::pi(
                        "h",
                        is_monoid(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        monoid_projection_target(
                            u,
                            projection,
                            Expr::bvar(3),
                            Expr::bvar(2),
                            Expr::bvar(1),
                        ),
                    ),
                ),
            ),
        )
    }

    fn algebra_monoid_projection_proof(u: Level, projection: MonoidProjection) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::lam(
                    "e",
                    Expr::bvar(1),
                    Expr::lam(
                        "h",
                        is_monoid(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        Expr::apps(
                            Expr::konst("IsMonoid.rec", vec![u.clone()]),
                            vec![
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(1),
                                Expr::lam(
                                    "_",
                                    is_monoid(
                                        u.clone(),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        Expr::bvar(1),
                                    ),
                                    monoid_projection_target(
                                        u.clone(),
                                        projection,
                                        Expr::bvar(4),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                    ),
                                ),
                                algebra_monoid_projection_minor(u.clone(), projection),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        )
    }

    fn monoid_projection_target(
        u: Level,
        projection: MonoidProjection,
        a: Expr,
        op: Expr,
        e: Expr,
    ) -> Expr {
        match projection {
            MonoidProjection::Assoc => associative(u, a, op),
            MonoidProjection::LeftId => left_identity(u, a, e, op),
            MonoidProjection::RightId => right_identity(u, a, e, op),
        }
    }

    fn algebra_monoid_projection_minor(u: Level, projection: MonoidProjection) -> Expr {
        Expr::lam(
            "assoc",
            associative(u.clone(), Expr::bvar(3), Expr::bvar(2)),
            Expr::lam(
                "left_id",
                left_identity(u.clone(), Expr::bvar(4), Expr::bvar(2), Expr::bvar(3)),
                Expr::lam(
                    "right_id",
                    right_identity(u, Expr::bvar(5), Expr::bvar(3), Expr::bvar(4)),
                    match projection {
                        MonoidProjection::Assoc => Expr::bvar(2),
                        MonoidProjection::LeftId => Expr::bvar(1),
                        MonoidProjection::RightId => Expr::bvar(0),
                    },
                ),
            ),
        )
    }

    fn algebra_comm_monoid_projection_theorem(
        name: &str,
        projection: CommMonoidProjection,
    ) -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: name.to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: algebra_comm_monoid_projection_type(u.clone(), projection),
            proof: algebra_comm_monoid_projection_proof(u, projection),
        }
    }

    fn algebra_comm_monoid_projection_type(u: Level, projection: CommMonoidProjection) -> Expr {
        Expr::pi(
            "A",
            Expr::sort(u.clone()),
            Expr::pi(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::pi(
                    "e",
                    Expr::bvar(1),
                    Expr::pi(
                        "h",
                        is_comm_monoid(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        comm_monoid_projection_target(
                            u,
                            projection,
                            Expr::bvar(3),
                            Expr::bvar(2),
                            Expr::bvar(1),
                        ),
                    ),
                ),
            ),
        )
    }

    fn algebra_comm_monoid_projection_proof(u: Level, projection: CommMonoidProjection) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::lam(
                    "e",
                    Expr::bvar(1),
                    Expr::lam(
                        "h",
                        is_comm_monoid(u.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                        Expr::apps(
                            Expr::konst("IsCommMonoid.rec", vec![u.clone()]),
                            vec![
                                Expr::bvar(3),
                                Expr::bvar(2),
                                Expr::bvar(1),
                                Expr::lam(
                                    "_",
                                    is_comm_monoid(
                                        u.clone(),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                        Expr::bvar(1),
                                    ),
                                    comm_monoid_projection_target(
                                        u.clone(),
                                        projection,
                                        Expr::bvar(4),
                                        Expr::bvar(3),
                                        Expr::bvar(2),
                                    ),
                                ),
                                algebra_comm_monoid_projection_minor(u.clone(), projection),
                                Expr::bvar(0),
                            ],
                        ),
                    ),
                ),
            ),
        )
    }

    fn comm_monoid_projection_target(
        u: Level,
        projection: CommMonoidProjection,
        a: Expr,
        op: Expr,
        e: Expr,
    ) -> Expr {
        match projection {
            CommMonoidProjection::Assoc => associative(u, a, op),
            CommMonoidProjection::Comm => commutative(u, a, op),
            CommMonoidProjection::LeftId => left_identity(u, a, e, op),
            CommMonoidProjection::RightId => right_identity(u, a, e, op),
        }
    }

    fn algebra_comm_monoid_projection_minor(u: Level, projection: CommMonoidProjection) -> Expr {
        Expr::lam(
            "assoc",
            associative(u.clone(), Expr::bvar(3), Expr::bvar(2)),
            Expr::lam(
                "comm",
                commutative(u.clone(), Expr::bvar(4), Expr::bvar(3)),
                Expr::lam(
                    "left_id",
                    left_identity(u.clone(), Expr::bvar(5), Expr::bvar(3), Expr::bvar(4)),
                    Expr::lam(
                        "right_id",
                        right_identity(u, Expr::bvar(6), Expr::bvar(4), Expr::bvar(5)),
                        match projection {
                            CommMonoidProjection::Assoc => Expr::bvar(3),
                            CommMonoidProjection::Comm => Expr::bvar(2),
                            CommMonoidProjection::LeftId => Expr::bvar(1),
                            CommMonoidProjection::RightId => Expr::bvar(0),
                        },
                    ),
                ),
            ),
        )
    }

    fn identity_unique_theorem() -> Decl {
        let u = Level::param("u");
        Decl::Theorem {
            name: "identity_unique".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "op",
                    binary_op_type(Expr::bvar(0)),
                    Expr::pi(
                        "e1",
                        Expr::bvar(1),
                        Expr::pi(
                            "e2",
                            Expr::bvar(2),
                            Expr::pi(
                                "h1",
                                left_identity(
                                    u.clone(),
                                    Expr::bvar(3),
                                    Expr::bvar(1),
                                    Expr::bvar(2),
                                ),
                                Expr::pi(
                                    "h2",
                                    right_identity(
                                        u.clone(),
                                        Expr::bvar(4),
                                        Expr::bvar(1),
                                        Expr::bvar(3),
                                    ),
                                    eq(u.clone(), Expr::bvar(5), Expr::bvar(3), Expr::bvar(2)),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            proof: identity_unique_proof(u),
        }
    }

    fn identity_unique_proof(u: Level) -> Expr {
        Expr::lam(
            "A",
            Expr::sort(u.clone()),
            Expr::lam(
                "op",
                binary_op_type(Expr::bvar(0)),
                Expr::lam(
                    "e1",
                    Expr::bvar(1),
                    Expr::lam(
                        "e2",
                        Expr::bvar(2),
                        Expr::lam(
                            "h1",
                            left_identity(u.clone(), Expr::bvar(3), Expr::bvar(1), Expr::bvar(2)),
                            Expr::lam(
                                "h2",
                                right_identity(
                                    u.clone(),
                                    Expr::bvar(4),
                                    Expr::bvar(1),
                                    Expr::bvar(3),
                                ),
                                {
                                    let a = Expr::bvar(5);
                                    let op = Expr::bvar(4);
                                    let e1 = Expr::bvar(3);
                                    let e2 = Expr::bvar(2);
                                    let h1 = Expr::bvar(1);
                                    let h2 = Expr::bvar(0);
                                    let mid = binary_op(op.clone(), e1.clone(), e2.clone());
                                    let h2_e1 = Expr::app(h2, e1.clone());
                                    let h1_e2 = Expr::app(h1, e2.clone());
                                    eq_trans_general(
                                        u.clone(),
                                        a.clone(),
                                        e1.clone(),
                                        mid.clone(),
                                        e2,
                                        eq_symm_general(u.clone(), a, mid.clone(), e1, h2_e1),
                                        h1_e2,
                                    )
                                },
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn nat_add_zero_prop(n: Expr) -> Expr {
        eq(type0(), nat(), nat_add(n.clone(), nat_zero()), n)
    }

    fn nat_zero_add_prop(n: Expr) -> Expr {
        eq(type0(), nat(), nat_add(nat_zero(), n.clone()), n)
    }

    fn nat_succ_add_prop(n: Expr, m: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_add(nat_succ(n.clone()), m.clone()),
            nat_succ(nat_add(n, m)),
        )
    }

    fn nat_add_assoc_prop(a: Expr, b: Expr, c: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_add(nat_add(a.clone(), b.clone()), c.clone()),
            nat_add(a, nat_add(b, c)),
        )
    }

    fn nat_add_comm_prop(a: Expr, b: Expr) -> Expr {
        eq(type0(), nat(), nat_add(a.clone(), b.clone()), nat_add(b, a))
    }

    fn nat_mul_zero_prop(n: Expr) -> Expr {
        eq(type0(), nat(), nat_mul(n, nat_zero()), nat_zero())
    }

    fn nat_zero_mul_prop(n: Expr) -> Expr {
        eq(type0(), nat(), nat_mul(nat_zero(), n), nat_zero())
    }

    fn nat_succ_mul_prop(n: Expr, m: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_mul(nat_succ(n.clone()), m.clone()),
            nat_add(m.clone(), nat_mul(n, m)),
        )
    }

    fn nat_mul_comm_prop(a: Expr, b: Expr) -> Expr {
        eq(type0(), nat(), nat_mul(a.clone(), b.clone()), nat_mul(b, a))
    }

    fn nat_left_distrib_prop(a: Expr, b: Expr, c: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_mul(a.clone(), nat_add(b.clone(), c.clone())),
            nat_add(nat_mul(a.clone(), b), nat_mul(a, c)),
        )
    }

    fn nat_mul_assoc_prop(a: Expr, b: Expr, c: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_mul(nat_mul(a.clone(), b.clone()), c.clone()),
            nat_mul(a, nat_mul(b, c)),
        )
    }

    fn nat_right_distrib_prop(a: Expr, b: Expr, c: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            nat_mul(nat_add(a.clone(), b.clone()), c.clone()),
            nat_add(nat_mul(a, c.clone()), nat_mul(b, c)),
        )
    }

    fn list_nil_append_prop(u: Level, a: Expr, xs: Expr) -> Expr {
        eq(
            u.clone(),
            list(u.clone(), a.clone()),
            list_append(u.clone(), a.clone(), list_nil(u.clone(), a), xs.clone()),
            xs,
        )
    }

    fn list_cons_append_prop(u: Level, a: Expr, x: Expr, xs: Expr, ys: Expr) -> Expr {
        eq(
            u.clone(),
            list(u.clone(), a.clone()),
            list_append(
                u.clone(),
                a.clone(),
                list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
                ys.clone(),
            ),
            list_cons(u.clone(), a.clone(), x, list_append(u, a, xs, ys)),
        )
    }

    fn list_append_nil_prop(u: Level, a: Expr, xs: Expr) -> Expr {
        eq(
            u.clone(),
            list(u.clone(), a.clone()),
            list_append(u.clone(), a.clone(), xs.clone(), list_nil(u.clone(), a)),
            xs,
        )
    }

    fn list_append_assoc_prop(u: Level, a: Expr, xs: Expr, ys: Expr, zs: Expr) -> Expr {
        eq(
            u.clone(),
            list(u.clone(), a.clone()),
            list_append(
                u.clone(),
                a.clone(),
                list_append(u.clone(), a.clone(), xs.clone(), ys.clone()),
                zs.clone(),
            ),
            list_append(u.clone(), a.clone(), xs, list_append(u, a, ys, zs)),
        )
    }

    fn list_length_nil_prop(u: Level, a: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            list_length(u.clone(), a.clone(), list_nil(u, a)),
            nat_zero(),
        )
    }

    fn list_length_cons_prop(u: Level, a: Expr, x: Expr, xs: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            list_length(
                u.clone(),
                a.clone(),
                list_cons(u.clone(), a.clone(), x, xs.clone()),
            ),
            nat_succ(list_length(u, a, xs)),
        )
    }

    fn list_length_append_prop(u: Level, a: Expr, xs: Expr, ys: Expr) -> Expr {
        eq(
            type0(),
            nat(),
            list_length(
                u.clone(),
                a.clone(),
                list_append(u.clone(), a.clone(), xs.clone(), ys.clone()),
            ),
            nat_add(list_length(u.clone(), a.clone(), xs), list_length(u, a, ys)),
        )
    }

    fn list_map_nil_prop(u: Level, v: Level, a: Expr, b: Expr, f: Expr) -> Expr {
        eq(
            v.clone(),
            list(v.clone(), b.clone()),
            list_map(
                u.clone(),
                v.clone(),
                a.clone(),
                b.clone(),
                f,
                list_nil(u, a),
            ),
            list_nil(v, b),
        )
    }

    fn list_map_cons_prop(
        u: Level,
        v: Level,
        a: Expr,
        b: Expr,
        f: Expr,
        x: Expr,
        xs: Expr,
    ) -> Expr {
        eq(
            v.clone(),
            list(v.clone(), b.clone()),
            list_map(
                u.clone(),
                v.clone(),
                a.clone(),
                b.clone(),
                f.clone(),
                list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
            ),
            list_cons(
                v.clone(),
                b.clone(),
                Expr::app(f.clone(), x),
                list_map(u, v, a, b, f, xs),
            ),
        )
    }

    fn list_map_id_prop(u: Level, a: Expr, xs: Expr) -> Expr {
        eq(
            u.clone(),
            list(u.clone(), a.clone()),
            list_map_id(u.clone(), a, xs.clone()),
            xs,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn list_map_comp_prop(
        u: Level,
        v: Level,
        w: Level,
        a: Expr,
        b: Expr,
        c: Expr,
        f: Expr,
        g: Expr,
        xs: Expr,
    ) -> Expr {
        eq(
            w.clone(),
            list(w.clone(), c.clone()),
            list_map(
                v.clone(),
                w.clone(),
                b.clone(),
                c.clone(),
                f.clone(),
                list_map(
                    u.clone(),
                    v.clone(),
                    a.clone(),
                    b.clone(),
                    g.clone(),
                    xs.clone(),
                ),
            ),
            list_map(u, w, a.clone(), c, compose_fn(a, f, g), xs),
        )
    }

    fn list_foldr_nil_prop(u: Level, v: Level, a: Expr, b: Expr, f: Expr, init: Expr) -> Expr {
        eq(
            v.clone(),
            b.clone(),
            list_foldr(
                u.clone(),
                v.clone(),
                a.clone(),
                b.clone(),
                f,
                init.clone(),
                list_nil(u, a),
            ),
            init,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn list_foldr_cons_prop(
        u: Level,
        v: Level,
        a: Expr,
        b: Expr,
        f: Expr,
        init: Expr,
        x: Expr,
        xs: Expr,
    ) -> Expr {
        eq(
            v.clone(),
            b.clone(),
            list_foldr(
                u.clone(),
                v.clone(),
                a.clone(),
                b.clone(),
                f.clone(),
                init.clone(),
                list_cons(u.clone(), a.clone(), x.clone(), xs.clone()),
            ),
            Expr::apps(f.clone(), vec![x, list_foldr(u, v, a, b, f, init, xs)]),
        )
    }

    fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst("Nat.add", vec![]), vec![lhs, rhs])
    }

    fn nat_mul(lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst("Nat.mul", vec![]), vec![lhs, rhs])
    }

    fn list(u: Level, elem_ty: Expr) -> Expr {
        Expr::app(Expr::konst("List", vec![u]), elem_ty)
    }

    fn list_nil(u: Level, elem_ty: Expr) -> Expr {
        Expr::app(Expr::konst("List.nil", vec![u]), elem_ty)
    }

    fn list_cons(u: Level, elem_ty: Expr, head: Expr, tail: Expr) -> Expr {
        Expr::apps(Expr::konst("List.cons", vec![u]), vec![elem_ty, head, tail])
    }

    fn list_append(u: Level, elem_ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst("List.append", vec![u]), vec![elem_ty, lhs, rhs])
    }

    fn list_length(u: Level, elem_ty: Expr, xs: Expr) -> Expr {
        Expr::apps(Expr::konst("List.length", vec![u]), vec![elem_ty, xs])
    }

    fn list_map(u: Level, v: Level, src_ty: Expr, dst_ty: Expr, f: Expr, xs: Expr) -> Expr {
        Expr::apps(
            Expr::konst("List.map", vec![u, v]),
            vec![src_ty, dst_ty, f, xs],
        )
    }

    fn list_map_id(u: Level, elem_ty: Expr, xs: Expr) -> Expr {
        list_map(
            u.clone(),
            u.clone(),
            elem_ty.clone(),
            elem_ty.clone(),
            identity_fn(elem_ty),
            xs,
        )
    }

    fn list_foldr(
        u: Level,
        v: Level,
        elem_ty: Expr,
        acc_ty: Expr,
        f: Expr,
        init: Expr,
        xs: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::konst("List.foldr", vec![u, v]),
            vec![elem_ty, acc_ty, f, init, xs],
        )
    }

    fn binary_op_type(a: Expr) -> Expr {
        Expr::pi(
            "_",
            a.clone(),
            Expr::pi("_", shift_expr(a.clone(), 1), shift_expr(a, 2)),
        )
    }

    fn binary_op(op: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(op, vec![lhs, rhs])
    }

    fn associative(u: Level, elem_ty: Expr, op: Expr) -> Expr {
        Expr::apps(Expr::konst("Associative", vec![u]), vec![elem_ty, op])
    }

    fn commutative(u: Level, elem_ty: Expr, op: Expr) -> Expr {
        Expr::apps(Expr::konst("Commutative", vec![u]), vec![elem_ty, op])
    }

    fn left_identity(u: Level, elem_ty: Expr, e: Expr, op: Expr) -> Expr {
        Expr::apps(Expr::konst("LeftIdentity", vec![u]), vec![elem_ty, e, op])
    }

    fn right_identity(u: Level, elem_ty: Expr, e: Expr, op: Expr) -> Expr {
        Expr::apps(Expr::konst("RightIdentity", vec![u]), vec![elem_ty, e, op])
    }

    fn is_semigroup(u: Level, elem_ty: Expr, op: Expr) -> Expr {
        Expr::apps(Expr::konst("IsSemigroup", vec![u]), vec![elem_ty, op])
    }

    fn is_monoid(u: Level, elem_ty: Expr, op: Expr, e: Expr) -> Expr {
        Expr::apps(Expr::konst("IsMonoid", vec![u]), vec![elem_ty, op, e])
    }

    fn is_comm_monoid(u: Level, elem_ty: Expr, op: Expr, e: Expr) -> Expr {
        Expr::apps(Expr::konst("IsCommMonoid", vec![u]), vec![elem_ty, op, e])
    }

    fn identity_fn(elem_ty: Expr) -> Expr {
        Expr::lam("x", elem_ty, Expr::bvar(0))
    }

    fn compose_fn(domain_ty: Expr, f: Expr, g: Expr) -> Expr {
        Expr::lam(
            "x",
            domain_ty,
            Expr::app(shift_expr(f, 1), Expr::app(shift_expr(g, 1), Expr::bvar(0))),
        )
    }

    fn eq_congr_succ(lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(
            Expr::konst("Eq.congrArg", vec![type0(), type0()]),
            vec![
                nat(),
                nat(),
                Expr::lam("x", nat(), nat_succ(Expr::bvar(0))),
                lhs,
                rhs,
                proof,
            ],
        )
    }

    fn eq_congr_add_right(addend: Expr, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(
            Expr::konst("Eq.congrArg", vec![type0(), type0()]),
            vec![
                nat(),
                nat(),
                Expr::lam("x", nat(), nat_add(Expr::bvar(0), shift_expr(addend, 1))),
                lhs,
                rhs,
                proof,
            ],
        )
    }

    fn eq_congr_add_left(addend: Expr, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(
            Expr::konst("Eq.congrArg", vec![type0(), type0()]),
            vec![
                nat(),
                nat(),
                Expr::lam("x", nat(), nat_add(shift_expr(addend, 1), Expr::bvar(0))),
                lhs,
                rhs,
                proof,
            ],
        )
    }

    fn eq_congr_list_cons_tail(
        u: Level,
        elem_ty: Expr,
        head: Expr,
        lhs_tail: Expr,
        rhs_tail: Expr,
        proof: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::konst("Eq.congrArg", vec![u.clone(), u.clone()]),
            vec![
                list(u.clone(), elem_ty.clone()),
                list(u.clone(), elem_ty.clone()),
                Expr::lam(
                    "tail",
                    list(u.clone(), elem_ty.clone()),
                    list_cons(
                        u,
                        shift_expr(elem_ty, 1),
                        shift_expr(head, 1),
                        Expr::bvar(0),
                    ),
                ),
                lhs_tail,
                rhs_tail,
                proof,
            ],
        )
    }

    fn eq_symm_nat(lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(
            Expr::konst("Eq.symm", vec![type0()]),
            vec![nat(), lhs, rhs, proof],
        )
    }

    fn eq_symm_general(u: Level, ty: Expr, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
        Expr::apps(Expr::konst("Eq.symm", vec![u]), vec![ty, lhs, rhs, proof])
    }

    fn eq_trans_nat(lhs: Expr, mid: Expr, rhs: Expr, left: Expr, right: Expr) -> Expr {
        Expr::apps(
            Expr::konst("Eq.trans", vec![type0()]),
            vec![nat(), lhs, mid, rhs, left, right],
        )
    }

    fn eq_trans_general(
        u: Level,
        ty: Expr,
        lhs: Expr,
        mid: Expr,
        rhs: Expr,
        left: Expr,
        right: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::konst("Eq.trans", vec![u]),
            vec![ty, lhs, mid, rhs, left, right],
        )
    }

    fn shift_expr(expr: Expr, amount: i32) -> Expr {
        npa_kernel::subst::shift(&expr, amount, 0).unwrap()
    }

    fn nat_m5_profile_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.Nat"),
            declarations: nat_basic_declarations(),
        }
    }

    fn list_m5_profile_module() -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Std.List"),
            declarations: list_append_declarations(),
        }
    }

    fn empty_axiom_report_for(loaded: &MachineStdLoadedRelease) -> MachineStdAxiomReport {
        MachineStdAxiomReport {
            library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
            modules: loaded
                .modules()
                .iter()
                .map(|module| MachineStdModuleAxiomReport {
                    module: module.module.clone(),
                    export_hash: module.expected_export_hash,
                    certificate_hash: module.expected_certificate_hash,
                    module_axioms: Vec::new(),
                    transitive_axioms: Vec::new(),
                })
                .collect(),
            axiom_report_hash: [0; 32],
        }
    }

    fn mvp_axiom_report_for(loaded: &MachineStdLoadedRelease) -> MachineStdAxiomReport {
        let mut reports_by_module = BTreeMap::new();
        let mut expected_transitive_by_module: BTreeMap<Name, Vec<MachineStdAxiomRef>> =
            BTreeMap::new();

        for module_name in loaded.verification_order() {
            let loaded_module = loaded.module(module_name).unwrap();
            let module_axioms = project_module_axioms(loaded, loaded_module).unwrap();
            let mut transitive = BTreeMap::new();
            for axiom in &module_axioms {
                transitive.insert(
                    machine_std_axiom_ref_canonical_bytes(axiom).unwrap(),
                    axiom.clone(),
                );
            }
            for import in &loaded_module.imports {
                for axiom in expected_transitive_by_module.get(&import.module).unwrap() {
                    transitive.insert(
                        machine_std_axiom_ref_canonical_bytes(axiom).unwrap(),
                        axiom.clone(),
                    );
                }
            }
            let transitive_axioms = transitive.into_values().collect::<Vec<_>>();
            expected_transitive_by_module.insert(module_name.clone(), transitive_axioms.clone());
            reports_by_module.insert(
                module_name.clone(),
                MachineStdModuleAxiomReport {
                    module: loaded_module.module.clone(),
                    export_hash: loaded_module.expected_export_hash,
                    certificate_hash: loaded_module.expected_certificate_hash,
                    module_axioms,
                    transitive_axioms,
                },
            );
        }

        let mut report = MachineStdAxiomReport {
            library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
            modules: loaded
                .modules()
                .iter()
                .map(|module| reports_by_module.remove(&module.module).unwrap())
                .collect(),
            axiom_report_hash: [0; 32],
        };
        report.axiom_report_hash = machine_std_axiom_report_hash(&report).unwrap();
        report
    }

    fn theorem_index_entry<'a>(
        theorem_index: &'a MachineStdTheoremIndex,
        name: &str,
    ) -> &'a MachineStdTheoremEntry {
        theorem_index
            .entries
            .iter()
            .find(|entry| entry.global_ref.name == Name::from_dotted(name))
            .unwrap()
    }

    fn theorem_index_entry_index(theorem_index: &MachineStdTheoremIndex, name: &str) -> usize {
        theorem_index
            .entries
            .iter()
            .position(|entry| entry.global_ref.name == Name::from_dotted(name))
            .unwrap()
    }

    fn human_theorem_search_entry<'a>(
        view: &'a HumanStdTheoremSearchView,
        name: &str,
    ) -> &'a HumanStdTheoremSearchEntry {
        view.entries
            .iter()
            .find(|entry| entry.global_ref.name == Name::from_dotted(name))
            .unwrap()
    }

    fn human_module_debug_view<'a>(
        views: &'a [HumanStdModuleDebugViews],
        module: &str,
    ) -> &'a HumanStdModuleDebugViews {
        views
            .iter()
            .find(|view| view.module == Name::from_dotted(module))
            .unwrap()
    }

    fn module_artifact<'a>(
        release: &'a MachineStdLibraryRelease,
        module: &str,
    ) -> &'a MachineStdModuleArtifact {
        release
            .modules
            .iter()
            .find(|artifact| artifact.module == Name::from_dotted(module))
            .unwrap()
    }

    fn module_artifact_mut<'a>(
        release: &'a mut MachineStdLibraryRelease,
        module: &str,
    ) -> &'a mut MachineStdModuleArtifact {
        release
            .modules
            .iter_mut()
            .find(|artifact| artifact.module == Name::from_dotted(module))
            .unwrap()
    }

    fn assert_nat_family_matches_std_nat_exports(
        loaded: &MachineStdLoadedRelease,
        family: &NatFamilyRef,
    ) {
        let nat_module = loaded.module(&Name::from_dotted("Std.Nat")).unwrap();
        assert_eq!(family.nat_name, Name::from_dotted("Nat"));
        assert_eq!(
            family.nat_interface_hash,
            export_entry(nat_module, "Nat").decl_interface_hash
        );
        assert_eq!(family.zero_name, Name::from_dotted("Nat.zero"));
        assert_eq!(
            family.zero_interface_hash,
            export_entry(nat_module, "Nat.zero").decl_interface_hash
        );
        assert_eq!(family.succ_name, Name::from_dotted("Nat.succ"));
        assert_eq!(
            family.succ_interface_hash,
            export_entry(nat_module, "Nat.succ").decl_interface_hash
        );
        assert_eq!(family.rec_name, Name::from_dotted("Nat.rec"));
        assert_eq!(
            family.rec_interface_hash,
            export_entry(nat_module, "Nat.rec").decl_interface_hash
        );
    }

    fn apply_final_sidecar_counts(
        release: &mut MachineStdLibraryRelease,
        theorem_index: &MachineStdTheoremIndex,
        simp_profiles: &MachineStdSimpProfileSet,
        rewrite_profiles: &MachineStdRewriteProfileSet,
    ) {
        let mut theorem_counts = BTreeMap::<Name, u64>::new();
        for entry in &theorem_index.entries {
            *theorem_counts
                .entry(entry.global_ref.module.clone())
                .or_default() += 1;
        }
        let simp_counts = simp_rule_counts_by_module(simp_profiles, rewrite_profiles).unwrap();
        for artifact in &mut release.modules {
            artifact.theorem_index_entry_count =
                *theorem_counts.get(&artifact.module).unwrap_or(&0);
            artifact.simp_rule_count = *simp_counts.get(&artifact.module).unwrap_or(&0);
        }
    }

    fn export_entry<'a>(module: &'a MachineStdLoadedModule, name: &str) -> &'a ExportEntry {
        module
            .verified_module
            .export_block()
            .iter()
            .find(|entry| {
                module
                    .verified_module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|entry_name| *entry_name == Name::from_dotted(name))
            })
            .unwrap()
    }

    fn rewrite_profile<'a>(
        profile_set: &'a MachineStdRewriteProfileSet,
        profile_id: &str,
    ) -> &'a MachineStdRewriteProfile {
        profile_set
            .profiles
            .iter()
            .find(|profile| profile.profile_id == profile_id)
            .unwrap()
    }

    fn simp_profile<'a>(
        profile_set: &'a MachineStdSimpProfileSet,
        profile_id: &str,
    ) -> &'a MachineStdSimpProfile {
        profile_set
            .profiles
            .iter()
            .find(|profile| profile.profile_id == profile_id)
            .unwrap()
    }

    fn human_source_simp_intent(profile_id: &str) -> BTreeSet<String> {
        match profile_id {
            STD_NAT_SIMP_PROFILE_ID => string_set(&[
                "Nat.add_zero",
                "Nat.add_succ",
                "Nat.zero_add",
                "Nat.mul_zero",
                "Nat.mul_succ",
                "Nat.zero_mul",
                "Nat.pred_zero",
                "Nat.pred_succ",
            ]),
            STD_LIST_SIMP_PROFILE_ID => string_set(&[
                "List.nil_append",
                "List.cons_append",
                "List.append_nil",
                "List.length_nil",
                "List.length_cons",
                "List.map_nil",
                "List.map_cons",
                "List.map_id",
                "List.foldr_nil",
                "List.foldr_cons",
            ]),
            STD_LOGIC_SIMP_PROFILE_ID => BTreeSet::new(),
            STD_ALL_SIMP_PROFILE_ID => {
                let mut rules = human_source_simp_intent(STD_NAT_SIMP_PROFILE_ID);
                rules.extend(human_source_simp_intent(STD_LIST_SIMP_PROFILE_ID));
                rules
            }
            _ => panic!("unexpected simp profile id: {profile_id}"),
        }
    }

    fn human_source_rw_only_intent(profile_id: &str) -> BTreeSet<String> {
        match profile_id {
            STD_NAT_RW_PROFILE_ID => string_set(&["Nat.add_comm", "Nat.add_assoc"]),
            STD_LIST_RW_PROFILE_ID => string_set(&["List.append_assoc", "List.length_append"]),
            STD_LOGIC_RW_PROFILE_ID => BTreeSet::new(),
            STD_ALL_RW_PROFILE_ID => {
                let mut rules = human_source_rw_only_intent(STD_NAT_RW_PROFILE_ID);
                rules.extend(human_source_rw_only_intent(STD_LIST_RW_PROFILE_ID));
                rules
            }
            _ => panic!("unexpected rewrite profile id: {profile_id}"),
        }
    }

    fn string_set(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn assert_doc_contains(doc: &str, needle: &str) {
        assert!(doc.contains(needle), "stdlib doc missing text: {needle}");
    }

    fn rewrite_profile_rule_names_by_safety(
        profile: &MachineStdRewriteProfile,
        safety: MachineStdRewriteSafety,
    ) -> BTreeSet<String> {
        profile
            .descriptors
            .iter()
            .filter(|descriptor| descriptor.safety == safety)
            .map(|descriptor| descriptor.source.name.as_dotted())
            .collect()
    }

    fn simp_profile_rule_names(profile: &MachineStdSimpProfile) -> BTreeSet<String> {
        profile
            .rules
            .iter()
            .map(|rule| rule.name.as_dotted())
            .collect()
    }

    fn simp_profile_rule_source_modules(
        profile: &MachineStdSimpProfile,
        paired_profile: &MachineStdRewriteProfile,
    ) -> BTreeSet<String> {
        profile
            .rules
            .iter()
            .map(|rule| {
                paired_simp_descriptor(rule, paired_profile)
                    .source
                    .module
                    .as_dotted()
            })
            .collect()
    }

    fn paired_simp_descriptor<'a>(
        rule: &SimpRuleRef,
        paired_profile: &'a MachineStdRewriteProfile,
    ) -> &'a MachineStdRewriteDescriptor {
        paired_profile
            .descriptors
            .iter()
            .find(|descriptor| {
                descriptor.safety == MachineStdRewriteSafety::SimpSafe
                    && descriptor.source.name == rule.name
                    && descriptor.source.decl_interface_hash == rule.decl_interface_hash
                    && descriptor.direction == rule.direction
            })
            .unwrap()
    }

    fn canonical_rewrite_descriptor_sequence(profile: &MachineStdRewriteProfile) -> Vec<Vec<u8>> {
        profile
            .descriptors
            .iter()
            .map(|descriptor| machine_std_rewrite_descriptor_canonical_bytes(descriptor).unwrap())
            .collect()
    }

    fn canonical_rewrite_descriptor_union(profiles: &[&MachineStdRewriteProfile]) -> Vec<Vec<u8>> {
        profiles
            .iter()
            .flat_map(|profile| &profile.descriptors)
            .map(|descriptor| machine_std_rewrite_descriptor_canonical_bytes(descriptor).unwrap())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    fn canonical_simp_rule_sequence(profile: &MachineStdSimpProfile) -> Vec<Vec<u8>> {
        profile
            .rules
            .iter()
            .map(|rule| simp_rule_ref_canonical_bytes(rule).unwrap())
            .collect()
    }

    fn canonical_simp_rule_union(profiles: &[&MachineStdSimpProfile]) -> Vec<Vec<u8>> {
        profiles
            .iter()
            .flat_map(|profile| &profile.rules)
            .map(|rule| simp_rule_ref_canonical_bytes(rule).unwrap())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    fn simp_rule_target_map(
        profile: &MachineStdSimpProfile,
        paired_profile: &MachineStdRewriteProfile,
    ) -> BTreeMap<Vec<u8>, MachineStdGlobalRef> {
        profile
            .rules
            .iter()
            .map(|rule| {
                (
                    simp_rule_ref_canonical_bytes(rule).unwrap(),
                    paired_simp_descriptor(rule, paired_profile).source.clone(),
                )
            })
            .collect()
    }

    fn refresh_theorem_index_hash(theorem_index: &mut MachineStdTheoremIndex) {
        theorem_index.index_hash = machine_std_theorem_index_hash(theorem_index).unwrap();
    }

    fn prompt_metadata_entry(
        global_ref: MachineStdGlobalRef,
        imports_bundle_id: &str,
        candidate_kind: &str,
        tags: &[&str],
    ) -> MachineStdPromptMetadata {
        MachineStdPromptMetadata {
            global_ref,
            short_doc: Some("display-only theorem metadata".to_owned()),
            examples: vec![MachineStdPromptExample {
                goal_core_hash: test_hash(171),
                imports_bundle_id: imports_bundle_id.to_owned(),
                candidate_kind: candidate_kind.to_owned(),
                display: candidate_kind.to_owned(),
            }],
            tags: tags.iter().map(|tag| (*tag).to_owned()).collect(),
        }
    }

    fn prompt_metadata_set_for_entries(
        entries: Vec<MachineStdPromptMetadata>,
    ) -> MachineStdPromptMetadataSet {
        let mut metadata = MachineStdPromptMetadataSet {
            metadata_profile_id: STD_PROMPT_METADATA_PROFILE_ID.to_owned(),
            library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
            entries,
            prompt_metadata_hash: [0; 32],
        };
        refresh_prompt_metadata_hash(&mut metadata);
        metadata
    }

    fn refresh_prompt_metadata_hash(metadata: &mut MachineStdPromptMetadataSet) {
        metadata.prompt_metadata_hash = machine_std_prompt_metadata_hash(metadata).unwrap();
    }

    fn release_manifest_for(
        loaded: &MachineStdLoadedRelease,
        axiom_report_hash: Hash,
    ) -> MachineStdLibraryRelease {
        let import_bundles_hash = generate_machine_std_mvp_import_bundle_set(loaded)
            .unwrap()
            .import_bundles_hash;
        MachineStdLibraryRelease {
            protocol_version: STD_LIBRARY_PROTOCOL_VERSION.to_owned(),
            library_profile_id: STD_LIBRARY_PROFILE_ID.to_owned(),
            core_spec_id: STD_CORE_SPEC_ID.to_owned(),
            kernel_semantics_profile_id: STD_KERNEL_SEMANTICS_PROFILE_ID.to_owned(),
            modules: loaded
                .modules()
                .iter()
                .map(|module| MachineStdModuleArtifact {
                    module: module.module.clone(),
                    expected_export_hash: module.expected_export_hash,
                    expected_certificate_hash: module.expected_certificate_hash,
                    certificate_encoding: STD_CERTIFICATE_ENCODING.to_owned(),
                    certificate_bytes_hash: module.certificate_bytes_hash,
                    axiom_report_hash: module.axiom_report_hash,
                    public_export_count: module.verified_module.export_block().len() as u64,
                    theorem_index_entry_count: module
                        .verified_module
                        .export_block()
                        .iter()
                        .filter(|entry| {
                            matches!(entry.kind, ExportKind::Theorem | ExportKind::Axiom)
                        })
                        .count() as u64,
                    simp_rule_count: 0,
                })
                .collect(),
            import_bundles_hash,
            theorem_index_hash: test_hash(2),
            simp_profiles_hash: test_hash(3),
            rewrite_profiles_hash: test_hash(4),
            axiom_report_hash,
        }
    }

    fn release_manifest_for_final_sidecars(
        loaded: &MachineStdLoadedRelease,
        axiom_report_hash: Hash,
        import_bundles: &MachineStdImportBundleSet,
        theorem_index: &MachineStdTheoremIndex,
        simp_profiles: &MachineStdSimpProfileSet,
        rewrite_profiles: &MachineStdRewriteProfileSet,
    ) -> MachineStdLibraryRelease {
        let mut release = release_manifest_for(loaded, axiom_report_hash);
        release.import_bundles_hash = import_bundles.import_bundles_hash;
        release.theorem_index_hash = theorem_index.index_hash;
        release.simp_profiles_hash = simp_profiles.simp_profiles_hash;
        release.rewrite_profiles_hash = rewrite_profiles.rewrite_profiles_hash;
        apply_final_sidecar_counts(&mut release, theorem_index, simp_profiles, rewrite_profiles);
        release
    }

    fn final_sidecar_artifacts_for_loaded(
        loaded: &MachineStdLoadedRelease,
    ) -> (
        MachineStdLibraryRelease,
        MachineStdImportBundleSet,
        MachineStdTheoremIndex,
        MachineStdRewriteProfileSet,
        MachineStdSimpProfileSet,
        MachineStdAxiomReport,
    ) {
        let rewrite_profiles = generate_machine_std_mvp_rewrite_profile_set(loaded).unwrap();
        let simp_profiles =
            generate_machine_std_mvp_simp_profile_set(loaded, &rewrite_profiles).unwrap();
        let import_bundles =
            generate_machine_std_mvp_final_import_bundle_set(loaded, &simp_profiles).unwrap();
        let theorem_index =
            generate_machine_std_mvp_final_theorem_index(loaded, &rewrite_profiles, &simp_profiles)
                .unwrap();
        let axiom_report = mvp_axiom_report_for(loaded);
        let release = release_manifest_for_final_sidecars(
            loaded,
            axiom_report.axiom_report_hash,
            &import_bundles,
            &theorem_index,
            &simp_profiles,
            &rewrite_profiles,
        );
        (
            release,
            import_bundles,
            theorem_index,
            rewrite_profiles,
            simp_profiles,
            axiom_report,
        )
    }

    fn write_machine_std_release_sidecars(
        root: &Path,
        release: &MachineStdLibraryRelease,
        import_bundles: &MachineStdImportBundleSet,
        theorem_index: &MachineStdTheoremIndex,
        rewrite_profiles: &MachineStdRewriteProfileSet,
        simp_profiles: &MachineStdSimpProfileSet,
        axiom_report: &MachineStdAxiomReport,
    ) {
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_RELEASE_JSON_PATH),
            release_manifest_json(release),
        )
        .unwrap();
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_IMPORT_BUNDLES_JSON_PATH),
            import_bundle_set_json(import_bundles),
        )
        .unwrap();
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_THEOREM_INDEX_JSON_PATH),
            theorem_index_json(theorem_index),
        )
        .unwrap();
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_REWRITE_PROFILES_JSON_PATH),
            rewrite_profile_set_json(rewrite_profiles),
        )
        .unwrap();
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_SIMP_PROFILES_JSON_PATH),
            simp_profile_set_json(simp_profiles),
        )
        .unwrap();
        fs::write(
            join_posix_relative_path(root, STD_MACHINE_AXIOM_REPORT_JSON_PATH),
            axiom_report_json(axiom_report),
        )
        .unwrap();
    }

    fn release_manifest_json(release: &MachineStdLibraryRelease) -> String {
        format!(
            "{{\"protocol_version\":\"{}\",\"library_profile_id\":\"{}\",\"core_spec_id\":\"{}\",\"kernel_semantics_profile_id\":\"{}\",\"modules\":[{}],\"import_bundles_hash\":\"{}\",\"theorem_index_hash\":\"{}\",\"simp_profiles_hash\":\"{}\",\"rewrite_profiles_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}",
            release.protocol_version,
            release.library_profile_id,
            release.core_spec_id,
            release.kernel_semantics_profile_id,
            release
                .modules
                .iter()
                .map(module_artifact_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&release.import_bundles_hash),
            format_hash_string(&release.theorem_index_hash),
            format_hash_string(&release.simp_profiles_hash),
            format_hash_string(&release.rewrite_profiles_hash),
            format_hash_string(&release.axiom_report_hash),
        )
    }

    fn module_artifact_json(module: &MachineStdModuleArtifact) -> String {
        format!(
            "{{\"module\":\"{}\",\"expected_export_hash\":\"{}\",\"expected_certificate_hash\":\"{}\",\"certificate_encoding\":\"{}\",\"certificate_bytes_hash\":\"{}\",\"axiom_report_hash\":\"{}\",\"public_export_count\":{},\"theorem_index_entry_count\":{},\"simp_rule_count\":{}}}",
            module.module.as_dotted(),
            format_hash_string(&module.expected_export_hash),
            format_hash_string(&module.expected_certificate_hash),
            module.certificate_encoding,
            format_hash_string(&module.certificate_bytes_hash),
            format_hash_string(&module.axiom_report_hash),
            module.public_export_count,
            module.theorem_index_entry_count,
            module.simp_rule_count,
        )
    }

    fn axiom_report_json(report: &MachineStdAxiomReport) -> String {
        format!(
            "{{\"library_profile_id\":\"{}\",\"modules\":[{}],\"axiom_report_hash\":\"{}\"}}",
            report.library_profile_id,
            report
                .modules
                .iter()
                .map(module_axiom_report_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&report.axiom_report_hash),
        )
    }

    fn module_axiom_report_json(module: &MachineStdModuleAxiomReport) -> String {
        format!(
            "{{\"module\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\",\"module_axioms\":[{}],\"transitive_axioms\":[{}]}}",
            module.module.as_dotted(),
            format_hash_string(&module.export_hash),
            format_hash_string(&module.certificate_hash),
            module
                .module_axioms
                .iter()
                .map(axiom_ref_json)
                .collect::<Vec<_>>()
                .join(","),
            module
                .transitive_axioms
                .iter()
                .map(axiom_ref_json)
                .collect::<Vec<_>>()
                .join(","),
        )
    }

    fn axiom_ref_json(axiom: &MachineStdAxiomRef) -> String {
        format!(
            "{{\"module\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"decl_interface_hash\":\"{}\"}}",
            axiom.module.as_dotted(),
            axiom.name.as_dotted(),
            format_hash_string(&axiom.export_hash),
            format_hash_string(&axiom.decl_interface_hash),
        )
    }

    fn import_bundle_set_json(bundle_set: &MachineStdImportBundleSet) -> String {
        format!(
            "{{\"library_profile_id\":\"{}\",\"bundles\":[{}],\"import_bundles_hash\":\"{}\"}}",
            bundle_set.library_profile_id,
            bundle_set
                .bundles
                .iter()
                .map(import_bundle_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&bundle_set.import_bundles_hash),
        )
    }

    fn import_bundle_json(bundle: &MachineStdImportBundle) -> String {
        format!(
            "{{\"bundle_id\":\"{}\",\"root_imports\":[{}],\"import_closure\":[{}],\"allow_axioms\":[{}],\"recommended_tactic_options\":{}}}",
            bundle.bundle_id,
            bundle
                .root_imports
                .iter()
                .map(import_key_json)
                .collect::<Vec<_>>()
                .join(","),
            bundle
                .import_closure
                .iter()
                .map(import_certificate_json)
                .collect::<Vec<_>>()
                .join(","),
            bundle
                .allow_axioms
                .iter()
                .map(machine_axiom_ref_wire_json)
                .collect::<Vec<_>>()
                .join(","),
            tactic_options_recipe_json(&bundle.recommended_tactic_options),
        )
    }

    fn import_key_json(key: &VerifiedImportKey) -> String {
        format!(
            "{{\"module\":\"{}\",\"expected_export_hash\":\"{}\",\"expected_certificate_hash\":\"{}\"}}",
            key.module.as_dotted(),
            format_hash_string(&key.export_hash),
            format_hash_string(&key.certificate_hash),
        )
    }

    fn import_certificate_json(certificate: &MachineStdImportCertificate) -> String {
        format!(
            "{{\"module\":\"{}\",\"expected_export_hash\":\"{}\",\"expected_certificate_hash\":\"{}\",\"certificate\":{{\"encoding\":\"{}\",\"bytes\":\"{}\"}}}}",
            certificate.module.as_dotted(),
            format_hash_string(&certificate.expected_export_hash),
            format_hash_string(&certificate.expected_certificate_hash),
            certificate.certificate_encoding,
            lower_hex_bytes(&certificate.certificate_bytes),
        )
    }

    fn session_create_json_for_bundle(bundle: &MachineStdImportBundle) -> String {
        session_create_json_for_bundle_with_theorem_type(bundle, "Prop")
    }

    fn session_create_json_for_bundle_with_theorem_type(
        bundle: &MachineStdImportBundle,
        theorem_type_source: &str,
    ) -> String {
        let allow_axioms_json = format!(
            "[{}]",
            bundle
                .allow_axioms
                .iter()
                .map(machine_axiom_ref_wire_json)
                .collect::<Vec<_>>()
                .join(",")
        );
        format!(
            r#"{{
              "protocol_version":"npa.machine-api.v1",
              "root":{{
                "module":"Scratch",
                "theorem_name":"Scratch.t",
                "source_index":0,
                "universe_params":[],
                "theorem_type":{{"format":"machine_surface_v1","source":"{}"}}
              }},
              "import_closure":[{}],
              "imports":[{}],
              "checked_current_decls":[],
              "options":{{
                "kernel_check_profile":"{}",
                "allow_axioms":{},
                "tactic_options":{}
              }}
            }}"#,
            theorem_type_source,
            bundle
                .import_closure
                .iter()
                .map(import_certificate_json)
                .collect::<Vec<_>>()
                .join(","),
            bundle
                .root_imports
                .iter()
                .map(import_key_json)
                .collect::<Vec<_>>()
                .join(","),
            bundle.recommended_tactic_options.kernel_check_profile,
            allow_axioms_json,
            tactic_options_request_json(&bundle.recommended_tactic_options),
        )
    }

    fn m8_search_json(session: &crate::MachineProofSession, filters: &str) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "modes":["apply","exact","rw","simp"],
              "limit":20,
              "filters":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            filters
        )
    }

    fn m8_apply_search_json(
        session: &crate::MachineProofSession,
        filters: &str,
        limit: u32,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "modes":["apply"],
              "limit":{},
              "filters":{}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            limit,
            filters
        )
    }

    fn m8_budget_json() -> &'static str {
        r#"{
          "max_tactic_steps":100,
          "max_whnf_steps":100,
          "max_conversion_steps":100,
          "max_rewrite_steps":100,
          "max_meta_allocations":8,
          "max_expr_nodes":20000
        }"#
    }

    fn m8_batch_json(session: &crate::MachineProofSession, candidates: &str) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "goal_id":"g0",
              "candidates":{},
              "deterministic_budget":{},
              "batch_policy":{{
                "max_evaluated_candidates":256,
                "stop_after_successes":256,
                "stop_after_failures":256
              }}
            }}"#,
            session.session_id.wire(),
            session.initial_snapshot.snapshot_id.wire(),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            candidates,
            m8_budget_json(),
        )
    }

    fn m8_batch_candidate_json(candidate_id: &str, candidate_json: &str) -> String {
        format!(r#"{{"candidate_id":"{candidate_id}","candidate":{candidate_json}}}"#)
    }

    fn m8_replay_step_json(
        previous_state_fingerprint: Hash,
        goal_id: GoalId,
        candidate: &str,
        candidate_hash: Hash,
        deterministic_budget_hash: Hash,
        proof_delta_hash: Hash,
        next_state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "previous_state_fingerprint":"{}",
              "goal_id":"{}",
              "candidate":{},
              "deterministic_budget":{},
              "candidate_hash":"{}",
              "deterministic_budget_hash":"{}",
              "proof_delta_hash":"{}",
              "next_state_fingerprint":"{}"
            }}"#,
            format_hash_string(&previous_state_fingerprint),
            format_goal_id_wire(goal_id),
            candidate,
            m8_budget_json(),
            format_hash_string(&candidate_hash),
            format_hash_string(&deterministic_budget_hash),
            format_hash_string(&proof_delta_hash),
            format_hash_string(&next_state_fingerprint),
        )
    }

    fn m8_replay_json(
        session: &crate::MachineProofSession,
        steps: &str,
        final_state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "plan":{{
                "protocol_version":"npa.machine-api.v1",
                "session_root_hash":"{}",
                "initial_state_fingerprint":"{}",
                "steps":{},
                "final_state_fingerprint":"{}"
              }}
            }}"#,
            session.session_id.wire(),
            format_hash_string(&session.session_root_hash),
            format_hash_string(&session.initial_snapshot.state_fingerprint),
            steps,
            format_hash_string(&final_state_fingerprint),
        )
    }

    fn m8_verify_json(
        session: &crate::MachineProofSession,
        snapshot_id: SnapshotId,
        state_fingerprint: Hash,
    ) -> String {
        format!(
            r#"{{
              "session_id":"{}",
              "snapshot_id":"{}",
              "state_fingerprint":"{}",
              "mode":"certificate"
            }}"#,
            session.session_id.wire(),
            snapshot_id.wire(),
            format_hash_string(&state_fingerprint),
        )
    }

    fn m8_suggested_candidate_json(candidate: &MachineTacticCandidate) -> String {
        match candidate {
            MachineTacticCandidate::Rewrite {
                rule,
                direction,
                site,
            } => {
                assert!(rule.universe_args.is_empty());
                format!(
                    r#"{{"kind":"rw","rule":{{"head":{},"universe_args":[],"args":[{}]}},"direction":"{}","site":"{}"}}"#,
                    m8_tactic_head_json(&rule.head),
                    rule.args
                        .iter()
                        .map(m8_apply_arg_json)
                        .collect::<Vec<_>>()
                        .join(","),
                    rewrite_direction_json(*direction),
                    m8_rewrite_site_json(*site),
                )
            }
            MachineTacticCandidate::SimpLite { rules } => {
                format!(
                    r#"{{"kind":"simp-lite","rules":[{}]}}"#,
                    rules
                        .iter()
                        .map(simp_rule_json)
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            _ => panic!("M8 fixture serializes only rw/simp search suggestions"),
        }
    }

    fn m8_tactic_head_json(head: &TacticHead) -> String {
        match head {
            TacticHead::Imported {
                name,
                decl_interface_hash,
            } => format!(
                r#"{{"imported":{{"name":"{}","decl_interface_hash":"{}"}}}}"#,
                name.as_dotted(),
                format_hash_string(decl_interface_hash),
            ),
            _ => panic!("M8 fixture expects imported tactic heads"),
        }
    }

    fn m8_apply_arg_json(arg: &CandidateApplyArg) -> String {
        match arg {
            CandidateApplyArg::InferFromTarget => r#"{"mode":"infer_from_target"}"#.to_owned(),
            _ => panic!("M8 fixture expects infer_from_target rw args"),
        }
    }

    fn m8_rewrite_site_json(site: RewriteSite) -> &'static str {
        match site {
            RewriteSite::EqTargetLeft => "eq_target_left",
            RewriteSite::EqTargetRight => "eq_target_right",
        }
    }

    fn tactic_options_recipe_json(recipe: &MachineStdTacticOptionsRecipe) -> String {
        format!(
            "{{\"recipe_id\":\"{}\",\"kernel_check_profile\":\"{}\",\"simp_rules\":[{}],\"eq_family\":{},\"nat_family\":{},\"max_simp_rewrite_steps\":{},\"max_open_goals\":{},\"max_metas\":{}}}",
            recipe.recipe_id,
            recipe.kernel_check_profile,
            recipe
                .simp_rules
                .iter()
                .map(simp_rule_json)
                .collect::<Vec<_>>()
                .join(","),
            recipe
                .eq_family
                .as_ref()
                .map(eq_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            recipe
                .nat_family
                .as_ref()
                .map(nat_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            recipe.max_simp_rewrite_steps,
            recipe.max_open_goals,
            recipe.max_metas,
        )
    }

    fn tactic_options_request_json(recipe: &MachineStdTacticOptionsRecipe) -> String {
        format!(
            "{{\"simp_rules\":[{}],\"eq_family\":{},\"nat_family\":{},\"max_simp_rewrite_steps\":{},\"max_open_goals\":{},\"max_metas\":{}}}",
            recipe
                .simp_rules
                .iter()
                .map(simp_rule_json)
                .collect::<Vec<_>>()
                .join(","),
            recipe
                .eq_family
                .as_ref()
                .map(eq_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            recipe
                .nat_family
                .as_ref()
                .map(nat_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            recipe.max_simp_rewrite_steps,
            recipe.max_open_goals,
            recipe.max_metas,
        )
    }

    fn simp_rule_json(rule: &SimpRuleRef) -> String {
        let direction = match rule.direction {
            RewriteDirection::Forward => "forward",
            RewriteDirection::Backward => "backward",
        };
        format!(
            "{{\"name\":\"{}\",\"decl_interface_hash\":\"{}\",\"direction\":\"{}\"}}",
            rule.name.as_dotted(),
            format_hash_string(&rule.decl_interface_hash),
            direction,
        )
    }

    fn eq_family_json(family: &EqFamilyRef) -> String {
        format!(
            "{{\"eq_name\":\"{}\",\"eq_interface_hash\":\"{}\",\"refl_name\":\"{}\",\"refl_interface_hash\":\"{}\",\"rec_name\":\"{}\",\"rec_interface_hash\":\"{}\"}}",
            family.eq_name.as_dotted(),
            format_hash_string(&family.eq_interface_hash),
            family.refl_name.as_dotted(),
            format_hash_string(&family.refl_interface_hash),
            family.rec_name.as_dotted(),
            format_hash_string(&family.rec_interface_hash),
        )
    }

    fn nat_family_json(family: &NatFamilyRef) -> String {
        format!(
            "{{\"nat_name\":\"{}\",\"nat_interface_hash\":\"{}\",\"zero_name\":\"{}\",\"zero_interface_hash\":\"{}\",\"succ_name\":\"{}\",\"succ_interface_hash\":\"{}\",\"rec_name\":\"{}\",\"rec_interface_hash\":\"{}\"}}",
            family.nat_name.as_dotted(),
            format_hash_string(&family.nat_interface_hash),
            family.zero_name.as_dotted(),
            format_hash_string(&family.zero_interface_hash),
            family.succ_name.as_dotted(),
            format_hash_string(&family.succ_interface_hash),
            family.rec_name.as_dotted(),
            format_hash_string(&family.rec_interface_hash),
        )
    }

    fn machine_axiom_ref_wire_json(axiom: &MachineAxiomRefWire) -> String {
        match axiom {
            MachineAxiomRefWire::Imported {
                module,
                name,
                export_hash,
                decl_interface_hash,
            } => format!(
                "{{\"kind\":\"imported\",\"module\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"decl_interface_hash\":\"{}\"}}",
                module.as_dotted(),
                name.as_dotted(),
                format_hash_string(export_hash),
                format_hash_string(decl_interface_hash),
            ),
            MachineAxiomRefWire::CurrentModule {
                module,
                name,
                source_index,
                decl_interface_hash,
            } => format!(
                "{{\"kind\":\"current_module\",\"module\":\"{}\",\"name\":\"{}\",\"source_index\":{},\"decl_interface_hash\":\"{}\"}}",
                module.as_dotted(),
                name.as_dotted(),
                source_index,
                format_hash_string(decl_interface_hash),
            ),
            MachineAxiomRefWire::Builtin {
                name,
                decl_interface_hash,
            } => format!(
                "{{\"kind\":\"builtin\",\"name\":\"{}\",\"decl_interface_hash\":\"{}\"}}",
                name.as_dotted(),
                format_hash_string(decl_interface_hash),
            ),
        }
    }

    fn theorem_index_json(theorem_index: &MachineStdTheoremIndex) -> String {
        format!(
            "{{\"index_profile_id\":\"{}\",\"library_profile_id\":\"{}\",\"entries\":[{}],\"index_hash\":\"{}\"}}",
            theorem_index.index_profile_id,
            theorem_index.library_profile_id,
            theorem_index
                .entries
                .iter()
                .map(theorem_entry_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&theorem_index.index_hash),
        )
    }

    fn prompt_metadata_set_json(metadata: &MachineStdPromptMetadataSet) -> String {
        format!(
            "{{\"metadata_profile_id\":\"{}\",\"library_profile_id\":\"{}\",\"entries\":[{}],\"prompt_metadata_hash\":\"{}\"}}",
            metadata.metadata_profile_id,
            metadata.library_profile_id,
            metadata
                .entries
                .iter()
                .map(prompt_metadata_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&metadata.prompt_metadata_hash),
        )
    }

    fn prompt_metadata_json(metadata: &MachineStdPromptMetadata) -> String {
        format!(
            "{{\"global_ref\":{},\"short_doc\":{},\"examples\":[{}],\"tags\":[{}]}}",
            global_ref_json(&metadata.global_ref),
            metadata
                .short_doc
                .as_ref()
                .map(|doc| format!("\"{doc}\""))
                .unwrap_or_else(|| "null".to_owned()),
            metadata
                .examples
                .iter()
                .map(prompt_example_json)
                .collect::<Vec<_>>()
                .join(","),
            metadata
                .tags
                .iter()
                .map(|tag| format!("\"{tag}\""))
                .collect::<Vec<_>>()
                .join(","),
        )
    }

    fn prompt_example_json(example: &MachineStdPromptExample) -> String {
        format!(
            "{{\"goal_core_hash\":\"{}\",\"imports_bundle_id\":\"{}\",\"candidate_kind\":\"{}\",\"display\":\"{}\"}}",
            format_hash_string(&example.goal_core_hash),
            example.imports_bundle_id,
            example.candidate_kind,
            example.display,
        )
    }

    fn theorem_entry_json(entry: &MachineStdTheoremEntry) -> String {
        format!(
            "{{\"global_ref\":{},\"kind\":\"{}\",\"universe_params\":[{}],\"statement_core_hash\":\"{}\",\"statement_head\":{},\"constants\":[{}],\"modes\":[{}],\"attributes\":[{}],\"rewrite_descriptors\":[{}],\"axiom_dependencies\":[{}],\"proof_term_size\":{}}}",
            global_ref_json(&entry.global_ref),
            theorem_kind_json(entry.kind),
            entry
                .universe_params
                .iter()
                .map(|param| format!("\"{param}\""))
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&entry.statement_core_hash),
            entry
                .statement_head
                .as_ref()
                .map(global_ref_view_json)
                .unwrap_or_else(|| "null".to_owned()),
            entry
                .constants
                .iter()
                .map(global_ref_view_json)
                .collect::<Vec<_>>()
                .join(","),
            entry
                .modes
                .iter()
                .map(|mode| format!("\"{}\"", mode.as_str()))
                .collect::<Vec<_>>()
                .join(","),
            entry
                .attributes
                .iter()
                .map(|attribute| format!("\"{}\"", std_attribute_json(*attribute)))
                .collect::<Vec<_>>()
                .join(","),
            entry
                .rewrite_descriptors
                .iter()
                .map(rewrite_descriptor_json)
                .collect::<Vec<_>>()
                .join(","),
            entry
                .axiom_dependencies
                .iter()
                .map(axiom_ref_json)
                .collect::<Vec<_>>()
                .join(","),
            entry
                .proof_term_size
                .map(|size| size.to_string())
                .unwrap_or_else(|| "null".to_owned()),
        )
    }

    fn global_ref_json(global_ref: &MachineStdGlobalRef) -> String {
        format!(
            "{{\"module\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\",\"decl_interface_hash\":\"{}\"}}",
            global_ref.module.as_dotted(),
            global_ref.name.as_dotted(),
            format_hash_string(&global_ref.export_hash),
            format_hash_string(&global_ref.certificate_hash),
            format_hash_string(&global_ref.decl_interface_hash),
        )
    }

    fn global_ref_view_json(view: &MachineStdGlobalRefView) -> String {
        match view {
            MachineStdGlobalRefView::Decl {
                module,
                name,
                export_hash,
                certificate_hash,
                decl_interface_hash,
                public_export,
            } => format!(
                "{{\"kind\":\"decl\",\"module\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\",\"decl_interface_hash\":\"{}\",\"public_export\":{}}}",
                module.as_dotted(),
                name.as_dotted(),
                format_hash_string(export_hash),
                format_hash_string(certificate_hash),
                format_hash_string(decl_interface_hash),
                public_export,
            ),
            MachineStdGlobalRefView::Generated {
                module,
                parent_name,
                name,
                export_hash,
                certificate_hash,
                parent_decl_interface_hash,
                decl_interface_hash,
                public_export,
            } => format!(
                "{{\"kind\":\"generated\",\"module\":\"{}\",\"parent_name\":\"{}\",\"name\":\"{}\",\"export_hash\":\"{}\",\"certificate_hash\":\"{}\",\"parent_decl_interface_hash\":\"{}\",\"decl_interface_hash\":\"{}\",\"public_export\":{}}}",
                module.as_dotted(),
                parent_name.as_dotted(),
                name.as_dotted(),
                format_hash_string(export_hash),
                format_hash_string(certificate_hash),
                format_hash_string(parent_decl_interface_hash),
                format_hash_string(decl_interface_hash),
                public_export,
            ),
        }
    }

    fn theorem_kind_json(kind: MachineStdTheoremKind) -> &'static str {
        match kind {
            MachineStdTheoremKind::Theorem => "theorem",
            MachineStdTheoremKind::Axiom => "axiom",
        }
    }

    fn std_attribute_json(attribute: MachineStdAttribute) -> &'static str {
        match attribute {
            MachineStdAttribute::Simp => "simp",
            MachineStdAttribute::Rw => "rw",
            MachineStdAttribute::Intro => "intro",
            MachineStdAttribute::Elim => "elim",
            MachineStdAttribute::Apply => "apply",
            MachineStdAttribute::Refl => "refl",
            MachineStdAttribute::Trans => "trans",
            MachineStdAttribute::Congr => "congr",
        }
    }

    fn rewrite_profile_set_json(profile_set: &MachineStdRewriteProfileSet) -> String {
        format!(
            "{{\"library_profile_id\":\"{}\",\"profiles\":[{}],\"rewrite_profiles_hash\":\"{}\"}}",
            profile_set.library_profile_id,
            profile_set
                .profiles
                .iter()
                .map(rewrite_profile_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&profile_set.rewrite_profiles_hash),
        )
    }

    fn rewrite_profile_json(profile: &MachineStdRewriteProfile) -> String {
        format!(
            "{{\"profile_id\":\"{}\",\"required_import_bundle_id\":\"{}\",\"kernel_check_profile\":\"{}\",\"eq_family\":{},\"descriptors\":[{}],\"profile_hash\":\"{}\"}}",
            profile.profile_id,
            profile.required_import_bundle_id,
            profile.kernel_check_profile,
            profile
                .eq_family
                .as_ref()
                .map(eq_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            profile
                .descriptors
                .iter()
                .map(rewrite_descriptor_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&profile.profile_hash),
        )
    }

    fn rewrite_descriptor_json(descriptor: &MachineStdRewriteDescriptor) -> String {
        format!(
            "{{\"source\":{},\"direction\":\"{}\",\"safety\":\"{}\",\"lhs_core_hash\":\"{}\",\"rhs_core_hash\":\"{}\",\"rule_telescope_hash\":\"{}\"}}",
            global_ref_json(&descriptor.source),
            rewrite_direction_json(descriptor.direction),
            rewrite_safety_json(descriptor.safety),
            format_hash_string(&descriptor.lhs_core_hash),
            format_hash_string(&descriptor.rhs_core_hash),
            format_hash_string(&descriptor.rule_telescope_hash),
        )
    }

    fn simp_profile_set_json(profile_set: &MachineStdSimpProfileSet) -> String {
        format!(
            "{{\"library_profile_id\":\"{}\",\"profiles\":[{}],\"simp_profiles_hash\":\"{}\"}}",
            profile_set.library_profile_id,
            profile_set
                .profiles
                .iter()
                .map(simp_profile_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&profile_set.simp_profiles_hash),
        )
    }

    fn simp_profile_json(profile: &MachineStdSimpProfile) -> String {
        format!(
            "{{\"profile_id\":\"{}\",\"required_import_bundle_id\":\"{}\",\"kernel_check_profile\":\"{}\",\"eq_family\":{},\"rules\":[{}],\"profile_hash\":\"{}\"}}",
            profile.profile_id,
            profile.required_import_bundle_id,
            profile.kernel_check_profile,
            profile
                .eq_family
                .as_ref()
                .map(eq_family_json)
                .unwrap_or_else(|| "null".to_owned()),
            profile
                .rules
                .iter()
                .map(simp_rule_json)
                .collect::<Vec<_>>()
                .join(","),
            format_hash_string(&profile.profile_hash),
        )
    }

    fn rewrite_direction_json(direction: RewriteDirection) -> &'static str {
        match direction {
            RewriteDirection::Forward => "forward",
            RewriteDirection::Backward => "backward",
        }
    }

    fn rewrite_safety_json(safety: MachineStdRewriteSafety) -> &'static str {
        match safety {
            MachineStdRewriteSafety::SimpSafe => "simp_safe",
            MachineStdRewriteSafety::RwOnly => "rw_only",
            MachineStdRewriteSafety::UnsafeForAutomation => "unsafe_for_automation",
        }
    }

    fn lower_hex_bytes(bytes: &[u8]) -> String {
        let mut out = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            out.push(hex_digit(byte >> 4));
            out.push(hex_digit(byte & 0x0f));
        }
        out
    }

    fn hex_digit(value: u8) -> char {
        match value {
            0..=9 => (b'0' + value) as char,
            10..=15 => (b'a' + (value - 10)) as char,
            _ => unreachable!("hex nybble is in range"),
        }
    }

    fn test_hash(seed: u8) -> Hash {
        [seed; 32]
    }

    struct TestPackage {
        path: PathBuf,
    }

    impl TestPackage {
        fn new(label: &str) -> Self {
            let mut path = std::env::temp_dir();
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            path.push(format!(
                "npa-stdlib-loader-{label}-{}-{nanos}",
                std::process::id()
            ));
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }

        fn path(&self) -> &Path {
            &self.path
        }
    }

    impl Drop for TestPackage {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}
