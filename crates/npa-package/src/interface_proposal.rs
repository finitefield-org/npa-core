//! Strict parser and data model for Mathlib interface proposals.
//!
//! Interface proposals are untrusted curation metadata. They describe a
//! possible future NPA interface and preserve provenance and use-site
//! observations, but they are not proof evidence, source-free checker input,
//! certificates, catalog admission, or release metadata. This module only
//! parses bytes supplied by its caller; it does not access a filesystem,
//! frontend, Git, network, or proof checker.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, str,
};

use npa_cert::Name;
use toml::{Table, Value};

use crate::hash::{package_file_hash, parse_package_hash, PackageHash};

/// Exact v1 schema accepted by the interface-proposal parser.
pub const INTERFACE_PROPOSAL_SCHEMA: &str = "npa.mathlib.interface_proposal.v1";

/// Exact proposal-file hash schema prefix used by the v1 contract.
pub const INTERFACE_PROPOSAL_HASH_PREFIX: &str = "sha256:";

/// Maximum number of canonical proposal files in one proposal set.
pub const MAX_PROPOSAL_FILES: usize = 4096;

/// Maximum raw UTF-8 TOML bytes in one proposal file.
pub const MAX_PROPOSAL_FILE_BYTES: usize = 262_144;

/// Maximum raw UTF-8 bytes across one proposal set.
pub const MAX_PROPOSAL_SET_BYTES: usize = 67_108_864;

/// Maximum declaration rows in one proposal.
pub const MAX_DECLARATIONS: usize = 256;

/// Maximum observation rows in one proposal.
pub const MAX_OBSERVATIONS: usize = 512;

/// Maximum proof-reference rows in one proposal.
pub const MAX_PROOF_REFERENCES: usize = 256;

/// Maximum alternative rows in one proposal.
pub const MAX_ALTERNATIVES: usize = 128;

/// Maximum direct imports in one proposal.
pub const MAX_IMPORTS: usize = 128;

/// Maximum entries in a link array such as `depends_on` or `evidence_ids`.
pub const MAX_LINKS_PER_ARRAY: usize = 256;

/// Maximum UTF-8 bytes in a repository-relative path value.
pub const MAX_PATH_BYTES: usize = 1024;

/// Maximum UTF-8 bytes in a non-path scalar string value.
pub const MAX_STRING_BYTES: usize = 16_384;

/// Maximum local interface or certificate file bytes used by later resolution.
pub const MAX_INTERFACE_FILE_BYTES: usize = 16_777_216;

/// Maximum diagnostics emitted by one public command result.
pub const MAX_DIAGNOSTICS: usize = 1024;

/// Maximum bytes in one rendered diagnostic expected or actual value.
pub const MAX_DIAGNOSTIC_VALUE_BYTES: usize = 256;

/// Result type for interface-proposal parsing and validation.
pub type InterfaceProposalResult<T> = Result<T, InterfaceProposalError>;

/// Interface lifecycle status, intentionally distinct from catalog maturity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalStatus {
    /// Evidence exists but the target interface is not complete.
    Observed,
    /// A complete target interface is available for review.
    Proposed,
    /// The exact target interface is manually adopted as an implementation contract.
    Adopted,
    /// An unadopted proposal is terminally abandoned.
    Withdrawn,
    /// An adopted proposal is terminally replaced by another proposal.
    Superseded,
}

impl InterfaceProposalStatus {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Observed => "observed",
            Self::Proposed => "proposed",
            Self::Adopted => "adopted",
            Self::Withdrawn => "withdrawn",
            Self::Superseded => "superseded",
        }
    }
}

/// Change relationship between a proposal and the current catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalChangeKind {
    /// Introduce a target module with no current catalog route.
    Add,
    /// Change the identity-bearing surface of the same module.
    Revise,
    /// Move one current module to a meaning-equivalent target name.
    Rename,
    /// Replace one current module with multiple target proposals.
    Split,
    /// Replace multiple current modules with one target proposal.
    Merge,
    /// Retire one current module for a materially different successor.
    Replace,
}

impl InterfaceProposalChangeKind {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Revise => "revise",
            Self::Rename => "rename",
            Self::Split => "split",
            Self::Merge => "merge",
            Self::Replace => "replace",
        }
    }
}

/// Declaration family admitted by the v1 public surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalDeclarationKind {
    /// An inductive family and its generated public names.
    Inductive,
    /// A definition with an exact NPA body when adopted.
    Definition,
    /// A theorem with separately recorded proof references when adopted.
    Theorem,
}

impl InterfaceProposalDeclarationKind {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Inductive => "inductive",
            Self::Definition => "definition",
            Self::Theorem => "theorem",
        }
    }
}

/// Whether a declaration is part of the intended public or support surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalSurface {
    /// Declaration intended to be exported as part of the public interface.
    Public,
    /// Declaration needed to close the public interface but not independently public.
    Support,
}

impl InterfaceProposalSurface {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Public => "public",
            Self::Support => "support",
        }
    }
}

/// Immutable revision locator kind for an observation or proof reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalRevisionKind {
    /// Full lower-case Git commit SHA.
    GitCommit,
    /// Lower-case SHA-256 release digest.
    ReleaseDigest,
}

impl InterfaceProposalRevisionKind {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::GitCommit => "git_commit",
            Self::ReleaseDigest => "release_digest",
        }
    }
}

/// Kind of repository usage recorded by an observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalUsageKind {
    /// Source declaration observed in the pinned repository.
    Declaration,
    /// Module import or module-layout observation.
    ModuleImport,
    /// Direct application of a declaration.
    DirectApplication,
    /// Rewrite using a declaration.
    Rewrite,
    /// Inference or instance dependency.
    InstanceDependency,
    /// Transitive dependency use.
    TransitiveDependency,
    /// Module boundary or placement observation.
    ModuleLayout,
}

impl InterfaceProposalUsageKind {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Declaration => "declaration",
            Self::ModuleImport => "module_import",
            Self::DirectApplication => "direct_application",
            Self::Rewrite => "rewrite",
            Self::InstanceDependency => "instance_dependency",
            Self::TransitiveDependency => "transitive_dependency",
            Self::ModuleLayout => "module_layout",
        }
    }
}

/// Role played by a pinned proof reference in a later proof design.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalReferenceRole {
    /// Reference to the overall proof structure.
    ProofStructure,
    /// Reference to a useful lemma choice.
    LemmaChoice,
    /// Reference to an induction scheme.
    InductionScheme,
    /// Reference to a normalization strategy.
    NormalizationStrategy,
}

impl InterfaceProposalReferenceRole {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProofStructure => "proof_structure",
            Self::LemmaChoice => "lemma_choice",
            Self::InductionScheme => "induction_scheme",
            Self::NormalizationStrategy => "normalization_strategy",
        }
    }
}

/// Kind of rejected or deferred alternative recorded during curation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalAlternativeKind {
    /// Alternative target module name.
    ModuleName,
    /// Alternative declaration name.
    DeclarationName,
    /// Alternative declaration signature.
    Signature,
    /// Alternative module boundary.
    ModuleBoundary,
}

impl InterfaceProposalAlternativeKind {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ModuleName => "module_name",
            Self::DeclarationName => "declaration_name",
            Self::Signature => "signature",
            Self::ModuleBoundary => "module_boundary",
        }
    }
}

/// Curation disposition for an alternative.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalAlternativeDisposition {
    /// Alternative was considered and rejected for this proposal.
    Rejected,
    /// Alternative was deferred for a later proposal.
    Deferred,
}

impl InterfaceProposalAlternativeDisposition {
    /// Return the canonical lower-case TOML spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rejected => "rejected",
            Self::Deferred => "deferred",
        }
    }
}

/// One exact declaration entry in an interface proposal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalDeclaration {
    /// Unqualified NPA declaration name.
    pub name: String,
    /// Declaration family.
    pub kind: InterfaceProposalDeclarationKind,
    /// Public/support boundary.
    pub surface: InterfaceProposalSurface,
    /// Exact NPA signature when supplied.
    pub signature: Option<String>,
    /// Exact NPA definition body when supplied.
    pub body: Option<String>,
    /// Semantic/generated family names in their declared order.
    pub family_members: Vec<String>,
    /// Explanation of why the declaration belongs in the module.
    pub semantic_role: String,
    /// Same-module declaration dependencies in semantic order.
    pub depends_on: Vec<String>,
    /// Proposal-local observation IDs supporting the declaration.
    pub evidence_ids: Vec<String>,
    /// Optional foundation exception for a public declaration without evidence.
    pub foundation_exception: Option<String>,
    /// Rationale for an unevidenced support declaration.
    pub support_rationale: Option<String>,
    /// Proposal-local proof-reference IDs for a theorem.
    pub proof_reference_ids: Vec<String>,
    /// Optional explanation for a theorem with no separate proof reference.
    pub proof_reference_exception: Option<String>,
}

/// One pinned repository observation used during curation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalObservation {
    /// Proposal-local unique observation ID.
    pub id: String,
    /// Repository URL or local repository identity.
    pub repository: String,
    /// Immutable revision locator kind.
    pub revision_kind: InterfaceProposalRevisionKind,
    /// Full immutable revision locator.
    pub revision: String,
    /// Known license identifier or `UNKNOWN`.
    pub license: String,
    /// Repository-relative source path.
    pub path: String,
    /// Source module when the observation identifies one.
    pub source_module: Option<String>,
    /// Source declaration when the usage identifies one.
    pub source_declaration: Option<String>,
    /// Observed usage category.
    pub usage_kind: InterfaceProposalUsageKind,
    /// Concise explanation of the exact observation.
    pub notes: String,
}

/// One pinned proof-design reference kept separate from use evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalProofReference {
    /// Proposal-local unique proof-reference ID.
    pub id: String,
    /// Repository URL or local repository identity.
    pub repository: String,
    /// Immutable revision locator kind.
    pub revision_kind: InterfaceProposalRevisionKind,
    /// Full immutable revision locator.
    pub revision: String,
    /// Known license identifier or `UNKNOWN`.
    pub license: String,
    /// Repository-relative proof source path.
    pub path: String,
    /// Source module when needed to identify the proof location.
    pub source_module: Option<String>,
    /// Source declaration containing the proof reference.
    pub source_declaration: String,
    /// Role of the reference in proof design.
    pub reference_role: InterfaceProposalReferenceRole,
    /// Concise explanation of the reference.
    pub notes: String,
}

/// One rejected or deferred alternative considered during curation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalAlternative {
    /// Alternative category.
    pub kind: InterfaceProposalAlternativeKind,
    /// Candidate name, signature, or boundary description.
    pub candidate: String,
    /// Curation disposition.
    pub disposition: InterfaceProposalAlternativeDisposition,
    /// Reason the candidate was not selected now.
    pub rationale: String,
    /// Proposal-local observation IDs supporting the decision.
    pub evidence_ids: Vec<String>,
}

/// Complete parsed v1 interface-proposal metadata record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposal {
    /// Exact proposal schema string.
    pub schema: String,
    /// Stable logical proposal ID.
    pub proposal_id: String,
    /// Positive canonical record revision.
    pub proposal_revision: u64,
    /// Exact hash of the immediately previous canonical file, when supplied.
    pub previous_proposal_hash: Option<PackageHash>,
    /// Exact target module name.
    pub module: String,
    /// Relationship to current catalog content.
    pub change_kind: InterfaceProposalChangeKind,
    /// Current catalog modules replaced or revised by this proposal.
    pub source_modules: Vec<String>,
    /// Shared nonempty group for a catalog split.
    pub change_group: Option<String>,
    /// Curation lifecycle status.
    pub interface_status: InterfaceProposalStatus,
    /// Always required to be false by the proposal contract; semantic checking is later.
    pub proof_evidence: bool,
    /// One-sentence mathematical description.
    pub summary: String,
    /// Included and excluded module scope.
    pub scope: String,
    /// Direct public import boundary in semantic order.
    pub imports: Vec<String>,
    /// Adoption date when supplied.
    pub adoption_date: Option<String>,
    /// Adoption rationale when supplied.
    pub adoption_rationale: Option<String>,
    /// Re-adoption rationale when supplied.
    pub re_adoption_rationale: Option<String>,
    /// Withdrawal rationale when supplied.
    pub withdrawal_rationale: Option<String>,
    /// Review of naming, signature, and boundary alternatives.
    pub alternatives_review: Option<String>,
    /// Proposal IDs replaced by this proposal.
    pub supersedes: Vec<String>,
    /// Sorted successor IDs for a superseded record, when supplied.
    pub superseded_by: Option<Vec<String>>,
    /// Declaration rows; an absent TOML collection is represented as empty.
    pub declarations: Vec<InterfaceProposalDeclaration>,
    /// Pinned use and declaration observations.
    pub observations: Vec<InterfaceProposalObservation>,
    /// Pinned proof-design references.
    pub proof_references: Vec<InterfaceProposalProofReference>,
    /// Rejected or deferred alternatives.
    pub alternatives: Vec<InterfaceProposalAlternative>,
}

/// Stable category for an interface-proposal diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalErrorCategory {
    /// Local filesystem or input-root failure.
    Io,
    /// Canonical proposal discovery failure.
    Discovery,
    /// TOML or UTF-8 syntax failure.
    Syntax,
    /// Frozen resource limit failure.
    Resource,
    /// One-record contract failure.
    Contract,
    /// Lifecycle or revision-transition failure.
    Lifecycle,
    /// Evidence or provenance failure.
    Evidence,
    /// Import or declaration graph failure.
    Graph,
    /// Current catalog relation failure.
    Catalog,
    /// Previous-snapshot comparison failure.
    Comparison,
}

impl InterfaceProposalErrorCategory {
    /// Return the canonical lower-case diagnostic category.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Io => "io",
            Self::Discovery => "discovery",
            Self::Syntax => "syntax",
            Self::Resource => "resource",
            Self::Contract => "contract",
            Self::Lifecycle => "lifecycle",
            Self::Evidence => "evidence",
            Self::Graph => "graph",
            Self::Catalog => "catalog",
            Self::Comparison => "comparison",
        }
    }
}

/// Stable lower-case UIA-01 reason code.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceProposalErrorReason {
    /// Root is not a directory.
    RootNotDirectory,
    /// Current proposal root is not a directory.
    ProposalRootNotDirectory,
    /// Previous proposal root is not a directory.
    PreviousRootNotDirectory,
    /// Current and previous roots are identical.
    PreviousRootSameAsCurrent,
    /// A local read failed.
    ReadFailed,
    /// Catalog metadata is missing.
    CatalogMetadataMissing,
    /// Catalog metadata is invalid.
    CatalogMetadataInvalid,
    /// A symlink was found in the scan domain.
    SymlinkEntry,
    /// A non-regular entry was found in the scan domain.
    NonRegularEntry,
    /// A canonical path escaped its root.
    PathEscape,
    /// A path was not valid UTF-8.
    InvalidPathUtf8,
    /// A path contained a tab or newline.
    PathContainsTabOrNewline,
    /// A canonical entry had a non-TOML extension.
    NoncanonicalExtension,
    /// Proposal file count exceeded the frozen limit.
    ProposalCountExceeded,
    /// Proposal file bytes exceeded the frozen limit.
    ProposalFileBytesExceeded,
    /// Proposal-set bytes exceeded the frozen limit.
    ProposalSetBytesExceeded,
    /// Input bytes were not UTF-8.
    InvalidUtf8,
    /// TOML syntax was invalid.
    InvalidToml,
    /// A duplicate TOML key was found.
    DuplicateKey,
    /// A field was not part of the closed schema.
    UnknownField,
    /// A TOML value had the wrong type.
    WrongType,
    /// The schema version was not recognized.
    UnknownSchema,
    /// Declaration rows exceeded the frozen limit.
    DeclarationCountExceeded,
    /// Observation rows exceeded the frozen limit.
    ObservationCountExceeded,
    /// Proof-reference rows exceeded the frozen limit.
    ProofReferenceCountExceeded,
    /// Alternative rows exceeded the frozen limit.
    AlternativeCountExceeded,
    /// Imports exceeded the frozen limit.
    ImportCountExceeded,
    /// A link array exceeded the frozen limit.
    LinkCountExceeded,
    /// A path value exceeded the frozen limit.
    PathBytesExceeded,
    /// A scalar string exceeded the frozen limit.
    StringBytesExceeded,
    /// An interface file exceeded the frozen limit.
    InterfaceFileBytesExceeded,
    /// Diagnostic count exceeded the frozen limit.
    DiagnosticCountExceeded,
    /// A required field was absent.
    MissingField,
    /// A string value was empty.
    EmptyValue,
    /// An enum value was not recognized.
    InvalidEnum,
    /// An identifier was invalid.
    InvalidIdentifier,
    /// A module name was invalid.
    InvalidModuleName,
    /// A canonical path did not match a module name.
    ModulePathMismatch,
    /// A revision number was invalid.
    InvalidRevision,
    /// A hash value was invalid.
    InvalidHash,
    /// An adoption date was invalid.
    InvalidDate,
    /// `proof_evidence` was not false.
    ProofEvidenceNotFalse,
    /// A change kind was invalid for the record.
    InvalidChangeKind,
    /// Source modules were invalid.
    InvalidSourceModules,
    /// A change group was invalid.
    InvalidChangeGroup,
    /// `superseded_by` was not sorted correctly.
    InvalidSupersededByOrder,
    /// A signature was invalid.
    InvalidSignature,
    /// A signature contained a placeholder.
    PlaceholderSignature,
    /// A definition body was invalid.
    InvalidDefinitionBody,
    /// A definition body contained a placeholder.
    PlaceholderDefinitionBody,
    /// An inductive family was invalid.
    InvalidFamily,
    /// An inductive family member was duplicated.
    DuplicateFamilyMember,
    /// An inductive family was incomplete.
    IncompleteFamily,
    /// A declaration name was duplicated.
    DuplicateDeclarationName,
    /// A set-like member was duplicated.
    DuplicateSetMember,
    /// A quotient-backed interface was forbidden.
    ForbiddenQuotientInterface,
    /// A status value was invalid.
    InvalidStatus,
    /// Status metadata was incomplete.
    StatusMetadataMissing,
    /// A status surface was incomplete.
    StatusSurfaceIncomplete,
    /// Withdrawal rationale was absent.
    WithdrawalRationaleMissing,
    /// Supersession metadata was incomplete.
    SupersessionMetadataMissing,
    /// Re-adoption metadata was incomplete.
    ReadoptionMetadataMissing,
    /// A proposal ID was reused.
    ProposalIdReused,
    /// A terminal ID was reused.
    TerminalIdReused,
    /// An evidence ID was duplicated.
    DuplicateEvidenceId,
    /// An evidence ID was unresolved.
    UnresolvedEvidenceId,
    /// A public declaration lacked evidence.
    MissingPublicEvidence,
    /// A foundation exception was invalid.
    InvalidFoundationException,
    /// A support rationale was invalid.
    InvalidSupportRationale,
    /// A support declaration was unreachable.
    SupportNotReachable,
    /// A source location was absent.
    MissingSourceLocation,
    /// A revision locator was invalid.
    InvalidRevisionLocator,
    /// A revision locator was floating.
    FloatingRevision,
    /// An unknown license lacked a follow-up note.
    LicenseUnknownWithoutNote,
    /// An unknown license blocked adoption.
    LicenseUnknownBlocksAdoption,
    /// A usage kind was invalid.
    InvalidUsageKind,
    /// A proof-reference ID was duplicated.
    DuplicateProofReferenceId,
    /// A proof-reference ID was unresolved.
    UnresolvedProofReferenceId,
    /// A reference role was invalid.
    InvalidReferenceRole,
    /// A theorem lacked a proof reference.
    MissingProofReference,
    /// A proof-reference exception was invalid.
    InvalidProofReferenceException,
    /// Alternatives review text was absent.
    MissingAlternativesReview,
    /// Alternative evidence was invalid.
    InvalidAlternativeEvidence,
    /// Alternative disposition was invalid.
    InvalidAlternativeDisposition,
    /// A dependency was unresolved.
    UnresolvedDependency,
    /// A declaration dependency cycle was found.
    DependencyCycle,
    /// An import was unresolved.
    ImportUnresolved,
    /// An import cycle was found.
    ImportCycle,
    /// Public support closure was incomplete.
    PublicSupportClosureIncomplete,
    /// An inductive family closure was incomplete.
    FamilyClosureIncomplete,
    /// A catalog module collided.
    CatalogModuleCollision,
    /// A catalog declaration collided.
    CatalogDeclarationCollision,
    /// A catalog target was missing.
    CatalogTargetMissing,
    /// A catalog target already existed.
    CatalogTargetExists,
    /// Catalog source cardinality was invalid.
    CatalogSourceCardinality,
    /// An import was forbidden.
    ForbiddenImport,
    /// Active module identities collided.
    ActiveModuleCollision,
    /// The previous snapshot was invalid.
    PreviousSnapshotInvalid,
    /// A previous record was removed.
    PreviousRecordRemoved,
    /// A record identity changed.
    RecordIdentityChanged,
    /// A revision was not incremented.
    RevisionNotIncremented,
    /// A previous hash did not match.
    PreviousHashMismatch,
    /// A terminal record changed.
    TerminalRecordChanged,
    /// A status transition was invalid.
    InvalidStatusTransition,
    /// A withdrawn surface changed.
    WithdrawnSurfaceChanged,
    /// Supersession links were not reciprocal.
    SupersessionNotReciprocal,
    /// Adopted rework was not re-adopted correctly.
    AdoptedReworkNotReadopted,
}

impl InterfaceProposalErrorReason {
    /// Return the canonical lower-case UIA-01 reason code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RootNotDirectory => "root_not_directory",
            Self::ProposalRootNotDirectory => "proposal_root_not_directory",
            Self::PreviousRootNotDirectory => "previous_root_not_directory",
            Self::PreviousRootSameAsCurrent => "previous_root_same_as_current",
            Self::ReadFailed => "read_failed",
            Self::CatalogMetadataMissing => "catalog_metadata_missing",
            Self::CatalogMetadataInvalid => "catalog_metadata_invalid",
            Self::SymlinkEntry => "symlink_entry",
            Self::NonRegularEntry => "non_regular_entry",
            Self::PathEscape => "path_escape",
            Self::InvalidPathUtf8 => "invalid_path_utf8",
            Self::PathContainsTabOrNewline => "path_contains_tab_or_newline",
            Self::NoncanonicalExtension => "noncanonical_extension",
            Self::ProposalCountExceeded => "proposal_count_exceeded",
            Self::ProposalFileBytesExceeded => "proposal_file_bytes_exceeded",
            Self::ProposalSetBytesExceeded => "proposal_set_bytes_exceeded",
            Self::InvalidUtf8 => "invalid_utf8",
            Self::InvalidToml => "invalid_toml",
            Self::DuplicateKey => "duplicate_key",
            Self::UnknownField => "unknown_field",
            Self::WrongType => "wrong_type",
            Self::UnknownSchema => "unknown_schema",
            Self::DeclarationCountExceeded => "declaration_count_exceeded",
            Self::ObservationCountExceeded => "observation_count_exceeded",
            Self::ProofReferenceCountExceeded => "proof_reference_count_exceeded",
            Self::AlternativeCountExceeded => "alternative_count_exceeded",
            Self::ImportCountExceeded => "import_count_exceeded",
            Self::LinkCountExceeded => "link_count_exceeded",
            Self::PathBytesExceeded => "path_bytes_exceeded",
            Self::StringBytesExceeded => "string_bytes_exceeded",
            Self::InterfaceFileBytesExceeded => "interface_file_bytes_exceeded",
            Self::DiagnosticCountExceeded => "diagnostic_count_exceeded",
            Self::MissingField => "missing_field",
            Self::EmptyValue => "empty_value",
            Self::InvalidEnum => "invalid_enum",
            Self::InvalidIdentifier => "invalid_identifier",
            Self::InvalidModuleName => "invalid_module_name",
            Self::ModulePathMismatch => "module_path_mismatch",
            Self::InvalidRevision => "invalid_revision",
            Self::InvalidHash => "invalid_hash",
            Self::InvalidDate => "invalid_date",
            Self::ProofEvidenceNotFalse => "proof_evidence_not_false",
            Self::InvalidChangeKind => "invalid_change_kind",
            Self::InvalidSourceModules => "invalid_source_modules",
            Self::InvalidChangeGroup => "invalid_change_group",
            Self::InvalidSupersededByOrder => "invalid_superseded_by_order",
            Self::InvalidSignature => "invalid_signature",
            Self::PlaceholderSignature => "placeholder_signature",
            Self::InvalidDefinitionBody => "invalid_definition_body",
            Self::PlaceholderDefinitionBody => "placeholder_definition_body",
            Self::InvalidFamily => "invalid_family",
            Self::DuplicateFamilyMember => "duplicate_family_member",
            Self::IncompleteFamily => "incomplete_family",
            Self::DuplicateDeclarationName => "duplicate_declaration_name",
            Self::DuplicateSetMember => "duplicate_set_member",
            Self::ForbiddenQuotientInterface => "forbidden_quotient_interface",
            Self::InvalidStatus => "invalid_status",
            Self::StatusMetadataMissing => "status_metadata_missing",
            Self::StatusSurfaceIncomplete => "status_surface_incomplete",
            Self::WithdrawalRationaleMissing => "withdrawal_rationale_missing",
            Self::SupersessionMetadataMissing => "supersession_metadata_missing",
            Self::ReadoptionMetadataMissing => "readoption_metadata_missing",
            Self::ProposalIdReused => "proposal_id_reused",
            Self::TerminalIdReused => "terminal_id_reused",
            Self::DuplicateEvidenceId => "duplicate_evidence_id",
            Self::UnresolvedEvidenceId => "unresolved_evidence_id",
            Self::MissingPublicEvidence => "missing_public_evidence",
            Self::InvalidFoundationException => "invalid_foundation_exception",
            Self::InvalidSupportRationale => "invalid_support_rationale",
            Self::SupportNotReachable => "support_not_reachable",
            Self::MissingSourceLocation => "missing_source_location",
            Self::InvalidRevisionLocator => "invalid_revision_locator",
            Self::FloatingRevision => "floating_revision",
            Self::LicenseUnknownWithoutNote => "license_unknown_without_note",
            Self::LicenseUnknownBlocksAdoption => "license_unknown_blocks_adoption",
            Self::InvalidUsageKind => "invalid_usage_kind",
            Self::DuplicateProofReferenceId => "duplicate_proof_reference_id",
            Self::UnresolvedProofReferenceId => "unresolved_proof_reference_id",
            Self::InvalidReferenceRole => "invalid_reference_role",
            Self::MissingProofReference => "missing_proof_reference",
            Self::InvalidProofReferenceException => "invalid_proof_reference_exception",
            Self::MissingAlternativesReview => "missing_alternatives_review",
            Self::InvalidAlternativeEvidence => "invalid_alternative_evidence",
            Self::InvalidAlternativeDisposition => "invalid_alternative_disposition",
            Self::UnresolvedDependency => "unresolved_dependency",
            Self::DependencyCycle => "dependency_cycle",
            Self::ImportUnresolved => "import_unresolved",
            Self::ImportCycle => "import_cycle",
            Self::PublicSupportClosureIncomplete => "public_support_closure_incomplete",
            Self::FamilyClosureIncomplete => "family_closure_incomplete",
            Self::CatalogModuleCollision => "catalog_module_collision",
            Self::CatalogDeclarationCollision => "catalog_declaration_collision",
            Self::CatalogTargetMissing => "catalog_target_missing",
            Self::CatalogTargetExists => "catalog_target_exists",
            Self::CatalogSourceCardinality => "catalog_source_cardinality",
            Self::ForbiddenImport => "forbidden_import",
            Self::ActiveModuleCollision => "active_module_collision",
            Self::PreviousSnapshotInvalid => "previous_snapshot_invalid",
            Self::PreviousRecordRemoved => "previous_record_removed",
            Self::RecordIdentityChanged => "record_identity_changed",
            Self::RevisionNotIncremented => "revision_not_incremented",
            Self::PreviousHashMismatch => "previous_hash_mismatch",
            Self::TerminalRecordChanged => "terminal_record_changed",
            Self::InvalidStatusTransition => "invalid_status_transition",
            Self::WithdrawnSurfaceChanged => "withdrawn_surface_changed",
            Self::SupersessionNotReciprocal => "supersession_not_reciprocal",
            Self::AdoptedReworkNotReadopted => "adopted_rework_not_readopted",
        }
    }
}

/// Structured error for parsing or validating one interface-proposal record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceProposalError {
    /// Stable UIA-01 diagnostic category.
    pub category: InterfaceProposalErrorCategory,
    /// Stable UIA-01 lower-case reason code.
    pub reason_code: InterfaceProposalErrorReason,
    /// Sanitized TOML path or proposal-relative path.
    pub path: String,
    /// Field attached to the diagnostic, when applicable.
    pub field: Option<String>,
    /// Expected type, bound, or value.
    pub expected: Option<String>,
    /// Sanitized observed type, bound, or value.
    pub actual: Option<String>,
}

impl InterfaceProposalError {
    /// Construct a structured interface-proposal diagnostic.
    pub fn new(
        category: InterfaceProposalErrorCategory,
        reason_code: InterfaceProposalErrorReason,
        path: impl Into<String>,
        field: Option<String>,
        expected: Option<String>,
        actual: Option<String>,
    ) -> Self {
        Self {
            category,
            reason_code,
            path: path.into(),
            field: field.map(|value| bounded_diagnostic(&value)),
            expected: expected.map(|value| bounded_diagnostic(&value)),
            actual: actual.map(|value| bounded_diagnostic(&value)),
        }
    }
}

impl fmt::Display for InterfaceProposalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at {}", self.reason_code.as_str(), self.path)
    }
}

impl std::error::Error for InterfaceProposalError {}

/// Compute the SHA-256 hash of the exact proposal-file bytes.
pub fn interface_proposal_file_hash(bytes: &[u8]) -> PackageHash {
    package_file_hash(bytes)
}

/// Parse one UTF-8 v1 proposal from exact TOML bytes.
pub fn parse_interface_proposal(bytes: &[u8]) -> InterfaceProposalResult<InterfaceProposal> {
    if bytes.len() > MAX_PROPOSAL_FILE_BYTES {
        return Err(resource_error(
            InterfaceProposalErrorReason::ProposalFileBytesExceeded,
            "$",
            None,
            MAX_PROPOSAL_FILE_BYTES,
            bytes.len(),
        ));
    }

    let source = str::from_utf8(bytes).map_err(|error| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Syntax,
            InterfaceProposalErrorReason::InvalidUtf8,
            "$",
            None,
            Some("UTF-8 TOML bytes".to_owned()),
            Some(error.to_string()),
        )
    })?;
    parse_interface_proposal_str(source)
}

/// Parse one v1 proposal from a UTF-8 TOML string.
pub fn parse_interface_proposal_str(source: &str) -> InterfaceProposalResult<InterfaceProposal> {
    if source.len() > MAX_PROPOSAL_FILE_BYTES {
        return Err(resource_error(
            InterfaceProposalErrorReason::ProposalFileBytesExceeded,
            "$",
            None,
            MAX_PROPOSAL_FILE_BYTES,
            source.len(),
        ));
    }

    let value = source.parse::<Value>().map_err(|error| {
        let message = error.message();
        let reason = if message.contains("duplicate key") {
            InterfaceProposalErrorReason::DuplicateKey
        } else {
            InterfaceProposalErrorReason::InvalidToml
        };
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Syntax,
            reason,
            "$",
            None,
            Some("valid TOML table".to_owned()),
            Some(message.to_owned()),
        )
    })?;
    let root = value
        .as_table()
        .ok_or_else(|| wrong_type_error("$", None, "table", value_type_name(&value)))?;
    reject_unknown_fields("$", root, TOP_LEVEL_FIELDS)?;

    let schema = required_string(root, "$", "schema")?;
    if schema != INTERFACE_PROPOSAL_SCHEMA {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Syntax,
            InterfaceProposalErrorReason::UnknownSchema,
            "schema",
            Some("schema".to_owned()),
            Some(INTERFACE_PROPOSAL_SCHEMA.to_owned()),
            Some(schema),
        ));
    }

    let interface_status = parse_status(root, "$", "interface_status")?;

    let declarations = table_rows(
        root,
        "$",
        "declarations",
        MAX_DECLARATIONS,
        InterfaceProposalErrorReason::DeclarationCountExceeded,
    )?
    .into_iter()
    .enumerate()
    .map(|(index, table)| parse_declaration(index, table, interface_status))
    .collect::<InterfaceProposalResult<Vec<_>>>()?;
    let observations = table_rows(
        root,
        "$",
        "observations",
        MAX_OBSERVATIONS,
        InterfaceProposalErrorReason::ObservationCountExceeded,
    )?
    .into_iter()
    .enumerate()
    .map(|(index, table)| parse_observation(index, table))
    .collect::<InterfaceProposalResult<Vec<_>>>()?;
    let proof_references = table_rows(
        root,
        "$",
        "proof_references",
        MAX_PROOF_REFERENCES,
        InterfaceProposalErrorReason::ProofReferenceCountExceeded,
    )?
    .into_iter()
    .enumerate()
    .map(|(index, table)| parse_proof_reference(index, table))
    .collect::<InterfaceProposalResult<Vec<_>>>()?;
    let alternatives = table_rows(
        root,
        "$",
        "alternatives",
        MAX_ALTERNATIVES,
        InterfaceProposalErrorReason::AlternativeCountExceeded,
    )?
    .into_iter()
    .enumerate()
    .map(|(index, table)| parse_alternative(index, table))
    .collect::<InterfaceProposalResult<Vec<_>>>()?;

    Ok(InterfaceProposal {
        schema,
        proposal_id: required_string(root, "$", "proposal_id")?,
        proposal_revision: required_revision(root, "$", "proposal_revision")?,
        previous_proposal_hash: optional_hash(root, "$", "previous_proposal_hash")?,
        module: required_string(root, "$", "module")?,
        change_kind: parse_change_kind(root, "$", "change_kind")?,
        source_modules: required_string_array(
            root,
            "$",
            "source_modules",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?,
        change_group: optional_string(root, "$", "change_group")?,
        interface_status,
        proof_evidence: required_bool(root, "$", "proof_evidence")?,
        summary: required_string(root, "$", "summary")?,
        scope: required_string(root, "$", "scope")?,
        imports: required_string_array(
            root,
            "$",
            "imports",
            MAX_IMPORTS,
            InterfaceProposalErrorReason::ImportCountExceeded,
        )?,
        adoption_date: optional_string(root, "$", "adoption_date")?,
        adoption_rationale: optional_string(root, "$", "adoption_rationale")?,
        re_adoption_rationale: optional_string(root, "$", "re_adoption_rationale")?,
        withdrawal_rationale: optional_string(root, "$", "withdrawal_rationale")?,
        alternatives_review: optional_string(root, "$", "alternatives_review")?,
        supersedes: required_string_array(
            root,
            "$",
            "supersedes",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?,
        superseded_by: optional_string_array(
            root,
            "$",
            "superseded_by",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?,
        declarations,
        observations,
        proof_references,
        alternatives,
    })
}

const TOP_LEVEL_FIELDS: &[&str] = &[
    "schema",
    "proposal_id",
    "proposal_revision",
    "previous_proposal_hash",
    "module",
    "change_kind",
    "source_modules",
    "change_group",
    "interface_status",
    "proof_evidence",
    "summary",
    "scope",
    "imports",
    "adoption_date",
    "adoption_rationale",
    "re_adoption_rationale",
    "withdrawal_rationale",
    "alternatives_review",
    "supersedes",
    "superseded_by",
    "declarations",
    "observations",
    "proof_references",
    "alternatives",
];

const DECLARATION_FIELDS: &[&str] = &[
    "name",
    "kind",
    "surface",
    "signature",
    "body",
    "family_members",
    "semantic_role",
    "depends_on",
    "evidence_ids",
    "foundation_exception",
    "support_rationale",
    "proof_reference_ids",
    "proof_reference_exception",
];

const OBSERVATION_FIELDS: &[&str] = &[
    "id",
    "repository",
    "revision_kind",
    "revision",
    "license",
    "path",
    "source_module",
    "source_declaration",
    "usage_kind",
    "notes",
];

const PROOF_REFERENCE_FIELDS: &[&str] = &[
    "id",
    "repository",
    "revision_kind",
    "revision",
    "license",
    "path",
    "source_module",
    "source_declaration",
    "reference_role",
    "notes",
];

const ALTERNATIVE_FIELDS: &[&str] = &[
    "kind",
    "candidate",
    "disposition",
    "rationale",
    "evidence_ids",
];

fn parse_declaration(
    index: usize,
    table: &Table,
    interface_status: InterfaceProposalStatus,
) -> InterfaceProposalResult<InterfaceProposalDeclaration> {
    let path = format!("declarations[{index}]");
    reject_unknown_fields(&path, table, DECLARATION_FIELDS)?;
    Ok(InterfaceProposalDeclaration {
        name: required_string(table, &path, "name")?,
        kind: parse_declaration_kind(table, &path, "kind")?,
        surface: parse_surface(table, &path, "surface")?,
        signature: optional_string(table, &path, "signature")?,
        body: optional_string(table, &path, "body")?,
        family_members: optional_string_array(
            table,
            &path,
            "family_members",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?
        .unwrap_or_default(),
        semantic_role: required_string(table, &path, "semantic_role")?,
        depends_on: if matches!(
            interface_status,
            InterfaceProposalStatus::Observed | InterfaceProposalStatus::Withdrawn
        ) {
            optional_string_array(
                table,
                &path,
                "depends_on",
                MAX_LINKS_PER_ARRAY,
                InterfaceProposalErrorReason::LinkCountExceeded,
            )?
            .unwrap_or_default()
        } else {
            required_string_array(
                table,
                &path,
                "depends_on",
                MAX_LINKS_PER_ARRAY,
                InterfaceProposalErrorReason::LinkCountExceeded,
            )?
        },
        evidence_ids: required_string_array(
            table,
            &path,
            "evidence_ids",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?,
        foundation_exception: optional_string(table, &path, "foundation_exception")?,
        support_rationale: optional_string(table, &path, "support_rationale")?,
        proof_reference_ids: optional_string_array(
            table,
            &path,
            "proof_reference_ids",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?
        .unwrap_or_default(),
        proof_reference_exception: optional_string(table, &path, "proof_reference_exception")?,
    })
}

fn parse_observation(
    index: usize,
    table: &Table,
) -> InterfaceProposalResult<InterfaceProposalObservation> {
    let path = format!("observations[{index}]");
    reject_unknown_fields(&path, table, OBSERVATION_FIELDS)?;
    Ok(InterfaceProposalObservation {
        id: required_string(table, &path, "id")?,
        repository: required_string(table, &path, "repository")?,
        revision_kind: parse_revision_kind(table, &path, "revision_kind")?,
        revision: required_string(table, &path, "revision")?,
        license: required_string(table, &path, "license")?,
        path: required_path(table, &path, "path")?,
        source_module: optional_string(table, &path, "source_module")?,
        source_declaration: optional_string(table, &path, "source_declaration")?,
        usage_kind: parse_usage_kind(table, &path, "usage_kind")?,
        notes: required_string(table, &path, "notes")?,
    })
}

fn parse_proof_reference(
    index: usize,
    table: &Table,
) -> InterfaceProposalResult<InterfaceProposalProofReference> {
    let path = format!("proof_references[{index}]");
    reject_unknown_fields(&path, table, PROOF_REFERENCE_FIELDS)?;
    Ok(InterfaceProposalProofReference {
        id: required_string(table, &path, "id")?,
        repository: required_string(table, &path, "repository")?,
        revision_kind: parse_revision_kind(table, &path, "revision_kind")?,
        revision: required_string(table, &path, "revision")?,
        license: required_string(table, &path, "license")?,
        path: required_path(table, &path, "path")?,
        source_module: optional_string(table, &path, "source_module")?,
        source_declaration: required_string(table, &path, "source_declaration")?,
        reference_role: parse_reference_role(table, &path, "reference_role")?,
        notes: required_string(table, &path, "notes")?,
    })
}

fn parse_alternative(
    index: usize,
    table: &Table,
) -> InterfaceProposalResult<InterfaceProposalAlternative> {
    let path = format!("alternatives[{index}]");
    reject_unknown_fields(&path, table, ALTERNATIVE_FIELDS)?;
    Ok(InterfaceProposalAlternative {
        kind: parse_alternative_kind(table, &path, "kind")?,
        candidate: required_string(table, &path, "candidate")?,
        disposition: parse_alternative_disposition(table, &path, "disposition")?,
        rationale: required_string(table, &path, "rationale")?,
        evidence_ids: required_string_array(
            table,
            &path,
            "evidence_ids",
            MAX_LINKS_PER_ARRAY,
            InterfaceProposalErrorReason::LinkCountExceeded,
        )?,
    })
}

fn parse_status(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalStatus> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "observed" => Ok(InterfaceProposalStatus::Observed),
        "proposed" => Ok(InterfaceProposalStatus::Proposed),
        "adopted" => Ok(InterfaceProposalStatus::Adopted),
        "withdrawn" => Ok(InterfaceProposalStatus::Withdrawn),
        "superseded" => Ok(InterfaceProposalStatus::Superseded),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "observed|proposed|adopted|withdrawn|superseded",
            &value,
        )),
    }
}

fn parse_change_kind(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalChangeKind> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "add" => Ok(InterfaceProposalChangeKind::Add),
        "revise" => Ok(InterfaceProposalChangeKind::Revise),
        "rename" => Ok(InterfaceProposalChangeKind::Rename),
        "split" => Ok(InterfaceProposalChangeKind::Split),
        "merge" => Ok(InterfaceProposalChangeKind::Merge),
        "replace" => Ok(InterfaceProposalChangeKind::Replace),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "add|revise|rename|split|merge|replace",
            &value,
        )),
    }
}

fn parse_declaration_kind(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalDeclarationKind> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "inductive" => Ok(InterfaceProposalDeclarationKind::Inductive),
        "definition" => Ok(InterfaceProposalDeclarationKind::Definition),
        "theorem" => Ok(InterfaceProposalDeclarationKind::Theorem),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "inductive|definition|theorem",
            &value,
        )),
    }
}

fn parse_surface(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalSurface> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "public" => Ok(InterfaceProposalSurface::Public),
        "support" => Ok(InterfaceProposalSurface::Support),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "public|support",
            &value,
        )),
    }
}

fn parse_revision_kind(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalRevisionKind> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "git_commit" => Ok(InterfaceProposalRevisionKind::GitCommit),
        "release_digest" => Ok(InterfaceProposalRevisionKind::ReleaseDigest),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "git_commit|release_digest",
            &value,
        )),
    }
}

fn parse_usage_kind(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalUsageKind> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "declaration" => Ok(InterfaceProposalUsageKind::Declaration),
        "module_import" => Ok(InterfaceProposalUsageKind::ModuleImport),
        "direct_application" => Ok(InterfaceProposalUsageKind::DirectApplication),
        "rewrite" => Ok(InterfaceProposalUsageKind::Rewrite),
        "instance_dependency" => Ok(InterfaceProposalUsageKind::InstanceDependency),
        "transitive_dependency" => Ok(InterfaceProposalUsageKind::TransitiveDependency),
        "module_layout" => Ok(InterfaceProposalUsageKind::ModuleLayout),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "declaration|module_import|direct_application|rewrite|instance_dependency|transitive_dependency|module_layout",
            &value,
        )),
    }
}

fn parse_reference_role(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalReferenceRole> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "proof_structure" => Ok(InterfaceProposalReferenceRole::ProofStructure),
        "lemma_choice" => Ok(InterfaceProposalReferenceRole::LemmaChoice),
        "induction_scheme" => Ok(InterfaceProposalReferenceRole::InductionScheme),
        "normalization_strategy" => Ok(InterfaceProposalReferenceRole::NormalizationStrategy),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "proof_structure|lemma_choice|induction_scheme|normalization_strategy",
            &value,
        )),
    }
}

fn parse_alternative_kind(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalAlternativeKind> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "module_name" => Ok(InterfaceProposalAlternativeKind::ModuleName),
        "declaration_name" => Ok(InterfaceProposalAlternativeKind::DeclarationName),
        "signature" => Ok(InterfaceProposalAlternativeKind::Signature),
        "module_boundary" => Ok(InterfaceProposalAlternativeKind::ModuleBoundary),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "module_name|declaration_name|signature|module_boundary",
            &value,
        )),
    }
}

fn parse_alternative_disposition(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<InterfaceProposalAlternativeDisposition> {
    let value = required_string(table, path, field)?;
    match value.as_str() {
        "rejected" => Ok(InterfaceProposalAlternativeDisposition::Rejected),
        "deferred" => Ok(InterfaceProposalAlternativeDisposition::Deferred),
        _ => Err(invalid_enum_error(
            field_path(path, field),
            field,
            "rejected|deferred",
            &value,
        )),
    }
}

fn required_revision(table: &Table, path: &str, field: &str) -> InterfaceProposalResult<u64> {
    let value = required_value(table, path, field)?;
    let Some(revision) = value.as_integer() else {
        return Err(wrong_type_error(
            field_path(path, field),
            Some(field.to_owned()),
            "positive integer",
            value_type_name(value),
        ));
    };
    if revision < 1 {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::InvalidRevision,
            field_path(path, field),
            Some(field.to_owned()),
            Some("positive integer".to_owned()),
            Some(revision.to_string()),
        ));
    }
    Ok(revision as u64)
}

fn required_bool(table: &Table, path: &str, field: &str) -> InterfaceProposalResult<bool> {
    let value = required_value(table, path, field)?;
    value.as_bool().ok_or_else(|| {
        wrong_type_error(
            field_path(path, field),
            Some(field.to_owned()),
            "bool",
            value_type_name(value),
        )
    })
}

fn required_string(table: &Table, path: &str, field: &str) -> InterfaceProposalResult<String> {
    let value = required_value(table, path, field)?;
    let value = value.as_str().ok_or_else(|| {
        wrong_type_error(
            field_path(path, field),
            Some(field.to_owned()),
            "nonempty string",
            value_type_name(value),
        )
    })?;
    copy_string(
        value,
        field_path(path, field),
        Some(field.to_owned()),
        false,
    )
}

fn optional_string(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<Option<String>> {
    table
        .get(field)
        .map(|value| {
            let value = value.as_str().ok_or_else(|| {
                wrong_type_error(
                    field_path(path, field),
                    Some(field.to_owned()),
                    "nonempty string",
                    value_type_name(value),
                )
            })?;
            copy_string(
                value,
                field_path(path, field),
                Some(field.to_owned()),
                false,
            )
        })
        .transpose()
}

fn required_path(table: &Table, path: &str, field: &str) -> InterfaceProposalResult<String> {
    let value = required_value(table, path, field)?;
    let value = value.as_str().ok_or_else(|| {
        wrong_type_error(
            field_path(path, field),
            Some(field.to_owned()),
            "nonempty path string",
            value_type_name(value),
        )
    })?;
    copy_string(value, field_path(path, field), Some(field.to_owned()), true)
}

fn required_value<'a>(
    table: &'a Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<&'a Value> {
    table.get(field).ok_or_else(|| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::MissingField,
            path,
            Some(field.to_owned()),
            Some("present".to_owned()),
            None,
        )
    })
}

fn optional_hash(
    table: &Table,
    path: &str,
    field: &str,
) -> InterfaceProposalResult<Option<PackageHash>> {
    optional_string(table, path, field)?
        .map(|value| parse_hash(&value, field_path(path, field), field))
        .transpose()
}

fn parse_hash(value: &str, path: String, field: &str) -> InterfaceProposalResult<PackageHash> {
    parse_package_hash(value, &path).map_err(|_| {
        InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::InvalidHash,
            path,
            Some(field.to_owned()),
            Some("sha256:<64 lowercase hex>".to_owned()),
            Some(value.to_owned()),
        )
    })
}

fn required_string_array(
    table: &Table,
    path: &str,
    field: &str,
    limit: usize,
    limit_reason: InterfaceProposalErrorReason,
) -> InterfaceProposalResult<Vec<String>> {
    let value = required_value(table, path, field)?;
    string_array_from_value(
        value,
        &field_path(path, field),
        Some(field.to_owned()),
        limit,
        limit_reason,
    )
}

fn optional_string_array(
    table: &Table,
    path: &str,
    field: &str,
    limit: usize,
    limit_reason: InterfaceProposalErrorReason,
) -> InterfaceProposalResult<Option<Vec<String>>> {
    table
        .get(field)
        .map(|value| {
            string_array_from_value(
                value,
                &field_path(path, field),
                Some(field.to_owned()),
                limit,
                limit_reason,
            )
        })
        .transpose()
}

fn string_array_from_value(
    value: &Value,
    path: &str,
    field: Option<String>,
    limit: usize,
    limit_reason: InterfaceProposalErrorReason,
) -> InterfaceProposalResult<Vec<String>> {
    let array = value.as_array().ok_or_else(|| {
        wrong_type_error(
            path,
            field.clone(),
            "array of strings",
            value_type_name(value),
        )
    })?;
    if array.len() > limit {
        return Err(resource_error(
            limit_reason,
            path,
            field,
            limit,
            array.len(),
        ));
    }
    let mut strings = Vec::with_capacity(array.len());
    for (index, item) in array.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let item = item
            .as_str()
            .ok_or_else(|| wrong_type_error(&item_path, None, "string", value_type_name(item)))?;
        strings.push(copy_string(item, item_path, None, false)?);
    }
    Ok(strings)
}

fn table_rows<'a>(
    root: &'a Table,
    path: &str,
    field: &str,
    limit: usize,
    limit_reason: InterfaceProposalErrorReason,
) -> InterfaceProposalResult<Vec<&'a Table>> {
    let Some(value) = root.get(field) else {
        return Ok(Vec::new());
    };
    let field_path = field_path(path, field);
    let array = value.as_array().ok_or_else(|| {
        wrong_type_error(
            &field_path,
            Some(field.to_owned()),
            "array of tables",
            value_type_name(value),
        )
    })?;
    if array.len() > limit {
        return Err(resource_error(
            limit_reason,
            &field_path,
            Some(field.to_owned()),
            limit,
            array.len(),
        ));
    }
    let mut tables = Vec::with_capacity(array.len());
    for (index, item) in array.iter().enumerate() {
        let item_path = format!("{field_path}[{index}]");
        tables.push(
            item.as_table().ok_or_else(|| {
                wrong_type_error(&item_path, None, "table", value_type_name(item))
            })?,
        );
    }
    Ok(tables)
}

fn reject_unknown_fields(
    path: &str,
    table: &Table,
    allowed: &[&str],
) -> InterfaceProposalResult<()> {
    for key in table.keys() {
        if !allowed.iter().any(|allowed_key| allowed_key == key) {
            return Err(InterfaceProposalError::new(
                InterfaceProposalErrorCategory::Syntax,
                InterfaceProposalErrorReason::UnknownField,
                path,
                Some(bounded_diagnostic(key)),
                Some("field in v1 schema".to_owned()),
                None,
            ));
        }
    }
    Ok(())
}

fn copy_string(
    value: &str,
    path: String,
    field: Option<String>,
    is_path: bool,
) -> InterfaceProposalResult<String> {
    let limit = if is_path {
        MAX_PATH_BYTES
    } else {
        MAX_STRING_BYTES
    };
    let reason = if is_path {
        InterfaceProposalErrorReason::PathBytesExceeded
    } else {
        InterfaceProposalErrorReason::StringBytesExceeded
    };
    if value.len() > limit {
        return Err(resource_error(reason, &path, field, limit, value.len()));
    }
    if value.is_empty() {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Contract,
            InterfaceProposalErrorReason::EmptyValue,
            path,
            field,
            Some("nonempty string".to_owned()),
            Some(String::new()),
        ));
    }
    if is_path
        && value
            .bytes()
            .any(|byte| byte == b'\t' || byte == b'\n' || byte == b'\r')
    {
        return Err(InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Discovery,
            InterfaceProposalErrorReason::PathContainsTabOrNewline,
            path,
            field,
            Some("path without tab or newline".to_owned()),
            Some(value.to_owned()),
        ));
    }
    Ok(value.to_owned())
}

fn wrong_type_error(
    path: impl Into<String>,
    field: Option<String>,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Syntax,
        InterfaceProposalErrorReason::WrongType,
        path,
        field,
        Some(expected.into()),
        Some(actual.into()),
    )
}

fn invalid_enum_error(
    path: impl Into<String>,
    field: &str,
    expected: &str,
    actual: &str,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Syntax,
        InterfaceProposalErrorReason::InvalidEnum,
        path,
        Some(field.to_owned()),
        Some(expected.to_owned()),
        Some(actual.to_owned()),
    )
}

fn resource_error(
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<String>,
    expected: usize,
    actual: usize,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        InterfaceProposalErrorCategory::Resource,
        reason,
        path,
        field,
        Some(expected.to_string()),
        Some(actual.to_string()),
    )
}

fn field_path(path: &str, field: &str) -> String {
    if path == "$" {
        field.to_owned()
    } else {
        format!("{path}.{field}")
    }
}

fn value_type_name(value: &Value) -> &'static str {
    match value {
        Value::String(_) => "string",
        Value::Integer(_) => "integer",
        Value::Float(_) => "float",
        Value::Boolean(_) => "bool",
        Value::Datetime(_) => "datetime",
        Value::Array(_) => "array",
        Value::Table(_) => "table",
    }
}

fn bounded_diagnostic(value: &str) -> String {
    if value.len() <= MAX_DIAGNOSTIC_VALUE_BYTES {
        return value.to_owned();
    }
    let mut end = MAX_DIAGNOSTIC_VALUE_BYTES;
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    value[..end].to_owned()
}

/// Validate one parsed proposal without reading any external state.
///
/// This pass checks the v1 record contract, lifecycle metadata, local
/// declaration/evidence references, support closure, immutable locator shape,
/// and declaration dependency cycles. It deliberately does not resolve
/// imports against a package, parse NPA terms with the frontend, inspect
/// certificates or source files, contact Git/network services, or claim proof
/// verification. Those checks belong to later validator layers.
pub fn validate_interface_proposal(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    validate_schema(proposal)?;
    validate_revision_metadata(proposal)?;
    validate_identifiers(proposal)?;
    validate_proof_boundary(proposal)?;
    validate_top_level_collections(proposal)?;
    validate_status_metadata(proposal)?;

    let observation_ids = validate_observations(&proposal.observations)?;
    let proof_reference_ids = validate_proof_references(&proposal.proof_references)?;
    validate_alternatives(proposal, &observation_ids)?;
    let declaration_names =
        validate_declarations(proposal, &observation_ids, &proof_reference_ids)?;
    validate_dependency_cycles(proposal, &declaration_names)?;
    validate_support_closure(proposal, &declaration_names)?;
    validate_adoption_licenses(proposal, &observation_ids, &proof_reference_ids)?;
    Ok(())
}

/// Parse and validate one proposal from exact UTF-8 TOML bytes.
pub fn parse_and_validate_interface_proposal(
    bytes: &[u8],
) -> InterfaceProposalResult<InterfaceProposal> {
    let proposal = parse_interface_proposal(bytes)?;
    validate_interface_proposal(&proposal)?;
    Ok(proposal)
}

fn validate_schema(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    if proposal.schema == INTERFACE_PROPOSAL_SCHEMA {
        Ok(())
    } else {
        Err(validation_error(
            InterfaceProposalErrorCategory::Syntax,
            InterfaceProposalErrorReason::UnknownSchema,
            "schema",
            Some("schema"),
            Some(INTERFACE_PROPOSAL_SCHEMA.to_owned()),
            Some(proposal.schema.clone()),
        ))
    }
}

fn validate_revision_metadata(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    if proposal.proposal_revision == 0 {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidRevision,
            "proposal_revision",
            Some("proposal_revision"),
            "positive integer",
            Some(proposal.proposal_revision.to_string()),
        ));
    }
    match (proposal.proposal_revision, proposal.previous_proposal_hash) {
        (1, Some(_)) => Err(contract_error(
            InterfaceProposalErrorReason::InvalidRevision,
            "previous_proposal_hash",
            Some("previous_proposal_hash"),
            "omitted at revision 1",
            Some("present".to_owned()),
        )),
        (revision, None) if revision > 1 => Err(contract_error(
            InterfaceProposalErrorReason::InvalidRevision,
            "previous_proposal_hash",
            Some("previous_proposal_hash"),
            "present at revisions after 1",
            Some("missing".to_owned()),
        )),
        _ => Ok(()),
    }
}

fn validate_identifiers(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    if !is_canonical_module_name(&proposal.module) || !proposal.module.starts_with("Mathlib.") {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidModuleName,
            "module",
            Some("module"),
            "canonical Mathlib.* module name",
            Some(proposal.module.clone()),
        ));
    }
    if !is_stable_identifier(&proposal.proposal_id) {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidIdentifier,
            "proposal_id",
            Some("proposal_id"),
            "nonempty stable identifier",
            Some(proposal.proposal_id.clone()),
        ));
    }
    if proposal.proposal_revision == 1 && proposal.proposal_id != proposal.module {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidIdentifier,
            "proposal_id",
            Some("proposal_id"),
            "equal to module at revision 1",
            Some(proposal.proposal_id.clone()),
        ));
    }
    if let Some(group) = &proposal.change_group {
        if !is_stable_identifier(group) {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidIdentifier,
                "change_group",
                Some("change_group"),
                "nonempty stable identifier",
                Some(group.clone()),
            ));
        }
    }
    for (index, module) in proposal.source_modules.iter().enumerate() {
        if !is_canonical_module_name(module) || !module.starts_with("Mathlib.") {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidModuleName,
                format!("source_modules[{index}]"),
                Some("source_modules"),
                "canonical Mathlib.* module name",
                Some(module.clone()),
            ));
        }
    }
    for (index, import) in proposal.imports.iter().enumerate() {
        if !is_canonical_module_name(import)
            || !(import.starts_with("Mathlib.") || import.starts_with("Std."))
        {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidModuleName,
                format!("imports[{index}]"),
                Some("imports"),
                "canonical Mathlib.* or Std.* module name",
                Some(import.clone()),
            ));
        }
    }
    for (field, values) in [
        ("supersedes", proposal.supersedes.as_slice()),
        (
            "superseded_by",
            proposal.superseded_by.as_deref().unwrap_or_default(),
        ),
    ] {
        for (index, value) in values.iter().enumerate() {
            if !is_stable_identifier(value) {
                return Err(contract_error(
                    InterfaceProposalErrorReason::InvalidIdentifier,
                    format!("{field}[{index}]"),
                    Some(field),
                    "nonempty stable identifier",
                    Some(value.clone()),
                ));
            }
        }
    }
    Ok(())
}

fn validate_proof_boundary(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    if proposal.proof_evidence {
        return Err(contract_error(
            InterfaceProposalErrorReason::ProofEvidenceNotFalse,
            "proof_evidence",
            Some("proof_evidence"),
            "false",
            Some("true".to_owned()),
        ));
    }
    Ok(())
}

fn validate_top_level_collections(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    validate_unique_strings(
        &proposal.imports,
        "imports",
        InterfaceProposalErrorReason::DuplicateSetMember,
        InterfaceProposalErrorCategory::Contract,
    )?;
    validate_unique_strings(
        &proposal.supersedes,
        "supersedes",
        InterfaceProposalErrorReason::DuplicateSetMember,
        InterfaceProposalErrorCategory::Contract,
    )?;
    validate_unique_strings(
        &proposal.source_modules,
        "source_modules",
        InterfaceProposalErrorReason::DuplicateSetMember,
        InterfaceProposalErrorCategory::Contract,
    )?;
    if !is_sorted_by_bytes(&proposal.source_modules) {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidSourceModules,
            "source_modules",
            Some("source_modules"),
            "unique UTF-8 byte-sorted array",
            Some("unsorted".to_owned()),
        ));
    }
    if let Some(superseded_by) = &proposal.superseded_by {
        validate_unique_strings(
            superseded_by,
            "superseded_by",
            InterfaceProposalErrorReason::DuplicateSetMember,
            InterfaceProposalErrorCategory::Contract,
        )?;
        if !is_sorted_by_bytes(superseded_by) {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidSupersededByOrder,
                "superseded_by",
                Some("superseded_by"),
                "unique UTF-8 byte-sorted nonempty array",
                Some("unsorted".to_owned()),
            ));
        }
    }
    validate_change_kind(proposal)
}

fn validate_change_kind(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    let source_count = proposal.source_modules.len();
    let valid = match proposal.change_kind {
        InterfaceProposalChangeKind::Add => source_count == 0,
        InterfaceProposalChangeKind::Revise => {
            source_count == 1 && proposal.source_modules[0] == proposal.module
        }
        InterfaceProposalChangeKind::Rename | InterfaceProposalChangeKind::Replace => {
            source_count == 1 && proposal.source_modules[0] != proposal.module
        }
        InterfaceProposalChangeKind::Split => source_count == 1,
        InterfaceProposalChangeKind::Merge => source_count >= 2,
    };
    if !valid {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidSourceModules,
            "source_modules",
            Some("source_modules"),
            proposal.change_kind.as_str(),
            Some(source_count.to_string()),
        ));
    }
    if proposal.change_kind == InterfaceProposalChangeKind::Split && proposal.change_group.is_none()
    {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidChangeGroup,
            "change_group",
            Some("change_group"),
            "nonempty group for split",
            Some("missing".to_owned()),
        ));
    }
    if proposal.change_kind != InterfaceProposalChangeKind::Split && proposal.change_group.is_some()
    {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidChangeGroup,
            "change_group",
            Some("change_group"),
            "omitted except for split",
            Some("present".to_owned()),
        ));
    }
    Ok(())
}

fn validate_status_metadata(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    let status = proposal.interface_status;
    let complete_surface = matches!(
        status,
        InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
            | InterfaceProposalStatus::Superseded
    );

    if complete_surface && proposal.declarations.is_empty() {
        return Err(lifecycle_error(
            InterfaceProposalErrorReason::StatusSurfaceIncomplete,
            "declarations",
            Some("declarations"),
            "nonempty declaration surface",
            Some("empty".to_owned()),
        ));
    }
    if matches!(
        status,
        InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
            | InterfaceProposalStatus::Superseded
    ) && proposal.alternatives_review.is_none()
    {
        return Err(evidence_error(
            InterfaceProposalErrorReason::MissingAlternativesReview,
            "alternatives_review",
            Some("alternatives_review"),
            "nonempty review text",
            Some("missing".to_owned()),
        ));
    }
    if let Some(review) = &proposal.alternatives_review {
        if review.trim().is_empty() || is_placeholder_text(review) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::MissingAlternativesReview,
                "alternatives_review",
                Some("alternatives_review"),
                "nonempty specific alternatives review",
                Some(review.clone()),
            ));
        }
    }

    match status {
        InterfaceProposalStatus::Observed => {
            reject_status_field(
                proposal.adoption_date.is_some(),
                "adoption_date",
                "omitted for observed",
            )?;
            reject_status_field(
                proposal.adoption_rationale.is_some(),
                "adoption_rationale",
                "omitted for observed",
            )?;
            reject_status_field(
                proposal.re_adoption_rationale.is_some(),
                "re_adoption_rationale",
                "omitted for observed",
            )?;
            reject_status_field(
                proposal.withdrawal_rationale.is_some(),
                "withdrawal_rationale",
                "omitted for observed",
            )?;
            reject_status_field(
                proposal.superseded_by.is_some(),
                "superseded_by",
                "omitted for observed",
            )?;
        }
        InterfaceProposalStatus::Proposed => {
            reject_status_field(
                proposal.adoption_date.is_some(),
                "adoption_date",
                "omitted for proposed",
            )?;
            reject_status_field(
                proposal.adoption_rationale.is_some(),
                "adoption_rationale",
                "omitted for proposed",
            )?;
            reject_status_field(
                proposal.re_adoption_rationale.is_some(),
                "re_adoption_rationale",
                "omitted for proposed",
            )?;
            reject_status_field(
                proposal.withdrawal_rationale.is_some(),
                "withdrawal_rationale",
                "omitted for proposed",
            )?;
            reject_status_field(
                proposal.superseded_by.is_some(),
                "superseded_by",
                "omitted for proposed",
            )?;
        }
        InterfaceProposalStatus::Adopted => {
            validate_adoption_fields(proposal)?;
            reject_status_field(
                proposal.withdrawal_rationale.is_some(),
                "withdrawal_rationale",
                "omitted for adopted",
            )?;
            reject_status_field(
                proposal.superseded_by.is_some(),
                "superseded_by",
                "omitted for adopted",
            )?;
        }
        InterfaceProposalStatus::Withdrawn => {
            if proposal
                .withdrawal_rationale
                .as_deref()
                .is_none_or(|rationale| {
                    rationale.trim().is_empty() || is_placeholder_text(rationale)
                })
            {
                return Err(lifecycle_error(
                    InterfaceProposalErrorReason::WithdrawalRationaleMissing,
                    "withdrawal_rationale",
                    Some("withdrawal_rationale"),
                    "nonempty rationale",
                    Some("missing".to_owned()),
                ));
            }
            reject_status_field(
                proposal.adoption_date.is_some(),
                "adoption_date",
                "omitted for withdrawn",
            )?;
            reject_status_field(
                proposal.adoption_rationale.is_some(),
                "adoption_rationale",
                "omitted for withdrawn",
            )?;
            reject_status_field(
                proposal.re_adoption_rationale.is_some(),
                "re_adoption_rationale",
                "omitted for withdrawn",
            )?;
            reject_status_field(
                proposal.superseded_by.is_some(),
                "superseded_by",
                "omitted for withdrawn",
            )?;
        }
        InterfaceProposalStatus::Superseded => {
            validate_adoption_fields(proposal)?;
            let Some(superseded_by) = &proposal.superseded_by else {
                return Err(lifecycle_error(
                    InterfaceProposalErrorReason::SupersessionMetadataMissing,
                    "superseded_by",
                    Some("superseded_by"),
                    "sorted nonempty successor IDs",
                    Some("missing".to_owned()),
                ));
            };
            if superseded_by.is_empty() {
                return Err(lifecycle_error(
                    InterfaceProposalErrorReason::SupersessionMetadataMissing,
                    "superseded_by",
                    Some("superseded_by"),
                    "sorted nonempty successor IDs",
                    Some("empty".to_owned()),
                ));
            }
            reject_status_field(
                proposal.re_adoption_rationale.is_some(),
                "re_adoption_rationale",
                "omitted for superseded",
            )?;
            reject_status_field(
                proposal.withdrawal_rationale.is_some(),
                "withdrawal_rationale",
                "omitted for superseded",
            )?;
        }
    }
    if let Some(date) = &proposal.adoption_date {
        validate_iso_date(date)?;
    }
    Ok(())
}

fn validate_adoption_fields(proposal: &InterfaceProposal) -> InterfaceProposalResult<()> {
    if proposal.adoption_date.is_none()
        || proposal
            .adoption_rationale
            .as_deref()
            .is_none_or(|rationale| rationale.trim().is_empty() || is_placeholder_text(rationale))
    {
        return Err(lifecycle_error(
            InterfaceProposalErrorReason::StatusMetadataMissing,
            "adoption_date",
            Some("adoption_date"),
            "adoption_date and adoption_rationale",
            Some("missing adoption metadata".to_owned()),
        ));
    }
    if let Some(rationale) = &proposal.re_adoption_rationale {
        if rationale.trim().is_empty() || is_placeholder_text(rationale) {
            return Err(lifecycle_error(
                InterfaceProposalErrorReason::ReadoptionMetadataMissing,
                "re_adoption_rationale",
                Some("re_adoption_rationale"),
                "nonempty re-adoption rationale",
                Some(rationale.clone()),
            ));
        }
    }
    Ok(())
}

fn reject_status_field(present: bool, field: &str, expected: &str) -> InterfaceProposalResult<()> {
    if present {
        Err(lifecycle_error(
            InterfaceProposalErrorReason::StatusMetadataMissing,
            field,
            Some(field),
            expected,
            Some("present".to_owned()),
        ))
    } else {
        Ok(())
    }
}

fn validate_iso_date(value: &str) -> InterfaceProposalResult<()> {
    let bytes = value.as_bytes();
    let valid_shape = bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && bytes
            .iter()
            .enumerate()
            .all(|(index, byte)| matches!(index, 4 | 7) || byte.is_ascii_digit());
    if !valid_shape {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidDate,
            "adoption_date",
            Some("adoption_date"),
            "ISO date YYYY-MM-DD",
            Some(value.to_owned()),
        ));
    }
    let year = value[0..4].parse::<u32>().unwrap_or_default();
    let month = value[5..7].parse::<u32>().unwrap_or_default();
    let day = value[8..10].parse::<u32>().unwrap_or_default();
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year % 400 == 0 || (year % 4 == 0 && year % 100 != 0) => 29,
        2 => 28,
        _ => 0,
    };
    if year == 0 || month == 0 || day == 0 || day > days {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidDate,
            "adoption_date",
            Some("adoption_date"),
            "calendar date YYYY-MM-DD",
            Some(value.to_owned()),
        ));
    }
    Ok(())
}

fn validation_error(
    category: InterfaceProposalErrorCategory,
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<&str>,
    expected: Option<String>,
    actual: Option<String>,
) -> InterfaceProposalError {
    InterfaceProposalError::new(
        category,
        reason,
        path,
        field.map(ToOwned::to_owned),
        expected,
        actual,
    )
}

fn contract_error(
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<&str>,
    expected: &str,
    actual: Option<String>,
) -> InterfaceProposalError {
    validation_error(
        InterfaceProposalErrorCategory::Contract,
        reason,
        path,
        field,
        Some(expected.to_owned()),
        actual,
    )
}

fn lifecycle_error(
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<&str>,
    expected: &str,
    actual: Option<String>,
) -> InterfaceProposalError {
    validation_error(
        InterfaceProposalErrorCategory::Lifecycle,
        reason,
        path,
        field,
        Some(expected.to_owned()),
        actual,
    )
}

fn evidence_error(
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<&str>,
    expected: &str,
    actual: Option<String>,
) -> InterfaceProposalError {
    validation_error(
        InterfaceProposalErrorCategory::Evidence,
        reason,
        path,
        field,
        Some(expected.to_owned()),
        actual,
    )
}

fn graph_error(
    reason: InterfaceProposalErrorReason,
    path: impl Into<String>,
    field: Option<&str>,
    expected: &str,
    actual: Option<String>,
) -> InterfaceProposalError {
    validation_error(
        InterfaceProposalErrorCategory::Graph,
        reason,
        path,
        field,
        Some(expected.to_owned()),
        actual,
    )
}

fn validate_unique_strings(
    values: &[String],
    path: &str,
    reason: InterfaceProposalErrorReason,
    category: InterfaceProposalErrorCategory,
) -> InterfaceProposalResult<()> {
    let mut seen = BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        if !seen.insert(value.as_str()) {
            return Err(validation_error(
                category,
                reason,
                format!("{path}[{index}]"),
                Some(path),
                None,
                Some(value.clone()),
            ));
        }
    }
    Ok(())
}

fn is_sorted_by_bytes(values: &[String]) -> bool {
    values
        .windows(2)
        .all(|pair| pair[0].as_bytes() <= pair[1].as_bytes())
}

fn is_canonical_module_name(value: &str) -> bool {
    Name::from_dotted(value).is_canonical()
}

fn is_stable_identifier(value: &str) -> bool {
    !value.is_empty()
        && !value
            .chars()
            .any(|character| character.is_control() || character.is_whitespace())
        && !value.contains('/')
        && !value.contains('\\')
        && !value.starts_with('.')
        && !value.ends_with('.')
        && !value.contains("..")
}

fn is_unqualified_name(value: &str) -> bool {
    !value.contains('.') && Name::from_dotted(value).is_canonical()
}

fn is_canonical_name(value: &str) -> bool {
    Name::from_dotted(value).is_canonical()
}

fn validate_source_path(path: &str, diagnostic_path: &str) -> InterfaceProposalResult<()> {
    let valid = !path.is_empty()
        && !path.starts_with('/')
        && !path.contains('\\')
        && !path.chars().any(char::is_control)
        && !path.contains(':')
        && path
            .split('/')
            .all(|component| !component.is_empty() && component != "." && component != "..");
    if valid {
        Ok(())
    } else {
        Err(evidence_error(
            InterfaceProposalErrorReason::MissingSourceLocation,
            diagnostic_path,
            Some("path"),
            "repository-relative path without escape components",
            Some(path.to_owned()),
        ))
    }
}

fn validate_revision_locator(
    kind: InterfaceProposalRevisionKind,
    revision: &str,
    path: &str,
) -> InterfaceProposalResult<()> {
    let valid = match kind {
        InterfaceProposalRevisionKind::GitCommit => revision.len() == 40 && is_lower_hex(revision),
        InterfaceProposalRevisionKind::ReleaseDigest => {
            revision.starts_with(INTERFACE_PROPOSAL_HASH_PREFIX)
                && revision.len() == INTERFACE_PROPOSAL_HASH_PREFIX.len() + 64
                && is_lower_hex(&revision[INTERFACE_PROPOSAL_HASH_PREFIX.len()..])
        }
    };
    if valid {
        Ok(())
    } else {
        let reason = if looks_like_floating_revision(revision) {
            InterfaceProposalErrorReason::FloatingRevision
        } else {
            InterfaceProposalErrorReason::InvalidRevisionLocator
        };
        Err(evidence_error(
            reason,
            path,
            Some("revision"),
            kind.as_str(),
            Some(revision.to_owned()),
        ))
    }
}

fn is_lower_hex(value: &str) -> bool {
    value
        .bytes()
        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn looks_like_floating_revision(value: &str) -> bool {
    value.len() < 40
        && !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-' | b'/'))
}

fn unknown_license_note_is_sufficient(notes: &str) -> bool {
    let lower = notes.to_ascii_lowercase();
    ["follow", "pending", "resolve", "review", "confirm"]
        .iter()
        .any(|marker| lower.contains(marker))
}

fn is_placeholder_text(value: &str) -> bool {
    let lower = value.to_ascii_lowercase();
    value.contains("...")
        || value.contains('…')
        || lower.contains("todo")
        || lower.contains("placeholder")
        || lower.contains("not yet specified")
        || value.contains("???")
}

fn contains_quotient_construction(value: &str) -> bool {
    let lower = value.to_ascii_lowercase();
    lower.contains("quotient") || value.contains("Quot")
}

fn validate_observations(
    observations: &[InterfaceProposalObservation],
) -> InterfaceProposalResult<BTreeSet<String>> {
    let mut ids = BTreeSet::new();
    for (index, observation) in observations.iter().enumerate() {
        let path = format!("observations[{index}]");
        if !is_stable_identifier(&observation.id) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidIdentifier,
                format!("{path}.id"),
                Some("id"),
                "nonempty stable identifier",
                Some(observation.id.clone()),
            ));
        }
        if !ids.insert(observation.id.clone()) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::DuplicateEvidenceId,
                format!("{path}.id"),
                Some("id"),
                "unique observation ID",
                Some(observation.id.clone()),
            ));
        }
        validate_revision_locator(
            observation.revision_kind,
            &observation.revision,
            &format!("{path}.revision"),
        )?;
        validate_source_path(&observation.path, &format!("{path}.path"))?;
        if observation.license.trim().is_empty() {
            return Err(evidence_error(
                InterfaceProposalErrorReason::EmptyValue,
                format!("{path}.license"),
                Some("license"),
                "known license identifier or UNKNOWN",
                Some("empty".to_owned()),
            ));
        }
        let Some(source_module) = &observation.source_module else {
            return Err(evidence_error(
                InterfaceProposalErrorReason::MissingSourceLocation,
                format!("{path}.source_module"),
                Some("source_module"),
                "canonical source module",
                Some("missing".to_owned()),
            ));
        };
        if !is_canonical_module_name(source_module) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidModuleName,
                format!("{path}.source_module"),
                Some("source_module"),
                "canonical source module",
                Some(source_module.clone()),
            ));
        }
        let declaration_required = matches!(
            observation.usage_kind,
            InterfaceProposalUsageKind::Declaration
                | InterfaceProposalUsageKind::DirectApplication
                | InterfaceProposalUsageKind::Rewrite
                | InterfaceProposalUsageKind::InstanceDependency
                | InterfaceProposalUsageKind::TransitiveDependency
        );
        if declaration_required {
            let Some(source_declaration) = &observation.source_declaration else {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::MissingSourceLocation,
                    format!("{path}.source_declaration"),
                    Some("source_declaration"),
                    "canonical source declaration",
                    Some("missing".to_owned()),
                ));
            };
            if !is_canonical_name(source_declaration) {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidIdentifier,
                    format!("{path}.source_declaration"),
                    Some("source_declaration"),
                    "canonical source declaration",
                    Some(source_declaration.clone()),
                ));
            }
        } else if observation.source_declaration.is_some() {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidUsageKind,
                format!("{path}.source_declaration"),
                Some("source_declaration"),
                "omitted for module_import or module_layout",
                Some("present".to_owned()),
            ));
        }
        if observation.license == "UNKNOWN"
            && !unknown_license_note_is_sufficient(&observation.notes)
        {
            return Err(evidence_error(
                InterfaceProposalErrorReason::LicenseUnknownWithoutNote,
                format!("{path}.license"),
                Some("license"),
                "UNKNOWN with an explicit licensing follow-up note",
                Some(observation.notes.clone()),
            ));
        }
    }
    Ok(ids)
}

fn validate_proof_references(
    references: &[InterfaceProposalProofReference],
) -> InterfaceProposalResult<BTreeSet<String>> {
    let mut ids = BTreeSet::new();
    for (index, reference) in references.iter().enumerate() {
        let path = format!("proof_references[{index}]");
        if !is_stable_identifier(&reference.id) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidIdentifier,
                format!("{path}.id"),
                Some("id"),
                "nonempty stable identifier",
                Some(reference.id.clone()),
            ));
        }
        if !ids.insert(reference.id.clone()) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::DuplicateProofReferenceId,
                format!("{path}.id"),
                Some("id"),
                "unique proof-reference ID",
                Some(reference.id.clone()),
            ));
        }
        validate_revision_locator(
            reference.revision_kind,
            &reference.revision,
            &format!("{path}.revision"),
        )?;
        validate_source_path(&reference.path, &format!("{path}.path"))?;
        if reference.license.trim().is_empty() {
            return Err(evidence_error(
                InterfaceProposalErrorReason::EmptyValue,
                format!("{path}.license"),
                Some("license"),
                "known license identifier or UNKNOWN",
                Some("empty".to_owned()),
            ));
        }
        if let Some(source_module) = &reference.source_module {
            if !is_canonical_module_name(source_module) {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidModuleName,
                    format!("{path}.source_module"),
                    Some("source_module"),
                    "canonical source module",
                    Some(source_module.clone()),
                ));
            }
        }
        if !is_canonical_name(&reference.source_declaration) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidIdentifier,
                format!("{path}.source_declaration"),
                Some("source_declaration"),
                "canonical source declaration",
                Some(reference.source_declaration.clone()),
            ));
        }
        if reference.license == "UNKNOWN" && !unknown_license_note_is_sufficient(&reference.notes) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::LicenseUnknownWithoutNote,
                format!("{path}.license"),
                Some("license"),
                "UNKNOWN with an explicit licensing follow-up note",
                Some(reference.notes.clone()),
            ));
        }
    }
    Ok(ids)
}

fn validate_alternatives(
    proposal: &InterfaceProposal,
    observation_ids: &BTreeSet<String>,
) -> InterfaceProposalResult<()> {
    // V1 has no separate alternative-id field; kind plus candidate is its
    // stable local identity while the evidence IDs remain separate links.
    let mut identities = BTreeSet::new();
    for (index, alternative) in proposal.alternatives.iter().enumerate() {
        let path = format!("alternatives[{index}]");
        let identity = (alternative.kind.as_str(), alternative.candidate.as_str());
        if !identities.insert(identity) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                format!("{path}.candidate"),
                Some("candidate"),
                "unique alternative identity",
                Some(alternative.candidate.clone()),
            ));
        }
        if alternative.candidate.trim().is_empty() {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                format!("{path}.candidate"),
                Some("candidate"),
                "nonempty concrete alternative candidate",
                Some(alternative.candidate.clone()),
            ));
        }
        match alternative.kind {
            InterfaceProposalAlternativeKind::ModuleName
                if !alternative.candidate.starts_with("Mathlib.")
                    || !is_canonical_module_name(&alternative.candidate) =>
            {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                    format!("{path}.candidate"),
                    Some("candidate"),
                    "canonical Mathlib.* module alternative",
                    Some(alternative.candidate.clone()),
                ));
            }
            InterfaceProposalAlternativeKind::DeclarationName
                if !is_canonical_name(&alternative.candidate) =>
            {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                    format!("{path}.candidate"),
                    Some("candidate"),
                    "canonical declaration-name alternative",
                    Some(alternative.candidate.clone()),
                ));
            }
            InterfaceProposalAlternativeKind::Signature if alternative.candidate.contains(":=") => {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                    format!("{path}.candidate"),
                    Some("candidate"),
                    "type-expression alternative without a definition body",
                    Some(alternative.candidate.clone()),
                ));
            }
            _ => {}
        }
        if alternative.rationale.trim().is_empty() || is_placeholder_text(&alternative.rationale) {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                format!("{path}.rationale"),
                Some("rationale"),
                "nonempty specific alternative rationale",
                Some(alternative.rationale.clone()),
            ));
        }
        validate_unique_strings(
            &alternative.evidence_ids,
            &format!("{path}.evidence_ids"),
            InterfaceProposalErrorReason::DuplicateSetMember,
            InterfaceProposalErrorCategory::Evidence,
        )?;
        for (evidence_index, evidence_id) in alternative.evidence_ids.iter().enumerate() {
            if !observation_ids.contains(evidence_id) {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidAlternativeEvidence,
                    format!("{path}.evidence_ids[{evidence_index}]"),
                    Some("evidence_ids"),
                    "ID present in observations",
                    Some(evidence_id.clone()),
                ));
            }
        }
    }
    Ok(())
}

fn validate_declarations(
    proposal: &InterfaceProposal,
    observation_ids: &BTreeSet<String>,
    proof_reference_ids: &BTreeSet<String>,
) -> InterfaceProposalResult<BTreeMap<String, usize>> {
    let complete_surface = matches!(
        proposal.interface_status,
        InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
            | InterfaceProposalStatus::Superseded
    );
    let adopted_surface = matches!(
        proposal.interface_status,
        InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
    );
    let mut declaration_names = BTreeMap::new();

    for (index, declaration) in proposal.declarations.iter().enumerate() {
        let path = format!("declarations[{index}]");
        if !is_unqualified_name(&declaration.name) {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidIdentifier,
                format!("{path}.name"),
                Some("name"),
                "canonical unqualified declaration name",
                Some(declaration.name.clone()),
            ));
        }
        if declaration_names
            .insert(declaration.name.clone(), index)
            .is_some()
        {
            return Err(contract_error(
                InterfaceProposalErrorReason::DuplicateDeclarationName,
                format!("{path}.name"),
                Some("name"),
                "unique declaration name",
                Some(declaration.name.clone()),
            ));
        }
    }

    for (index, declaration) in proposal.declarations.iter().enumerate() {
        let path = format!("declarations[{index}]");
        if complete_surface && declaration.signature.is_none() {
            return Err(lifecycle_error(
                InterfaceProposalErrorReason::StatusSurfaceIncomplete,
                format!("{path}.signature"),
                Some("signature"),
                "exact signature for proposed, adopted, or superseded declaration",
                Some("missing".to_owned()),
            ));
        }
        if let Some(signature) = &declaration.signature {
            validate_signature_text(signature, &format!("{path}.signature"))?;
            if declaration.surface == InterfaceProposalSurface::Public
                && contains_quotient_construction(signature)
            {
                return Err(contract_error(
                    InterfaceProposalErrorReason::ForbiddenQuotientInterface,
                    format!("{path}.signature"),
                    Some("signature"),
                    "setoid-based public interface without quotient construction",
                    Some(signature.clone()),
                ));
            }
        }

        match declaration.kind {
            InterfaceProposalDeclarationKind::Definition => {
                if adopted_surface && declaration.body.is_none() {
                    return Err(lifecycle_error(
                        InterfaceProposalErrorReason::StatusSurfaceIncomplete,
                        format!("{path}.body"),
                        Some("body"),
                        "exact body for adopted or superseded definition",
                        Some("missing".to_owned()),
                    ));
                }
                if let Some(body) = &declaration.body {
                    validate_definition_body(body, &format!("{path}.body"))?;
                    if declaration.surface == InterfaceProposalSurface::Public
                        && contains_quotient_construction(body)
                    {
                        return Err(contract_error(
                            InterfaceProposalErrorReason::ForbiddenQuotientInterface,
                            format!("{path}.body"),
                            Some("body"),
                            "setoid-based public interface without quotient construction",
                            Some(body.clone()),
                        ));
                    }
                }
                if !declaration.family_members.is_empty() {
                    return Err(contract_error(
                        InterfaceProposalErrorReason::InvalidFamily,
                        format!("{path}.family_members"),
                        Some("family_members"),
                        "empty for a definition",
                        Some("present".to_owned()),
                    ));
                }
            }
            InterfaceProposalDeclarationKind::Inductive => {
                if adopted_surface && declaration.family_members.is_empty() {
                    return Err(lifecycle_error(
                        InterfaceProposalErrorReason::IncompleteFamily,
                        format!("{path}.family_members"),
                        Some("family_members"),
                        "complete nonempty ordered inductive family",
                        Some("missing".to_owned()),
                    ));
                }
                if declaration.body.is_some() {
                    return Err(contract_error(
                        InterfaceProposalErrorReason::InvalidDefinitionBody,
                        format!("{path}.body"),
                        Some("body"),
                        "omitted for an inductive declaration",
                        Some("present".to_owned()),
                    ));
                }
                validate_family_members(declaration, &path)?;
            }
            InterfaceProposalDeclarationKind::Theorem => {
                if declaration.body.is_some() {
                    return Err(contract_error(
                        InterfaceProposalErrorReason::InvalidDefinitionBody,
                        format!("{path}.body"),
                        Some("body"),
                        "omitted for a theorem",
                        Some("present".to_owned()),
                    ));
                }
                if !declaration.family_members.is_empty() {
                    return Err(contract_error(
                        InterfaceProposalErrorReason::InvalidFamily,
                        format!("{path}.family_members"),
                        Some("family_members"),
                        "empty for a theorem",
                        Some("present".to_owned()),
                    ));
                }
            }
        }

        validate_unique_strings(
            &declaration.depends_on,
            &format!("{path}.depends_on"),
            InterfaceProposalErrorReason::DuplicateSetMember,
            InterfaceProposalErrorCategory::Graph,
        )?;
        for (dependency_index, dependency) in declaration.depends_on.iter().enumerate() {
            if !declaration_names.contains_key(dependency) {
                return Err(graph_error(
                    InterfaceProposalErrorReason::UnresolvedDependency,
                    format!("{path}.depends_on[{dependency_index}]"),
                    Some("depends_on"),
                    "declaration name in this proposal",
                    Some(dependency.clone()),
                ));
            }
        }

        validate_unique_strings(
            &declaration.evidence_ids,
            &format!("{path}.evidence_ids"),
            InterfaceProposalErrorReason::DuplicateSetMember,
            InterfaceProposalErrorCategory::Evidence,
        )?;
        for (evidence_index, evidence_id) in declaration.evidence_ids.iter().enumerate() {
            if !observation_ids.contains(evidence_id) {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::UnresolvedEvidenceId,
                    format!("{path}.evidence_ids[{evidence_index}]"),
                    Some("evidence_ids"),
                    "ID present in observations",
                    Some(evidence_id.clone()),
                ));
            }
        }
        validate_declaration_evidence(declaration, &path)?;

        validate_unique_strings(
            &declaration.proof_reference_ids,
            &format!("{path}.proof_reference_ids"),
            InterfaceProposalErrorReason::DuplicateSetMember,
            InterfaceProposalErrorCategory::Evidence,
        )?;
        for (reference_index, reference_id) in declaration.proof_reference_ids.iter().enumerate() {
            if !proof_reference_ids.contains(reference_id) {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::UnresolvedProofReferenceId,
                    format!("{path}.proof_reference_ids[{reference_index}]"),
                    Some("proof_reference_ids"),
                    "ID present in proof_references",
                    Some(reference_id.clone()),
                ));
            }
        }
        if declaration.kind != InterfaceProposalDeclarationKind::Theorem
            && (!declaration.proof_reference_ids.is_empty()
                || declaration.proof_reference_exception.is_some())
        {
            return Err(evidence_error(
                InterfaceProposalErrorReason::InvalidProofReferenceException,
                format!("{path}.proof_reference_ids"),
                Some("proof_reference_ids"),
                "proof references only for theorems",
                Some("present on non-theorem".to_owned()),
            ));
        }
        if let Some(exception) = &declaration.proof_reference_exception {
            if declaration.kind != InterfaceProposalDeclarationKind::Theorem
                || !declaration.proof_reference_ids.is_empty()
                || is_placeholder_text(exception)
                || exception.trim().is_empty()
            {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidProofReferenceException,
                    format!("{path}.proof_reference_exception"),
                    Some("proof_reference_exception"),
                    "nonempty explanation used instead of theorem proof references",
                    Some(exception.clone()),
                ));
            }
        }
        if declaration.kind == InterfaceProposalDeclarationKind::Theorem
            && adopted_surface
            && declaration.proof_reference_ids.is_empty()
            && declaration.proof_reference_exception.is_none()
        {
            return Err(evidence_error(
                InterfaceProposalErrorReason::MissingProofReference,
                format!("{path}.proof_reference_ids"),
                Some("proof_reference_ids"),
                "resolvable proof reference or proof_reference_exception",
                Some("missing".to_owned()),
            ));
        }
    }
    Ok(declaration_names)
}

fn validate_signature_text(signature: &str, path: &str) -> InterfaceProposalResult<()> {
    if signature.trim().is_empty() || signature.contains(":=") {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidSignature,
            path,
            Some("signature"),
            "exact NPA type expression without a definition body",
            Some(signature.to_owned()),
        ));
    }
    if is_placeholder_text(signature) {
        return Err(contract_error(
            InterfaceProposalErrorReason::PlaceholderSignature,
            path,
            Some("signature"),
            "complete non-placeholder NPA type expression",
            Some(signature.to_owned()),
        ));
    }
    Ok(())
}

fn validate_definition_body(body: &str, path: &str) -> InterfaceProposalResult<()> {
    if body.trim().is_empty() {
        return Err(contract_error(
            InterfaceProposalErrorReason::InvalidDefinitionBody,
            path,
            Some("body"),
            "nonempty exact NPA definition body",
            Some("empty".to_owned()),
        ));
    }
    if is_placeholder_text(body) {
        return Err(contract_error(
            InterfaceProposalErrorReason::PlaceholderDefinitionBody,
            path,
            Some("body"),
            "complete non-placeholder NPA definition body",
            Some(body.to_owned()),
        ));
    }
    Ok(())
}

fn validate_family_members(
    declaration: &InterfaceProposalDeclaration,
    path: &str,
) -> InterfaceProposalResult<()> {
    validate_unique_strings(
        &declaration.family_members,
        &format!("{path}.family_members"),
        InterfaceProposalErrorReason::DuplicateFamilyMember,
        InterfaceProposalErrorCategory::Contract,
    )?;
    for (index, member) in declaration.family_members.iter().enumerate() {
        if !is_canonical_name(member) {
            return Err(contract_error(
                InterfaceProposalErrorReason::InvalidFamily,
                format!("{path}.family_members[{index}]"),
                Some("family_members"),
                "canonical generated declaration name",
                Some(member.clone()),
            ));
        }
    }
    Ok(())
}

fn validate_declaration_evidence(
    declaration: &InterfaceProposalDeclaration,
    path: &str,
) -> InterfaceProposalResult<()> {
    match declaration.surface {
        InterfaceProposalSurface::Public => {
            if let Some(rationale) = &declaration.support_rationale {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidSupportRationale,
                    format!("{path}.support_rationale"),
                    Some("support_rationale"),
                    "omitted for a public declaration",
                    Some(rationale.clone()),
                ));
            }
            if declaration.evidence_ids.is_empty() {
                let Some(exception) = &declaration.foundation_exception else {
                    return Err(evidence_error(
                        InterfaceProposalErrorReason::MissingPublicEvidence,
                        format!("{path}.evidence_ids"),
                        Some("evidence_ids"),
                        "evidence ID or nonempty foundation_exception",
                        Some("empty".to_owned()),
                    ));
                };
                if exception.trim().is_empty() || is_placeholder_text(exception) {
                    return Err(evidence_error(
                        InterfaceProposalErrorReason::InvalidFoundationException,
                        format!("{path}.foundation_exception"),
                        Some("foundation_exception"),
                        "nonempty specific foundational rationale",
                        Some(exception.clone()),
                    ));
                }
            } else if let Some(exception) = &declaration.foundation_exception {
                if exception.trim().is_empty() || is_placeholder_text(exception) {
                    return Err(evidence_error(
                        InterfaceProposalErrorReason::InvalidFoundationException,
                        format!("{path}.foundation_exception"),
                        Some("foundation_exception"),
                        "nonempty specific foundational rationale",
                        Some(exception.clone()),
                    ));
                }
            }
        }
        InterfaceProposalSurface::Support => {
            if declaration.foundation_exception.is_some() {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::InvalidFoundationException,
                    format!("{path}.foundation_exception"),
                    Some("foundation_exception"),
                    "omitted for a support declaration",
                    Some("present".to_owned()),
                ));
            }
            if declaration.evidence_ids.is_empty() {
                let Some(rationale) = &declaration.support_rationale else {
                    return Err(evidence_error(
                        InterfaceProposalErrorReason::InvalidSupportRationale,
                        format!("{path}.support_rationale"),
                        Some("support_rationale"),
                        "nonempty rationale for unevidenced support",
                        Some("missing".to_owned()),
                    ));
                };
                if rationale.trim().is_empty() || is_placeholder_text(rationale) {
                    return Err(evidence_error(
                        InterfaceProposalErrorReason::InvalidSupportRationale,
                        format!("{path}.support_rationale"),
                        Some("support_rationale"),
                        "nonempty specific rationale for unevidenced support",
                        Some(rationale.clone()),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_dependency_cycles(
    proposal: &InterfaceProposal,
    declaration_names: &BTreeMap<String, usize>,
) -> InterfaceProposalResult<()> {
    let mut states = vec![0_u8; proposal.declarations.len()];
    let mut stack = Vec::new();
    for index in 0..proposal.declarations.len() {
        if states[index] == 0 {
            visit_dependency_node(index, proposal, declaration_names, &mut states, &mut stack)?;
        }
    }
    Ok(())
}

fn visit_dependency_node(
    index: usize,
    proposal: &InterfaceProposal,
    declaration_names: &BTreeMap<String, usize>,
    states: &mut [u8],
    stack: &mut Vec<usize>,
) -> InterfaceProposalResult<()> {
    states[index] = 1;
    stack.push(index);
    for (dependency_index, dependency) in proposal.declarations[index].depends_on.iter().enumerate()
    {
        let dependency_node = declaration_names[dependency];
        match states[dependency_node] {
            0 => {
                visit_dependency_node(dependency_node, proposal, declaration_names, states, stack)?
            }
            1 => {
                let cycle_start = stack
                    .iter()
                    .position(|&node| node == dependency_node)
                    .unwrap_or_default();
                let mut cycle_names = stack[cycle_start..]
                    .iter()
                    .map(|&node| proposal.declarations[node].name.clone())
                    .collect::<Vec<_>>();
                cycle_names.push(proposal.declarations[dependency_node].name.clone());
                return Err(graph_error(
                    InterfaceProposalErrorReason::DependencyCycle,
                    format!("declarations[{index}].depends_on[{dependency_index}]"),
                    Some("depends_on"),
                    "acyclic same-module declaration dependency graph",
                    Some(cycle_names.join(" -> ")),
                ));
            }
            _ => {}
        }
    }
    stack.pop();
    states[index] = 2;
    Ok(())
}

fn validate_support_closure(
    proposal: &InterfaceProposal,
    declaration_names: &BTreeMap<String, usize>,
) -> InterfaceProposalResult<()> {
    let mut reachable = BTreeSet::new();
    let mut pending = Vec::new();
    for declaration in &proposal.declarations {
        if declaration.surface == InterfaceProposalSurface::Public {
            pending.push(declaration.name.clone());
            pending.extend(
                declaration
                    .family_members
                    .iter()
                    .filter(|member| declaration_names.contains_key(*member))
                    .cloned(),
            );
        }
    }
    while let Some(name) = pending.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        let Some(&index) = declaration_names.get(&name) else {
            continue;
        };
        pending.extend(proposal.declarations[index].depends_on.iter().cloned());
        pending.extend(
            proposal.declarations[index]
                .family_members
                .iter()
                .filter(|member| declaration_names.contains_key(*member))
                .cloned(),
        );
    }
    for (index, declaration) in proposal.declarations.iter().enumerate() {
        if declaration.surface == InterfaceProposalSurface::Support
            && declaration.evidence_ids.is_empty()
            && !reachable.contains(&declaration.name)
        {
            return Err(graph_error(
                InterfaceProposalErrorReason::SupportNotReachable,
                format!("declarations[{index}].name"),
                Some("surface"),
                "support declaration reachable from public dependency or family closure",
                Some(declaration.name.clone()),
            ));
        }
    }
    Ok(())
}

fn validate_adoption_licenses(
    proposal: &InterfaceProposal,
    observation_ids: &BTreeSet<String>,
    proof_reference_ids: &BTreeSet<String>,
) -> InterfaceProposalResult<()> {
    if !matches!(
        proposal.interface_status,
        InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
    ) {
        return Ok(());
    }
    let mut observations = BTreeMap::new();
    for observation in &proposal.observations {
        observations.insert(observation.id.as_str(), observation);
    }
    let mut proof_references = BTreeMap::new();
    for reference in &proposal.proof_references {
        proof_references.insert(reference.id.as_str(), reference);
    }
    for (index, declaration) in proposal.declarations.iter().enumerate() {
        for evidence_id in &declaration.evidence_ids {
            let Some(observation) = observations.get(evidence_id.as_str()) else {
                debug_assert!(!observation_ids.contains(evidence_id));
                return Err(evidence_error(
                    InterfaceProposalErrorReason::UnresolvedEvidenceId,
                    format!("declarations[{index}].evidence_ids"),
                    Some("evidence_ids"),
                    "ID present in observations",
                    Some(evidence_id.clone()),
                ));
            };
            if observation.license == "UNKNOWN" {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::LicenseUnknownBlocksAdoption,
                    format!("declarations[{index}].evidence_ids"),
                    Some("evidence_ids"),
                    "known license for evidence required by adoption",
                    Some(evidence_id.clone()),
                ));
            }
        }
        for reference_id in &declaration.proof_reference_ids {
            let Some(reference) = proof_references.get(reference_id.as_str()) else {
                debug_assert!(!proof_reference_ids.contains(reference_id));
                return Err(evidence_error(
                    InterfaceProposalErrorReason::UnresolvedProofReferenceId,
                    format!("declarations[{index}].proof_reference_ids"),
                    Some("proof_reference_ids"),
                    "ID present in proof_references",
                    Some(reference_id.clone()),
                ));
            };
            if reference.license == "UNKNOWN" {
                return Err(evidence_error(
                    InterfaceProposalErrorReason::LicenseUnknownBlocksAdoption,
                    format!("declarations[{index}].proof_reference_ids"),
                    Some("proof_reference_ids"),
                    "known license for proof reference required by adoption",
                    Some(reference_id.clone()),
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    fn root_source() -> String {
        format!(
            r#"schema = "{INTERFACE_PROPOSAL_SCHEMA}"
proposal_id = "Mathlib.Test.Basic"
proposal_revision = 1
previous_proposal_hash = "{HASH}"
module = "Mathlib.Test.Basic"
change_kind = "add"
source_modules = []
change_group = "test-group"
interface_status = "adopted"
proof_evidence = false
summary = "A compact test surface."
scope = "Only the compact test surface."
imports = ["Mathlib.Logic.Eq"]
adoption_date = "2026-08-02"
adoption_rationale = "The selected surface is bounded."
re_adoption_rationale = "The selected surface was re-reviewed."
withdrawal_rationale = "This is fixture metadata."
alternatives_review = "No material alternative was selected."
supersedes = []
superseded_by = ["Mathlib.Test.Next"]
"#
        )
    }

    fn valid_source() -> String {
        format!(
            r#"{}
[[declarations]]
name = "comp"
kind = "definition"
surface = "support"
signature = "forall (x : Nat), Nat"
body = "fun x => x"
family_members = ["comp"]
semantic_role = "support closure"
depends_on = []
evidence_ids = ["obs-decl"]
foundation_exception = "foundation support"
support_rationale = "Required by the public closure."
proof_reference_ids = []
proof_reference_exception = "Immediately constructible."

[[observations]]
id = "obs-decl"
repository = "https://example.invalid/mathlib4"
revision_kind = "git_commit"
revision = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
license = "Apache-2.0"
path = "Mathlib/Test/Basic.lean"
source_module = "Mathlib.Test.Basic"
source_declaration = "Function.comp"
usage_kind = "declaration"
notes = "Pinned declaration observation."

[[proof_references]]
id = "proof-structure"
repository = "https://example.invalid/mathlib4"
revision_kind = "release_digest"
revision = "{HASH}"
license = "Apache-2.0"
path = "Mathlib/Test/Basic.lean"
source_module = "Mathlib.Test.Basic"
source_declaration = "Function.comp_assoc"
reference_role = "proof_structure"
notes = "Pinned proof-design reference only."

[[alternatives]]
kind = "module_name"
candidate = "Mathlib.Test.Defs"
disposition = "rejected"
rationale = "The chosen boundary is clearer."
evidence_ids = ["obs-decl"]
"#,
            root_source()
        )
    }

    fn validation_observation() -> InterfaceProposalObservation {
        InterfaceProposalObservation {
            id: "obs".to_owned(),
            repository: "https://example.invalid/mathlib4".to_owned(),
            revision_kind: InterfaceProposalRevisionKind::GitCommit,
            revision: "c5ea00351c28e24afc9f0f84379aa41082b1188f".to_owned(),
            license: "Apache-2.0".to_owned(),
            path: "Mathlib/Test/Basic.lean".to_owned(),
            source_module: Some("Mathlib.Test.Source".to_owned()),
            source_declaration: Some("Function.comp".to_owned()),
            usage_kind: InterfaceProposalUsageKind::Declaration,
            notes: "Pinned declaration observation.".to_owned(),
        }
    }

    fn validation_declaration(
        kind: InterfaceProposalDeclarationKind,
        surface: InterfaceProposalSurface,
    ) -> InterfaceProposalDeclaration {
        InterfaceProposalDeclaration {
            name: "target".to_owned(),
            kind,
            surface,
            signature: Some("forall (x : Nat), Nat".to_owned()),
            body: (kind == InterfaceProposalDeclarationKind::Definition)
                .then(|| "fun x => x".to_owned()),
            family_members: Vec::new(),
            semantic_role: "The selected declaration has a bounded role.".to_owned(),
            depends_on: Vec::new(),
            evidence_ids: vec!["obs".to_owned()],
            foundation_exception: None,
            support_rationale: (surface == InterfaceProposalSurface::Support)
                .then(|| "The support declaration closes a public dependency.".to_owned()),
            proof_reference_ids: Vec::new(),
            proof_reference_exception: None,
        }
    }

    fn validation_fixture(
        status: InterfaceProposalStatus,
        change_kind: InterfaceProposalChangeKind,
    ) -> InterfaceProposal {
        let module = "Mathlib.Test.Basic".to_owned();
        let source_modules = match change_kind {
            InterfaceProposalChangeKind::Add => Vec::new(),
            InterfaceProposalChangeKind::Revise => vec![module.clone()],
            InterfaceProposalChangeKind::Rename | InterfaceProposalChangeKind::Replace => {
                vec!["Mathlib.Test.Old".to_owned()]
            }
            InterfaceProposalChangeKind::Split => vec!["Mathlib.Test.Old".to_owned()],
            InterfaceProposalChangeKind::Merge => vec![
                "Mathlib.Test.Left".to_owned(),
                "Mathlib.Test.Right".to_owned(),
            ],
        };
        let declarations = match status {
            InterfaceProposalStatus::Observed | InterfaceProposalStatus::Withdrawn => Vec::new(),
            InterfaceProposalStatus::Proposed
            | InterfaceProposalStatus::Adopted
            | InterfaceProposalStatus::Superseded => {
                vec![validation_declaration(
                    InterfaceProposalDeclarationKind::Definition,
                    InterfaceProposalSurface::Public,
                )]
            }
        };
        InterfaceProposal {
            schema: INTERFACE_PROPOSAL_SCHEMA.to_owned(),
            proposal_id: module.clone(),
            proposal_revision: 1,
            previous_proposal_hash: None,
            module,
            change_kind,
            source_modules,
            change_group: (change_kind == InterfaceProposalChangeKind::Split)
                .then(|| "test-split".to_owned()),
            interface_status: status,
            proof_evidence: false,
            summary: "A compact test surface.".to_owned(),
            scope: "Only the compact test surface.".to_owned(),
            imports: vec!["Mathlib.Logic.Eq".to_owned()],
            adoption_date: matches!(
                status,
                InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
            )
            .then(|| "2026-08-02".to_owned()),
            adoption_rationale: matches!(
                status,
                InterfaceProposalStatus::Adopted | InterfaceProposalStatus::Superseded
            )
            .then(|| "The selected surface is bounded.".to_owned()),
            re_adoption_rationale: None,
            withdrawal_rationale: (status == InterfaceProposalStatus::Withdrawn)
                .then(|| "The incomplete record is not pursued.".to_owned()),
            alternatives_review: matches!(
                status,
                InterfaceProposalStatus::Proposed
                    | InterfaceProposalStatus::Adopted
                    | InterfaceProposalStatus::Superseded
            )
            .then(|| "No material alternative was selected.".to_owned()),
            supersedes: Vec::new(),
            superseded_by: (status == InterfaceProposalStatus::Superseded)
                .then(|| vec!["Mathlib.Test.Next".to_owned()]),
            declarations,
            observations: vec![validation_observation()],
            proof_references: Vec::new(),
            alternatives: Vec::new(),
        }
    }

    #[test]
    fn parses_all_table_kinds_and_optional_fields() {
        let proposal = parse_interface_proposal(valid_source().as_bytes()).unwrap();
        assert_eq!(proposal.schema, INTERFACE_PROPOSAL_SCHEMA);
        assert_eq!(
            proposal.previous_proposal_hash,
            Some(parse_package_hash(HASH, "hash").unwrap())
        );
        assert_eq!(proposal.declarations.len(), 1);
        assert_eq!(proposal.observations.len(), 1);
        assert_eq!(proposal.proof_references.len(), 1);
        assert_eq!(proposal.alternatives.len(), 1);
        assert_eq!(proposal.declarations[0].family_members, vec!["comp"]);
    }

    #[test]
    fn parses_every_status_and_change_kind() {
        for status in ["observed", "proposed", "adopted", "withdrawn", "superseded"] {
            for change_kind in ["add", "revise", "rename", "split", "merge", "replace"] {
                let source = valid_source()
                    .replace(
                        "interface_status = \"adopted\"",
                        &format!("interface_status = \"{status}\""),
                    )
                    .replace(
                        "change_kind = \"add\"",
                        &format!("change_kind = \"{change_kind}\""),
                    );
                let proposal = parse_interface_proposal(source.as_bytes()).unwrap();
                assert_eq!(proposal.interface_status.as_str(), status);
                assert_eq!(proposal.change_kind.as_str(), change_kind);
            }
        }
    }

    #[test]
    fn rejects_unknown_schema_and_unknown_fields_at_every_table_depth() {
        let root = valid_source().replace(
            &format!("schema = \"{INTERFACE_PROPOSAL_SCHEMA}\""),
            "schema = \"npa.mathlib.interface_proposal.v999\"",
        );
        assert_eq!(
            parse_interface_proposal(root.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::UnknownSchema
        );

        for marker in [
            "unknown_root = true\n",
            "unknown_declaration = true\n",
            "unknown_observation = true\n",
            "unknown_proof = true\n",
            "unknown_alternative = true\n",
        ] {
            let source = match marker {
                "unknown_root = true\n" => format!("{}{}", marker, valid_source()),
                "unknown_declaration = true\n" => valid_source().replace(
                    "name = \"comp\"\n",
                    "name = \"comp\"\nunknown_declaration = true\n",
                ),
                "unknown_observation = true\n" => valid_source().replace(
                    "id = \"obs-decl\"\n",
                    "id = \"obs-decl\"\nunknown_observation = true\n",
                ),
                "unknown_proof = true\n" => valid_source().replace(
                    "id = \"proof-structure\"\n",
                    "id = \"proof-structure\"\nunknown_proof = true\n",
                ),
                _ => valid_source().replace(
                    "kind = \"module_name\"\n",
                    "kind = \"module_name\"\nunknown_alternative = true\n",
                ),
            };
            let error = parse_interface_proposal(source.as_bytes()).unwrap_err();
            assert_eq!(
                error.reason_code,
                InterfaceProposalErrorReason::UnknownField
            );
        }
    }

    #[test]
    fn rejects_duplicate_keys_and_wrong_types() {
        assert_eq!(
            parse_interface_proposal(&[0xff, 0xfe])
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::InvalidUtf8
        );

        let missing = valid_source().replace("scope = \"Only the compact test surface.\"\n", "");
        assert_eq!(
            parse_interface_proposal(missing.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::MissingField
        );

        let duplicate = format!("proposal_id = \"first\"\n{}", valid_source());
        assert_eq!(
            parse_interface_proposal(duplicate.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::DuplicateKey
        );

        let wrong_type =
            valid_source().replace("proposal_revision = 1", "proposal_revision = \"one\"");
        let error = parse_interface_proposal(wrong_type.as_bytes()).unwrap_err();
        assert_eq!(error.reason_code, InterfaceProposalErrorReason::WrongType);

        let invalid_enum = valid_source().replace(
            "reference_role = \"proof_structure\"",
            "reference_role = \"unknown_role\"",
        );
        assert_eq!(
            parse_interface_proposal(invalid_enum.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::InvalidEnum
        );
    }

    #[test]
    fn enforces_file_string_and_path_limits_before_typed_clones() {
        let oversized_file = vec![b'#'; MAX_PROPOSAL_FILE_BYTES + 1];
        assert_eq!(
            parse_interface_proposal(&oversized_file)
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::ProposalFileBytesExceeded
        );

        let oversized_string = format!(
            "{}\nsummary = \"{}\"\n",
            root_source().replace("summary = \"A compact test surface.\"\n", ""),
            "s".repeat(MAX_STRING_BYTES + 1)
        );
        assert_eq!(
            parse_interface_proposal(oversized_string.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::StringBytesExceeded
        );

        let oversized_path = valid_source().replace(
            "path = \"Mathlib/Test/Basic.lean\"",
            &format!("path = \"{}\"", "p".repeat(MAX_PATH_BYTES + 1)),
        );
        assert_eq!(
            parse_interface_proposal(oversized_path.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::PathBytesExceeded
        );
    }

    #[test]
    fn enforces_nested_collection_limits_before_collecting_rows() {
        let imports = (0..=MAX_IMPORTS)
            .map(|index| format!("\"Mathlib.Import{index}\""))
            .collect::<Vec<_>>()
            .join(", ");
        let source = valid_source().replace(
            "imports = [\"Mathlib.Logic.Eq\"]",
            &format!("imports = [{imports}]"),
        );
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::ImportCountExceeded
        );

        let declarations = (0..=MAX_DECLARATIONS)
            .map(|index| format!("\n[[declarations]]\nname = \"d{index}\"\nkind = \"theorem\"\nsurface = \"public\"\nsemantic_role = \"role\"\ndepends_on = []\nevidence_ids = []\nproof_reference_ids = []\n"))
            .collect::<String>();
        let source = format!("{}{}", root_source(), declarations);
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::DeclarationCountExceeded
        );

        let links = (0..=MAX_LINKS_PER_ARRAY)
            .map(|index| format!("\"e{index}\""))
            .collect::<Vec<_>>()
            .join(", ");
        let source = valid_source().replace(
            "evidence_ids = [\"obs-decl\"]",
            &format!("evidence_ids = [{links}]"),
        );
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::LinkCountExceeded
        );

        let observations = (0..=MAX_OBSERVATIONS)
            .map(|index| {
                format!(
                    "\n[[observations]]\nid = \"obs-{index}\"\nrepository = \"fixture\"\nrevision_kind = \"git_commit\"\nrevision = \"c5ea00351c28e24afc9f0f84379aa41082b1188f\"\nlicense = \"Apache-2.0\"\npath = \"Fixture/{index}.lean\"\nusage_kind = \"module_layout\"\nnotes = \"layout\"\n"
                )
            })
            .collect::<String>();
        let source = format!("{}{}", root_source(), observations);
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::ObservationCountExceeded
        );

        let proof_references = (0..=MAX_PROOF_REFERENCES)
            .map(|index| {
                format!(
                    "\n[[proof_references]]\nid = \"proof-{index}\"\nrepository = \"fixture\"\nrevision_kind = \"git_commit\"\nrevision = \"c5ea00351c28e24afc9f0f84379aa41082b1188f\"\nlicense = \"Apache-2.0\"\npath = \"Fixture/{index}.lean\"\nsource_declaration = \"proof\"\nreference_role = \"proof_structure\"\nnotes = \"proof\"\n"
                )
            })
            .collect::<String>();
        let source = format!("{}{}", root_source(), proof_references);
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::ProofReferenceCountExceeded
        );

        let alternatives = (0..=MAX_ALTERNATIVES)
            .map(|index| {
                format!(
                    "\n[[alternatives]]\nkind = \"module_name\"\ncandidate = \"Mathlib.Test.{index}\"\ndisposition = \"deferred\"\nrationale = \"later\"\nevidence_ids = []\n"
                )
            })
            .collect::<String>();
        let source = format!("{}{}", root_source(), alternatives);
        assert_eq!(
            parse_interface_proposal(source.as_bytes())
                .unwrap_err()
                .reason_code,
            InterfaceProposalErrorReason::AlternativeCountExceeded
        );
    }

    #[test]
    fn validates_every_status_and_change_kind_fixture() {
        let statuses = [
            InterfaceProposalStatus::Observed,
            InterfaceProposalStatus::Proposed,
            InterfaceProposalStatus::Adopted,
            InterfaceProposalStatus::Withdrawn,
            InterfaceProposalStatus::Superseded,
        ];
        let change_kinds = [
            InterfaceProposalChangeKind::Add,
            InterfaceProposalChangeKind::Revise,
            InterfaceProposalChangeKind::Rename,
            InterfaceProposalChangeKind::Split,
            InterfaceProposalChangeKind::Merge,
            InterfaceProposalChangeKind::Replace,
        ];
        for status in statuses {
            for change_kind in change_kinds {
                let proposal = validation_fixture(status, change_kind);
                validate_interface_proposal(&proposal)
                    .unwrap_or_else(|error| panic!("{status:?}/{change_kind:?}: {error:?}"));
            }
        }
    }

    #[test]
    fn permits_unresolved_surfaces_only_for_observed_and_early_withdrawn() {
        for status in [
            InterfaceProposalStatus::Observed,
            InterfaceProposalStatus::Withdrawn,
        ] {
            let mut proposal = validation_fixture(status, InterfaceProposalChangeKind::Add);
            let mut declaration = validation_declaration(
                InterfaceProposalDeclarationKind::Definition,
                InterfaceProposalSurface::Public,
            );
            declaration.signature = None;
            declaration.body = None;
            declaration.evidence_ids.clear();
            declaration.foundation_exception = Some(
                "This early record reserves a foundational name before downstream use is known."
                    .to_owned(),
            );
            proposal.declarations = vec![declaration];
            validate_interface_proposal(&proposal).unwrap();
        }

        for status in [
            InterfaceProposalStatus::Proposed,
            InterfaceProposalStatus::Adopted,
        ] {
            let mut proposal = validation_fixture(status, InterfaceProposalChangeKind::Add);
            proposal.declarations[0].signature = None;
            let error = validate_interface_proposal(&proposal).unwrap_err();
            assert_eq!(
                error.reason_code,
                InterfaceProposalErrorReason::StatusSurfaceIncomplete
            );
        }
    }

    #[test]
    fn enforces_evidence_foundation_and_support_reachability() {
        let mut missing_evidence = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        missing_evidence.declarations[0].evidence_ids.clear();
        let error = validate_interface_proposal(&missing_evidence).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::MissingPublicEvidence
        );

        missing_evidence.declarations[0].foundation_exception = Some(
            "This public primitive is foundational and has no expected direct downstream use."
                .to_owned(),
        );
        validate_interface_proposal(&missing_evidence).unwrap();

        let mut unreachable_support = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        let mut support = validation_declaration(
            InterfaceProposalDeclarationKind::Definition,
            InterfaceProposalSurface::Support,
        );
        support.name = "unreachable".to_owned();
        support.evidence_ids.clear();
        unreachable_support.declarations.push(support);
        let error = validate_interface_proposal(&unreachable_support).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::SupportNotReachable
        );

        let mut missing_support_rationale = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        let mut support = validation_declaration(
            InterfaceProposalDeclarationKind::Definition,
            InterfaceProposalSurface::Support,
        );
        support.name = "unexplained".to_owned();
        support.evidence_ids.clear();
        support.support_rationale = None;
        missing_support_rationale.declarations.push(support);
        let error = validate_interface_proposal(&missing_support_rationale).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidSupportRationale
        );
    }

    #[test]
    fn validates_revision_locators_licenses_cycles_and_proof_references() {
        let mut unknown_during_observation = validation_fixture(
            InterfaceProposalStatus::Observed,
            InterfaceProposalChangeKind::Add,
        );
        unknown_during_observation.observations[0].license = "UNKNOWN".to_owned();
        unknown_during_observation.observations[0].notes =
            "License follow-up is pending before adoption.".to_owned();
        validate_interface_proposal(&unknown_during_observation).unwrap();

        let mut unknown_at_adoption = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        unknown_at_adoption.observations[0].license = "UNKNOWN".to_owned();
        unknown_at_adoption.observations[0].notes =
            "License follow-up is pending before adoption.".to_owned();
        let error = validate_interface_proposal(&unknown_at_adoption).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::LicenseUnknownBlocksAdoption
        );

        let mut cycle = validation_fixture(
            InterfaceProposalStatus::Proposed,
            InterfaceProposalChangeKind::Add,
        );
        let mut first = validation_declaration(
            InterfaceProposalDeclarationKind::Definition,
            InterfaceProposalSurface::Public,
        );
        first.name = "first".to_owned();
        first.depends_on = vec!["second".to_owned()];
        let mut second = validation_declaration(
            InterfaceProposalDeclarationKind::Definition,
            InterfaceProposalSurface::Public,
        );
        second.name = "second".to_owned();
        second.depends_on = vec!["first".to_owned()];
        cycle.declarations = vec![first, second];
        let error = validate_interface_proposal(&cycle).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::DependencyCycle
        );

        let mut theorem = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        theorem.declarations = vec![validation_declaration(
            InterfaceProposalDeclarationKind::Theorem,
            InterfaceProposalSurface::Public,
        )];
        let error = validate_interface_proposal(&theorem).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::MissingProofReference
        );

        theorem.declarations[0].proof_reference_ids = vec!["proof".to_owned()];
        theorem.proof_references = vec![InterfaceProposalProofReference {
            id: "proof".to_owned(),
            repository: "https://example.invalid/mathlib4".to_owned(),
            revision_kind: InterfaceProposalRevisionKind::ReleaseDigest,
            revision: HASH.to_owned(),
            license: "Apache-2.0".to_owned(),
            path: "Mathlib/Test/Basic.lean".to_owned(),
            source_module: Some("Mathlib.Test.Source".to_owned()),
            source_declaration: "Function.comp_assoc".to_owned(),
            reference_role: InterfaceProposalReferenceRole::ProofStructure,
            notes: "Pinned proof-design reference only.".to_owned(),
        }];
        validate_interface_proposal(&theorem).unwrap();
    }

    #[test]
    fn validates_revision_chain_presence_and_proof_boundary() {
        let mut proposal = validation_fixture(
            InterfaceProposalStatus::Observed,
            InterfaceProposalChangeKind::Add,
        );
        proposal.proof_evidence = true;
        let error = validate_interface_proposal(&proposal).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::ProofEvidenceNotFalse
        );

        proposal.proof_evidence = false;
        proposal.proposal_revision = 0;
        let error = validate_interface_proposal(&proposal).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidRevision
        );

        proposal.proposal_revision = 2;
        let error = validate_interface_proposal(&proposal).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidRevision
        );

        proposal.previous_proposal_hash = Some(parse_package_hash(HASH, "previous").unwrap());
        validate_interface_proposal(&proposal).unwrap();
    }

    #[test]
    fn rejects_duplicate_families_alternative_identities_and_unsorted_sets() {
        let mut descriptive_alternative = validation_fixture(
            InterfaceProposalStatus::Proposed,
            InterfaceProposalChangeKind::Add,
        );
        descriptive_alternative.alternatives = vec![InterfaceProposalAlternative {
            kind: InterfaceProposalAlternativeKind::Signature,
            candidate: "forall (x : alpha), ...".to_owned(),
            disposition: InterfaceProposalAlternativeDisposition::Rejected,
            rationale: "The pointwise form would weaken the selected rewrite surface.".to_owned(),
            evidence_ids: vec!["obs".to_owned()],
        }];
        validate_interface_proposal(&descriptive_alternative).unwrap();

        let mut family = validation_fixture(
            InterfaceProposalStatus::Adopted,
            InterfaceProposalChangeKind::Add,
        );
        let mut inductive = validation_declaration(
            InterfaceProposalDeclarationKind::Inductive,
            InterfaceProposalSurface::Public,
        );
        inductive.family_members = vec!["target.mk".to_owned(), "target.mk".to_owned()];
        family.declarations = vec![inductive];
        let error = validate_interface_proposal(&family).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::DuplicateFamilyMember
        );

        let mut alternatives = validation_fixture(
            InterfaceProposalStatus::Proposed,
            InterfaceProposalChangeKind::Add,
        );
        alternatives.alternatives = vec![
            InterfaceProposalAlternative {
                kind: InterfaceProposalAlternativeKind::ModuleName,
                candidate: "Mathlib.Test.Other".to_owned(),
                disposition: InterfaceProposalAlternativeDisposition::Rejected,
                rationale: "The selected boundary is narrower.".to_owned(),
                evidence_ids: vec!["obs".to_owned()],
            },
            InterfaceProposalAlternative {
                kind: InterfaceProposalAlternativeKind::ModuleName,
                candidate: "Mathlib.Test.Other".to_owned(),
                disposition: InterfaceProposalAlternativeDisposition::Deferred,
                rationale: "The broader boundary can be revisited later.".to_owned(),
                evidence_ids: vec!["obs".to_owned()],
            },
        ];
        let error = validate_interface_proposal(&alternatives).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidAlternativeEvidence
        );

        let mut unsorted = validation_fixture(
            InterfaceProposalStatus::Superseded,
            InterfaceProposalChangeKind::Merge,
        );
        unsorted.source_modules.reverse();
        let error = validate_interface_proposal(&unsorted).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidSourceModules
        );
        let mut unsorted_successors = validation_fixture(
            InterfaceProposalStatus::Superseded,
            InterfaceProposalChangeKind::Add,
        );
        unsorted_successors.superseded_by = Some(vec![
            "Mathlib.Test.Z".to_owned(),
            "Mathlib.Test.A".to_owned(),
        ]);
        let error = validate_interface_proposal(&unsorted_successors).unwrap_err();
        assert_eq!(
            error.reason_code,
            InterfaceProposalErrorReason::InvalidSupersededByOrder
        );
    }

    #[test]
    fn interface_proposal_hashes_exact_bytes_and_bounds_diagnostic_values() {
        assert_eq!(
            interface_proposal_file_hash(b"abc"),
            package_file_hash(b"abc")
        );
        let value = "x".repeat(MAX_DIAGNOSTIC_VALUE_BYTES + 10);
        let error = InterfaceProposalError::new(
            InterfaceProposalErrorCategory::Syntax,
            InterfaceProposalErrorReason::InvalidToml,
            "$",
            Some(value.clone()),
            Some(value.clone()),
            Some(value),
        );
        assert_eq!(
            error.field.as_ref().unwrap().len(),
            MAX_DIAGNOSTIC_VALUE_BYTES
        );
        assert_eq!(
            error.expected.as_ref().unwrap().len(),
            MAX_DIAGNOSTIC_VALUE_BYTES
        );
        assert_eq!(
            error.actual.as_ref().unwrap().len(),
            MAX_DIAGNOSTIC_VALUE_BYTES
        );
    }
}
