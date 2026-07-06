use std::collections::{BTreeMap, BTreeSet, VecDeque};

use npa_cert::{
    decode_module_cert, term_hash, AxiomRef, CertReducibility, DeclCert, DeclPayload, ExportEntry,
    ExportKind, GlobalRef, Hash, ModuleCert, Name, NameId, TermId, TermNode, VerifiedModule,
};
use sha2::{Digest, Sha256};

const CERTIFICATE_THEOREM_GRAPH_HASH_TAG: &[u8] = b"npa.certificate-theorem-graph.v1";
const CERTIFICATE_THEOREM_GRAPH_QUERY_FEATURES_HASH_TAG: &[u8] =
    b"npa.certificate-theorem-graph.query-features.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphOptions {
    pub require_import_certificate_hashes: bool,
}

impl CertificateTheoremGraphOptions {
    pub fn export_hash_bound() -> Self {
        Self {
            require_import_certificate_hashes: false,
        }
    }

    pub fn high_trust_certificate_hash_bound() -> Self {
        Self {
            require_import_certificate_hashes: true,
        }
    }
}

impl Default for CertificateTheoremGraphOptions {
    fn default() -> Self {
        Self::export_hash_bound()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertificateTheoremGraphError {
    DecodeCertificate,
    MissingImportBinding {
        module: Name,
    },
    DuplicateImportBinding {
        module: Name,
    },
    ImportExportHashMismatch {
        module: Name,
    },
    ImportCertificateHashMissing {
        module: Name,
    },
    ImportCertificateHashMismatch {
        module: Name,
    },
    MissingName {
        name_id: NameId,
    },
    MissingTerm {
        term_id: TermId,
    },
    MissingDeclaration {
        decl_index: usize,
    },
    MissingExport {
        name: Name,
    },
    MissingImportedExport {
        module: Name,
        name: Name,
    },
    MissingGraphNode {
        name: Name,
    },
    DeclInterfaceHashMismatch {
        name: Name,
    },
    TermHash {
        term_id: TermId,
    },
    GraphSnapshotHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    GraphSnapshotBytesMismatch,
    QueryFeaturesHashMismatch {
        expected: Hash,
        actual: Hash,
    },
    QueryFeaturesBytesMismatch,
    DuplicateGraphNode {
        node: Box<CertificateTheoremGraphNodeId>,
    },
    DuplicateGraphEdge {
        edge: Box<CertificateTheoremGraphEdge>,
    },
    MalformedEdgeReference {
        from: Box<CertificateTheoremGraphNodeId>,
        to: Box<CertificateTheoremGraphNodeId>,
    },
    MissingVerifiedIdentity {
        node: Box<CertificateTheoremGraphNodeId>,
    },
    VerifiedIdentityMismatch {
        node: Box<CertificateTheoremGraphNodeId>,
    },
    UnverifiedCandidateNode {
        node: Box<CertificateTheoremGraphNodeId>,
    },
    MalformedNodeMetadata {
        node: Box<CertificateTheoremGraphNodeId>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphSnapshot {
    pub source_module: Name,
    pub source_export_hash: Hash,
    pub source_certificate_hash: Hash,
    pub extractor_version: CertificateTheoremGraphExtractorVersion,
    pub imports: Vec<CertificateTheoremGraphImportBinding>,
    pub nodes: Vec<CertificateTheoremGraphNode>,
    pub edges: Vec<CertificateTheoremGraphEdge>,
    pub graph_hash: Hash,
}

impl CertificateTheoremGraphSnapshot {
    pub fn node(&self, id: &CertificateTheoremGraphNodeId) -> Option<&CertificateTheoremGraphNode> {
        self.nodes.iter().find(|node| &node.id == id)
    }

    pub fn outgoing_edges(
        &self,
        id: &CertificateTheoremGraphNodeId,
    ) -> Vec<CertificateTheoremGraphEdge> {
        self.edges
            .iter()
            .filter(|edge| &edge.from == id)
            .cloned()
            .collect()
    }

    pub fn direct_axiom_dependencies(
        &self,
        id: &CertificateTheoremGraphNodeId,
    ) -> Vec<CertificateTheoremGraphNodeId> {
        self.edge_targets(id, CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom)
    }

    pub fn transitive_axiom_dependencies(
        &self,
        id: &CertificateTheoremGraphNodeId,
    ) -> Vec<CertificateTheoremGraphNodeId> {
        self.edge_targets(
            id,
            CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom,
        )
    }

    pub fn direct_dependency_targets(
        &self,
        id: &CertificateTheoremGraphNodeId,
    ) -> Vec<CertificateTheoremGraphNodeId> {
        self.edge_targets(id, CertificateTheoremGraphEdgeKind::ImportsDeclaration)
    }

    fn edge_targets(
        &self,
        id: &CertificateTheoremGraphNodeId,
        kind: CertificateTheoremGraphEdgeKind,
    ) -> Vec<CertificateTheoremGraphNodeId> {
        self.edges
            .iter()
            .filter(|edge| &edge.from == id && edge.kind == kind)
            .map(|edge| edge.to.clone())
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphImportBinding {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CertificateTheoremGraphExtractorVersion {
    CertificateGraphV1,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CertificateTheoremGraphNodeId {
    pub scope: CertificateTheoremGraphNodeScope,
    pub module: Name,
    pub name: Name,
    pub decl_interface_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CertificateTheoremGraphNodeScope {
    Builtin,
    Imported {
        import_export_hash: Hash,
        import_certificate_hash: Option<Hash>,
    },
    Local,
    LocalGenerated {
        source_decl_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphNode {
    pub id: CertificateTheoremGraphNodeId,
    pub kind: CertificateTheoremGraphNodeKind,
    pub type_hash: Option<Hash>,
    pub proof_hash: Option<Hash>,
    pub body_hash: Option<Hash>,
    pub metadata: CertificateTheoremGraphNodeMetadata,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CertificateTheoremGraphNodeMetadata {
    pub usage_count: Option<u64>,
    pub domain_tags: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CertificateTheoremGraphNodeKind {
    Axiom,
    Definition,
    Theorem,
    Inductive,
    Constructor,
    Recursor,
    Builtin,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CertificateTheoremGraphEdge {
    pub from: CertificateTheoremGraphNodeId,
    pub to: CertificateTheoremGraphNodeId,
    pub kind: CertificateTheoremGraphEdgeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CertificateTheoremGraphEdgeKind {
    ImportsDeclaration,
    MentionsType,
    UsesConstant,
    GeneratedDeclaration,
    DependsOnDirectAxiom,
    DependsOnTransitiveAxiom,
    UsedBy,
    SimilarStatement,
    AxiomPath,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CertificateTheoremGraphVerifiedIdentity {
    pub module: Name,
    pub name: Name,
    pub export_hash: Hash,
    pub certificate_hash: Option<Hash>,
    pub decl_interface_hash: Hash,
    pub statement_or_type_hash: Hash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphValidatedSnapshot {
    pub graph_snapshot_hash: Hash,
    pub verified_identities: Vec<CertificateTheoremGraphVerifiedIdentity>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CertificateTheoremGraphSnapshotValidationOptions<'a> {
    pub verified_identities: &'a [CertificateTheoremGraphVerifiedIdentity],
    pub require_verified_identities: bool,
}

#[derive(Clone, Copy, Debug)]
pub enum CertificateTheoremGraphSnapshotSidecar<'a> {
    Absent,
    Inline {
        snapshot: &'a CertificateTheoremGraphSnapshot,
        graph_snapshot_hash: Hash,
    },
    Artifact {
        snapshot: &'a CertificateTheoremGraphSnapshot,
        canonical_bytes: &'a [u8],
        graph_snapshot_hash: Hash,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphQueryFeatures {
    pub environment_hash: Hash,
    pub goal_fingerprint: Hash,
    pub local_context_hash: Hash,
    pub query_profile_hash: Hash,
    pub theorem_index_fingerprint: Hash,
    pub graph_snapshot_hash: Option<Hash>,
}

#[derive(Clone, Copy, Debug)]
pub enum CertificateTheoremGraphQueryFeaturesSidecar<'a> {
    Inline {
        features: &'a CertificateTheoremGraphQueryFeatures,
        query_features_hash: Hash,
    },
    Artifact {
        features: &'a CertificateTheoremGraphQueryFeatures,
        canonical_bytes: &'a [u8],
        query_features_hash: Hash,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateTheoremGraphDependenciesMode {
    Direct,
    Transitive,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphDependenciesRequest {
    pub declaration: Name,
    pub mode: CertificateTheoremGraphDependenciesMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphDependenciesResponse {
    pub declaration: CertificateTheoremGraphNodeId,
    pub dependencies: Vec<CertificateTheoremGraphNodeId>,
    pub axioms_used: Vec<CertificateTheoremGraphNodeId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphRelatedRequest {
    pub declaration: Name,
    pub limit: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphRelatedResponse {
    pub declaration: CertificateTheoremGraphNodeId,
    pub related: Vec<CertificateTheoremGraphRelatedNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphQueryRequest {
    pub roots: Vec<Name>,
    pub limit: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphQueryResponse {
    pub nodes: Vec<CertificateTheoremGraphRelatedNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphRelatedNode {
    pub node: CertificateTheoremGraphNodeId,
    pub score: CertificateTheoremGraphRelatedScore,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphRelatedScore {
    pub score_microunits: i64,
    pub shared_dependency_count: u32,
    pub dependency_distance: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphUnusedImportsRequest {
    pub kept_declarations: Vec<Name>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphUnusedImportsResponse {
    pub candidates: Vec<CertificateTheoremGraphImportPruneCandidate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateTheoremGraphImportPruneCandidate {
    pub module: Name,
    pub export_hash: Hash,
    pub certificate_hash: Option<Hash>,
    pub reason: CertificateTheoremGraphImportPruneReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateTheoremGraphImportPruneReason {
    NotReferencedByKeptDeclarations,
}

pub fn extract_certificate_theorem_graph(
    certificate_bytes: &[u8],
    imports: &[VerifiedModule],
    options: CertificateTheoremGraphOptions,
) -> Result<CertificateTheoremGraphSnapshot, CertificateTheoremGraphError> {
    let cert = decode_module_cert(certificate_bytes)
        .map_err(|_| CertificateTheoremGraphError::DecodeCertificate)?;
    extract_certificate_theorem_graph_from_cert(&cert, imports, options)
}

pub fn extract_certificate_theorem_graph_from_cert(
    cert: &ModuleCert,
    imports: &[VerifiedModule],
    options: CertificateTheoremGraphOptions,
) -> Result<CertificateTheoremGraphSnapshot, CertificateTheoremGraphError> {
    let import_modules = validate_import_bindings(cert, imports, options)?;
    let export_by_name = export_entries_by_name(cert)?;
    let direct_axioms_by_decl = direct_axioms_by_decl(cert);
    let transitive_axioms_by_decl = transitive_axioms_by_decl(cert);
    let mut state = GraphExtractionState {
        cert,
        export_by_name,
        import_modules,
        nodes: BTreeMap::new(),
        edges: BTreeSet::new(),
    };

    for (decl_index, decl) in cert.declarations.iter().enumerate() {
        let source = local_decl_node_id(cert, decl_index)?;
        insert_node(
            &mut state.nodes,
            local_decl_node(cert, &state.export_by_name, decl_index, decl)?,
        );

        for dependency in &decl.dependencies {
            let target = graph_node_for_global_ref(
                cert,
                &state.export_by_name,
                &state.import_modules,
                &dependency.global_ref,
                Some(dependency.decl_interface_hash),
                None,
            )?;
            insert_node(&mut state.nodes, target.clone());
            state.edges.insert(CertificateTheoremGraphEdge {
                from: source.clone(),
                to: target.id,
                kind: CertificateTheoremGraphEdgeKind::ImportsDeclaration,
            });
        }

        for axiom in direct_axioms_by_decl.get(&decl_index).into_iter().flatten() {
            add_axiom_edge(
                &mut state,
                &source,
                axiom,
                CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom,
            )?;
        }
        for axiom in transitive_axioms_by_decl
            .get(&decl_index)
            .into_iter()
            .flatten()
        {
            add_axiom_edge(
                &mut state,
                &source,
                axiom,
                CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom,
            )?;
        }

        add_decl_payload_edges(&mut state, decl_index, decl, &source)?;
    }

    let imports = cert
        .imports
        .iter()
        .map(|import| CertificateTheoremGraphImportBinding {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
        })
        .collect();
    let mut snapshot = CertificateTheoremGraphSnapshot {
        source_module: cert.header.module.clone(),
        source_export_hash: cert.hashes.export_hash,
        source_certificate_hash: cert.hashes.certificate_hash,
        extractor_version: CertificateTheoremGraphExtractorVersion::CertificateGraphV1,
        imports,
        nodes: state.nodes.into_values().collect(),
        edges: state.edges.into_iter().collect(),
        graph_hash: [0; 32],
    };
    snapshot.graph_hash = certificate_theorem_graph_snapshot_hash(&snapshot);
    Ok(snapshot)
}

pub fn certificate_theorem_graph_snapshot_canonical_bytes(
    snapshot: &CertificateTheoremGraphSnapshot,
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_name(&mut out, &snapshot.source_module);
    out.extend(snapshot.source_export_hash);
    out.extend(snapshot.source_certificate_hash);
    out.push(extractor_version_tag(snapshot.extractor_version));
    encode_uvar(&mut out, snapshot.imports.len() as u64);
    for import in &snapshot.imports {
        encode_name(&mut out, &import.module);
        out.extend(import.export_hash);
        encode_optional_hash(&mut out, import.certificate_hash);
    }
    let mut nodes = snapshot.nodes.clone();
    nodes.sort_by(|lhs, rhs| lhs.id.cmp(&rhs.id));
    encode_uvar(&mut out, nodes.len() as u64);
    for node in &nodes {
        encode_node(&mut out, node);
    }
    let mut edges = snapshot.edges.clone();
    edges.sort();
    encode_uvar(&mut out, edges.len() as u64);
    for edge in &edges {
        encode_node_id(&mut out, &edge.from);
        encode_node_id(&mut out, &edge.to);
        out.push(edge_kind_tag(edge.kind));
    }
    out
}

pub fn certificate_theorem_graph_snapshot_hash(snapshot: &CertificateTheoremGraphSnapshot) -> Hash {
    hash_with_domain(
        CERTIFICATE_THEOREM_GRAPH_HASH_TAG,
        &certificate_theorem_graph_snapshot_canonical_bytes(snapshot),
    )
}

pub fn certificate_theorem_graph_query_features_canonical_bytes(
    features: &CertificateTheoremGraphQueryFeatures,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend(features.environment_hash);
    out.extend(features.goal_fingerprint);
    out.extend(features.local_context_hash);
    out.extend(features.query_profile_hash);
    out.extend(features.theorem_index_fingerprint);
    encode_optional_hash(&mut out, features.graph_snapshot_hash);
    out
}

pub fn certificate_theorem_graph_query_features_hash(
    features: &CertificateTheoremGraphQueryFeatures,
) -> Hash {
    hash_with_domain(
        CERTIFICATE_THEOREM_GRAPH_QUERY_FEATURES_HASH_TAG,
        &certificate_theorem_graph_query_features_canonical_bytes(features),
    )
}

pub fn validate_certificate_theorem_graph_snapshot_sidecar(
    sidecar: CertificateTheoremGraphSnapshotSidecar<'_>,
    options: CertificateTheoremGraphSnapshotValidationOptions<'_>,
) -> Result<Option<CertificateTheoremGraphValidatedSnapshot>, CertificateTheoremGraphError> {
    match sidecar {
        CertificateTheoremGraphSnapshotSidecar::Absent => Ok(None),
        CertificateTheoremGraphSnapshotSidecar::Inline {
            snapshot,
            graph_snapshot_hash,
        } => validate_certificate_theorem_graph_snapshot_contract(
            snapshot,
            graph_snapshot_hash,
            options,
        )
        .map(Some),
        CertificateTheoremGraphSnapshotSidecar::Artifact {
            snapshot,
            canonical_bytes,
            graph_snapshot_hash,
        } => {
            let actual_bytes = certificate_theorem_graph_snapshot_canonical_bytes(snapshot);
            if actual_bytes.as_slice() != canonical_bytes {
                return Err(CertificateTheoremGraphError::GraphSnapshotBytesMismatch);
            }
            validate_certificate_theorem_graph_snapshot_contract(
                snapshot,
                graph_snapshot_hash,
                options,
            )
            .map(Some)
        }
    }
}

pub fn validate_certificate_theorem_graph_query_features_sidecar(
    sidecar: CertificateTheoremGraphQueryFeaturesSidecar<'_>,
) -> Result<Hash, CertificateTheoremGraphError> {
    match sidecar {
        CertificateTheoremGraphQueryFeaturesSidecar::Inline {
            features,
            query_features_hash,
        } => validate_certificate_theorem_graph_query_features_hash(features, query_features_hash),
        CertificateTheoremGraphQueryFeaturesSidecar::Artifact {
            features,
            canonical_bytes,
            query_features_hash,
        } => {
            let actual_bytes = certificate_theorem_graph_query_features_canonical_bytes(features);
            if actual_bytes.as_slice() != canonical_bytes {
                return Err(CertificateTheoremGraphError::QueryFeaturesBytesMismatch);
            }
            validate_certificate_theorem_graph_query_features_hash(features, query_features_hash)
        }
    }
}

pub fn certificate_theorem_graph_verified_identities(
    snapshot: &CertificateTheoremGraphSnapshot,
) -> Result<Vec<CertificateTheoremGraphVerifiedIdentity>, CertificateTheoremGraphError> {
    validate_certificate_theorem_graph_snapshot_contract(
        snapshot,
        snapshot.graph_hash,
        CertificateTheoremGraphSnapshotValidationOptions::default(),
    )
    .map(|validated| validated.verified_identities)
}

pub fn certificate_theorem_graph_verified_identity_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    node: &CertificateTheoremGraphNode,
) -> Option<CertificateTheoremGraphVerifiedIdentity> {
    if !certificate_theorem_graph_node_is_certificate_bound_public_export(node) {
        return None;
    }
    let statement_or_type_hash = node.type_hash?;
    match &node.id.scope {
        CertificateTheoremGraphNodeScope::Builtin => None,
        CertificateTheoremGraphNodeScope::Imported {
            import_export_hash,
            import_certificate_hash,
        } => Some(CertificateTheoremGraphVerifiedIdentity {
            module: node.id.module.clone(),
            name: node.id.name.clone(),
            export_hash: *import_export_hash,
            certificate_hash: *import_certificate_hash,
            decl_interface_hash: node.id.decl_interface_hash,
            statement_or_type_hash,
        }),
        CertificateTheoremGraphNodeScope::Local
        | CertificateTheoremGraphNodeScope::LocalGenerated { .. } => {
            if node.id.module != snapshot.source_module {
                return None;
            }
            Some(CertificateTheoremGraphVerifiedIdentity {
                module: node.id.module.clone(),
                name: node.id.name.clone(),
                export_hash: snapshot.source_export_hash,
                certificate_hash: Some(snapshot.source_certificate_hash),
                decl_interface_hash: node.id.decl_interface_hash,
                statement_or_type_hash,
            })
        }
    }
}

pub fn certificate_theorem_graph_node_is_certificate_bound_public_export(
    node: &CertificateTheoremGraphNode,
) -> bool {
    !matches!(node.id.scope, CertificateTheoremGraphNodeScope::Builtin)
        && !matches!(
            node.kind,
            CertificateTheoremGraphNodeKind::Builtin | CertificateTheoremGraphNodeKind::Unknown
        )
        && node.type_hash.is_some()
}

fn validate_certificate_theorem_graph_snapshot_contract(
    snapshot: &CertificateTheoremGraphSnapshot,
    graph_snapshot_hash: Hash,
    options: CertificateTheoremGraphSnapshotValidationOptions<'_>,
) -> Result<CertificateTheoremGraphValidatedSnapshot, CertificateTheoremGraphError> {
    let actual_hash = certificate_theorem_graph_snapshot_hash(snapshot);
    if snapshot.graph_hash != actual_hash {
        return Err(CertificateTheoremGraphError::GraphSnapshotHashMismatch {
            expected: snapshot.graph_hash,
            actual: actual_hash,
        });
    }
    if graph_snapshot_hash != actual_hash {
        return Err(CertificateTheoremGraphError::GraphSnapshotHashMismatch {
            expected: graph_snapshot_hash,
            actual: actual_hash,
        });
    }

    let mut node_ids = BTreeSet::new();
    for node in &snapshot.nodes {
        if !node_ids.insert(node.id.clone()) {
            return Err(CertificateTheoremGraphError::DuplicateGraphNode {
                node: Box::new(node.id.clone()),
            });
        }
        validate_certificate_theorem_graph_node_scope_binding(snapshot, node)?;
        validate_certificate_theorem_graph_node_metadata(node)?;
    }

    let mut edges = BTreeSet::new();
    for edge in &snapshot.edges {
        if !node_ids.contains(&edge.from) || !node_ids.contains(&edge.to) {
            return Err(CertificateTheoremGraphError::MalformedEdgeReference {
                from: Box::new(edge.from.clone()),
                to: Box::new(edge.to.clone()),
            });
        }
        if !edges.insert(edge.clone()) {
            return Err(CertificateTheoremGraphError::DuplicateGraphEdge {
                edge: Box::new(edge.clone()),
            });
        }
    }

    let verified_set: BTreeSet<_> = options.verified_identities.iter().cloned().collect();
    let mut verified_identities = Vec::new();
    for node in &snapshot.nodes {
        if let Some(identity) = certificate_theorem_graph_verified_identity_for_node(snapshot, node)
        {
            if options.require_verified_identities && !verified_set.contains(&identity) {
                if options.verified_identities.iter().any(|verified| {
                    verified.module == identity.module && verified.name == identity.name
                }) {
                    return Err(CertificateTheoremGraphError::VerifiedIdentityMismatch {
                        node: Box::new(node.id.clone()),
                    });
                }
                return Err(CertificateTheoremGraphError::MissingVerifiedIdentity {
                    node: Box::new(node.id.clone()),
                });
            }
            verified_identities.push(identity);
        } else if certificate_theorem_graph_node_claims_unverified_candidate(node) {
            return Err(CertificateTheoremGraphError::UnverifiedCandidateNode {
                node: Box::new(node.id.clone()),
            });
        }
    }

    verified_identities.sort();
    Ok(CertificateTheoremGraphValidatedSnapshot {
        graph_snapshot_hash: actual_hash,
        verified_identities,
    })
}

fn validate_certificate_theorem_graph_query_features_hash(
    features: &CertificateTheoremGraphQueryFeatures,
    expected_hash: Hash,
) -> Result<Hash, CertificateTheoremGraphError> {
    let actual_hash = certificate_theorem_graph_query_features_hash(features);
    if expected_hash != actual_hash {
        return Err(CertificateTheoremGraphError::QueryFeaturesHashMismatch {
            expected: expected_hash,
            actual: actual_hash,
        });
    }
    Ok(actual_hash)
}

fn validate_certificate_theorem_graph_node_metadata(
    node: &CertificateTheoremGraphNode,
) -> Result<(), CertificateTheoremGraphError> {
    let mut previous = None;
    for tag in &node.metadata.domain_tags {
        if !certificate_theorem_graph_domain_tag_is_valid(tag) {
            return Err(CertificateTheoremGraphError::MalformedNodeMetadata {
                node: Box::new(node.id.clone()),
            });
        }
        if previous.as_ref().is_some_and(|previous| *previous >= tag) {
            return Err(CertificateTheoremGraphError::MalformedNodeMetadata {
                node: Box::new(node.id.clone()),
            });
        }
        previous = Some(tag);
    }
    Ok(())
}

fn validate_certificate_theorem_graph_node_scope_binding(
    snapshot: &CertificateTheoremGraphSnapshot,
    node: &CertificateTheoremGraphNode,
) -> Result<(), CertificateTheoremGraphError> {
    match &node.id.scope {
        CertificateTheoremGraphNodeScope::Builtin => Ok(()),
        CertificateTheoremGraphNodeScope::Local
        | CertificateTheoremGraphNodeScope::LocalGenerated { .. } => {
            if node.id.module == snapshot.source_module {
                Ok(())
            } else {
                Err(CertificateTheoremGraphError::VerifiedIdentityMismatch {
                    node: Box::new(node.id.clone()),
                })
            }
        }
        CertificateTheoremGraphNodeScope::Imported {
            import_export_hash,
            import_certificate_hash,
        } => {
            if snapshot.imports.iter().any(|import| {
                import.module == node.id.module
                    && import.export_hash == *import_export_hash
                    && import.certificate_hash == *import_certificate_hash
            }) {
                Ok(())
            } else {
                Err(CertificateTheoremGraphError::MissingVerifiedIdentity {
                    node: Box::new(node.id.clone()),
                })
            }
        }
    }
}

fn certificate_theorem_graph_domain_tag_is_valid(tag: &str) -> bool {
    !tag.is_empty()
        && tag.len() <= 64
        && tag
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'.' | b':' | b'-'))
}

fn certificate_theorem_graph_node_claims_unverified_candidate(
    node: &CertificateTheoremGraphNode,
) -> bool {
    !matches!(node.id.scope, CertificateTheoremGraphNodeScope::Builtin)
        && (node.kind == CertificateTheoremGraphNodeKind::Unknown
            || (matches!(
                node.kind,
                CertificateTheoremGraphNodeKind::Axiom | CertificateTheoremGraphNodeKind::Theorem
            ) && node.type_hash.is_none()))
}

pub fn certificate_theorem_graph_dependencies(
    snapshot: &CertificateTheoremGraphSnapshot,
    request: &CertificateTheoremGraphDependenciesRequest,
) -> Result<CertificateTheoremGraphDependenciesResponse, CertificateTheoremGraphError> {
    let declaration = certificate_theorem_graph_node_id_by_name(snapshot, &request.declaration)?;
    let dependencies =
        certificate_theorem_graph_dependencies_for_node(snapshot, &declaration, request.mode);
    let axioms_used =
        certificate_theorem_graph_axiom_dependencies_for_node(snapshot, &declaration, request.mode);
    Ok(CertificateTheoremGraphDependenciesResponse {
        declaration,
        dependencies,
        axioms_used,
    })
}

pub fn certificate_theorem_graph_related(
    snapshot: &CertificateTheoremGraphSnapshot,
    request: &CertificateTheoremGraphRelatedRequest,
) -> Result<CertificateTheoremGraphRelatedResponse, CertificateTheoremGraphError> {
    let declaration = certificate_theorem_graph_node_id_by_name(snapshot, &request.declaration)?;
    let mut related = certificate_theorem_graph_related_for_node(snapshot, &declaration);
    related.truncate(request.limit as usize);
    Ok(CertificateTheoremGraphRelatedResponse {
        declaration,
        related,
    })
}

pub fn certificate_theorem_graph_query(
    snapshot: &CertificateTheoremGraphSnapshot,
    request: &CertificateTheoremGraphQueryRequest,
) -> Result<CertificateTheoremGraphQueryResponse, CertificateTheoremGraphError> {
    let mut nodes =
        BTreeMap::<CertificateTheoremGraphNodeId, CertificateTheoremGraphRelatedScore>::new();
    if request.roots.is_empty() {
        for node in certificate_theorem_graph_public_export_nodes(snapshot) {
            nodes.insert(
                node.id.clone(),
                CertificateTheoremGraphRelatedScore {
                    score_microunits: 0,
                    shared_dependency_count: 0,
                    dependency_distance: None,
                },
            );
        }
    } else {
        for root_name in &request.roots {
            let root = certificate_theorem_graph_node_id_by_name(snapshot, root_name)?;
            let root_dependency_count = certificate_theorem_graph_dependencies_for_node(
                snapshot,
                &root,
                CertificateTheoremGraphDependenciesMode::Transitive,
            )
            .len();
            certificate_theorem_graph_merge_query_node(
                &mut nodes,
                root.clone(),
                CertificateTheoremGraphRelatedScore {
                    score_microunits: 2_000_000,
                    shared_dependency_count: usize_to_u32(root_dependency_count),
                    dependency_distance: Some(0),
                },
            );
            for related in certificate_theorem_graph_related_for_node(snapshot, &root) {
                certificate_theorem_graph_merge_query_node(&mut nodes, related.node, related.score);
            }
        }
    }

    let mut nodes: Vec<_> = nodes
        .into_iter()
        .map(|(node, score)| CertificateTheoremGraphRelatedNode { node, score })
        .collect();
    nodes.sort_by(certificate_theorem_graph_related_node_order);
    nodes.truncate(request.limit as usize);
    Ok(CertificateTheoremGraphQueryResponse { nodes })
}

pub fn certificate_theorem_graph_unused_imports(
    snapshot: &CertificateTheoremGraphSnapshot,
    request: &CertificateTheoremGraphUnusedImportsRequest,
) -> Result<CertificateTheoremGraphUnusedImportsResponse, CertificateTheoremGraphError> {
    let mut used_import_modules = BTreeSet::new();
    for kept in &request.kept_declarations {
        let root = certificate_theorem_graph_node_id_by_name(snapshot, kept)?;
        if matches!(
            root.scope,
            CertificateTheoremGraphNodeScope::Imported { .. }
        ) {
            used_import_modules.insert(root.module.clone());
        }
        for dependency in certificate_theorem_graph_dependencies_for_node(
            snapshot,
            &root,
            CertificateTheoremGraphDependenciesMode::Transitive,
        ) {
            if matches!(
                dependency.scope,
                CertificateTheoremGraphNodeScope::Imported { .. }
            ) {
                used_import_modules.insert(dependency.module);
            }
        }
    }
    let candidates = snapshot
        .imports
        .iter()
        .filter(|import| !used_import_modules.contains(&import.module))
        .map(|import| CertificateTheoremGraphImportPruneCandidate {
            module: import.module.clone(),
            export_hash: import.export_hash,
            certificate_hash: import.certificate_hash,
            reason: CertificateTheoremGraphImportPruneReason::NotReferencedByKeptDeclarations,
        })
        .collect();
    Ok(CertificateTheoremGraphUnusedImportsResponse { candidates })
}

fn certificate_theorem_graph_public_export_nodes(
    snapshot: &CertificateTheoremGraphSnapshot,
) -> Vec<&CertificateTheoremGraphNode> {
    let mut nodes: Vec<_> = snapshot
        .nodes
        .iter()
        .filter(|node| certificate_theorem_graph_node_is_certificate_bound_public_export(node))
        .collect();
    nodes.sort_by(|left, right| left.id.cmp(&right.id));
    nodes
}

fn certificate_theorem_graph_node_id_by_name(
    snapshot: &CertificateTheoremGraphSnapshot,
    name: &Name,
) -> Result<CertificateTheoremGraphNodeId, CertificateTheoremGraphError> {
    certificate_theorem_graph_public_export_nodes(snapshot)
        .into_iter()
        .find(|node| node.id.name == *name)
        .map(|node| node.id.clone())
        .ok_or_else(|| CertificateTheoremGraphError::MissingGraphNode { name: name.clone() })
}

fn certificate_theorem_graph_dependencies_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    id: &CertificateTheoremGraphNodeId,
    mode: CertificateTheoremGraphDependenciesMode,
) -> Vec<CertificateTheoremGraphNodeId> {
    match mode {
        CertificateTheoremGraphDependenciesMode::Direct => {
            certificate_theorem_graph_direct_dependencies_for_node(snapshot, id)
        }
        CertificateTheoremGraphDependenciesMode::Transitive => {
            certificate_theorem_graph_transitive_dependencies_for_node(snapshot, id)
        }
    }
}

fn certificate_theorem_graph_direct_dependencies_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    id: &CertificateTheoremGraphNodeId,
) -> Vec<CertificateTheoremGraphNodeId> {
    let mut dependencies = BTreeSet::new();
    for edge in &snapshot.edges {
        if &edge.from == id
            && certificate_theorem_graph_direct_dependency_edge(edge.kind)
            && certificate_theorem_graph_public_export_node_id(snapshot, &edge.to)
        {
            dependencies.insert(edge.to.clone());
        }
    }
    dependencies.into_iter().collect()
}

fn certificate_theorem_graph_transitive_dependencies_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    id: &CertificateTheoremGraphNodeId,
) -> Vec<CertificateTheoremGraphNodeId> {
    let mut dependencies = BTreeSet::new();
    let mut visited = BTreeSet::from([id.clone()]);
    let mut queue = VecDeque::from([id.clone()]);
    while let Some(current) = queue.pop_front() {
        for edge in &snapshot.edges {
            if edge.from != current
                || !certificate_theorem_graph_transitive_dependency_edge(edge.kind)
                || !certificate_theorem_graph_public_export_node_id(snapshot, &edge.to)
            {
                continue;
            }
            if &edge.to == id {
                continue;
            }
            if dependencies.insert(edge.to.clone()) && visited.insert(edge.to.clone()) {
                queue.push_back(edge.to.clone());
            }
        }
    }
    dependencies.into_iter().collect()
}

fn certificate_theorem_graph_axiom_dependencies_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    id: &CertificateTheoremGraphNodeId,
    mode: CertificateTheoremGraphDependenciesMode,
) -> Vec<CertificateTheoremGraphNodeId> {
    let mut axioms = BTreeSet::new();
    for edge in &snapshot.edges {
        let include = match mode {
            CertificateTheoremGraphDependenciesMode::Direct => {
                edge.kind == CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom
            }
            CertificateTheoremGraphDependenciesMode::Transitive => {
                edge.kind == CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom
                    || edge.kind == CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom
            }
        };
        if &edge.from == id
            && include
            && certificate_theorem_graph_public_export_node_id(snapshot, &edge.to)
        {
            axioms.insert(edge.to.clone());
        }
    }
    axioms.into_iter().collect()
}

fn certificate_theorem_graph_related_for_node(
    snapshot: &CertificateTheoremGraphSnapshot,
    declaration: &CertificateTheoremGraphNodeId,
) -> Vec<CertificateTheoremGraphRelatedNode> {
    let root_dependencies: BTreeSet<_> =
        certificate_theorem_graph_transitive_dependencies_for_node(snapshot, declaration)
            .into_iter()
            .collect();
    let mut related = Vec::new();
    for node in certificate_theorem_graph_public_export_nodes(snapshot) {
        if node.id == *declaration {
            continue;
        }
        let candidate_dependencies: BTreeSet<_> =
            certificate_theorem_graph_transitive_dependencies_for_node(snapshot, &node.id)
                .into_iter()
                .collect();
        let shared_dependency_count = root_dependencies
            .intersection(&candidate_dependencies)
            .count();
        let dependency_distance =
            certificate_theorem_graph_shortest_dependency_distance(snapshot, declaration, &node.id);
        if shared_dependency_count == 0 && dependency_distance.is_none() {
            continue;
        }
        related.push(CertificateTheoremGraphRelatedNode {
            node: node.id.clone(),
            score: certificate_theorem_graph_related_score(
                shared_dependency_count,
                dependency_distance,
            ),
        });
    }
    related.sort_by(certificate_theorem_graph_related_node_order);
    related
}

fn certificate_theorem_graph_related_score(
    shared_dependency_count: usize,
    dependency_distance: Option<u32>,
) -> CertificateTheoremGraphRelatedScore {
    let distance_score = dependency_distance
        .map(|distance| 1_000_000i64.saturating_sub(i64::from(distance) * 10_000))
        .unwrap_or(0);
    let shared_dependency_count = usize_to_u32(shared_dependency_count);
    CertificateTheoremGraphRelatedScore {
        score_microunits: i64::from(shared_dependency_count) * 100_000 + distance_score,
        shared_dependency_count,
        dependency_distance,
    }
}

fn certificate_theorem_graph_shortest_dependency_distance(
    snapshot: &CertificateTheoremGraphSnapshot,
    source: &CertificateTheoremGraphNodeId,
    target: &CertificateTheoremGraphNodeId,
) -> Option<u32> {
    if source == target {
        return Some(0);
    }
    let mut visited = BTreeSet::from([source.clone()]);
    let mut queue = VecDeque::from([(source.clone(), 0u32)]);
    while let Some((current, distance)) = queue.pop_front() {
        for edge in &snapshot.edges {
            if edge.from != current
                || !certificate_theorem_graph_transitive_dependency_edge(edge.kind)
                || !certificate_theorem_graph_public_export_node_id(snapshot, &edge.to)
            {
                continue;
            }
            let next_distance = distance.saturating_add(1);
            if &edge.to == target {
                return Some(next_distance);
            }
            if visited.insert(edge.to.clone()) {
                queue.push_back((edge.to.clone(), next_distance));
            }
        }
    }
    None
}

fn certificate_theorem_graph_direct_dependency_edge(kind: CertificateTheoremGraphEdgeKind) -> bool {
    matches!(
        kind,
        CertificateTheoremGraphEdgeKind::ImportsDeclaration
            | CertificateTheoremGraphEdgeKind::MentionsType
            | CertificateTheoremGraphEdgeKind::UsesConstant
            | CertificateTheoremGraphEdgeKind::GeneratedDeclaration
            | CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom
    )
}

fn certificate_theorem_graph_transitive_dependency_edge(
    kind: CertificateTheoremGraphEdgeKind,
) -> bool {
    matches!(
        kind,
        CertificateTheoremGraphEdgeKind::ImportsDeclaration
            | CertificateTheoremGraphEdgeKind::MentionsType
            | CertificateTheoremGraphEdgeKind::UsesConstant
            | CertificateTheoremGraphEdgeKind::GeneratedDeclaration
            | CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom
            | CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom
    )
}

fn certificate_theorem_graph_public_export_node_id(
    snapshot: &CertificateTheoremGraphSnapshot,
    id: &CertificateTheoremGraphNodeId,
) -> bool {
    snapshot
        .node(id)
        .is_some_and(certificate_theorem_graph_node_is_certificate_bound_public_export)
}

fn certificate_theorem_graph_related_node_order(
    left: &CertificateTheoremGraphRelatedNode,
    right: &CertificateTheoremGraphRelatedNode,
) -> std::cmp::Ordering {
    right
        .score
        .score_microunits
        .cmp(&left.score.score_microunits)
        .then_with(|| {
            left.score
                .dependency_distance
                .unwrap_or(u32::MAX)
                .cmp(&right.score.dependency_distance.unwrap_or(u32::MAX))
        })
        .then_with(|| {
            right
                .score
                .shared_dependency_count
                .cmp(&left.score.shared_dependency_count)
        })
        .then_with(|| left.node.cmp(&right.node))
}

fn certificate_theorem_graph_merge_query_node(
    nodes: &mut BTreeMap<CertificateTheoremGraphNodeId, CertificateTheoremGraphRelatedScore>,
    node: CertificateTheoremGraphNodeId,
    score: CertificateTheoremGraphRelatedScore,
) {
    nodes
        .entry(node)
        .and_modify(|existing| {
            if score.score_microunits > existing.score_microunits {
                *existing = score;
            }
        })
        .or_insert(score);
}

fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn validate_import_bindings<'a>(
    cert: &ModuleCert,
    imports: &'a [VerifiedModule],
    options: CertificateTheoremGraphOptions,
) -> Result<BTreeMap<Name, &'a VerifiedModule>, CertificateTheoremGraphError> {
    let mut by_module = BTreeMap::new();
    for import in imports {
        if by_module.insert(import.module().clone(), import).is_some() {
            return Err(CertificateTheoremGraphError::DuplicateImportBinding {
                module: import.module().clone(),
            });
        }
    }
    for required in &cert.imports {
        let Some(verified) = by_module.get(&required.module) else {
            return Err(CertificateTheoremGraphError::MissingImportBinding {
                module: required.module.clone(),
            });
        };
        if verified.export_hash() != required.export_hash {
            return Err(CertificateTheoremGraphError::ImportExportHashMismatch {
                module: required.module.clone(),
            });
        }
        if let Some(certificate_hash) = required.certificate_hash {
            if verified.certificate_hash() != certificate_hash {
                return Err(
                    CertificateTheoremGraphError::ImportCertificateHashMismatch {
                        module: required.module.clone(),
                    },
                );
            }
        } else if options.require_import_certificate_hashes {
            return Err(CertificateTheoremGraphError::ImportCertificateHashMissing {
                module: required.module.clone(),
            });
        }
    }
    Ok(by_module)
}

fn export_entries_by_name(
    cert: &ModuleCert,
) -> Result<BTreeMap<Name, &ExportEntry>, CertificateTheoremGraphError> {
    let mut exports = BTreeMap::new();
    for entry in &cert.export_block {
        exports.insert(name(cert, entry.name)?, entry);
    }
    Ok(exports)
}

fn direct_axioms_by_decl(cert: &ModuleCert) -> BTreeMap<usize, Vec<AxiomRef>> {
    cert.axiom_report
        .per_declaration
        .iter()
        .map(|report| (report.decl_index, report.direct_axioms.clone()))
        .collect()
}

fn transitive_axioms_by_decl(cert: &ModuleCert) -> BTreeMap<usize, Vec<AxiomRef>> {
    cert.axiom_report
        .per_declaration
        .iter()
        .map(|report| (report.decl_index, report.transitive_axioms.clone()))
        .collect()
}

struct GraphExtractionState<'a> {
    cert: &'a ModuleCert,
    export_by_name: BTreeMap<Name, &'a ExportEntry>,
    import_modules: BTreeMap<Name, &'a VerifiedModule>,
    nodes: BTreeMap<CertificateTheoremGraphNodeId, CertificateTheoremGraphNode>,
    edges: BTreeSet<CertificateTheoremGraphEdge>,
}

fn add_decl_payload_edges(
    state: &mut GraphExtractionState<'_>,
    decl_index: usize,
    decl: &DeclCert,
    source: &CertificateTheoremGraphNodeId,
) -> Result<(), CertificateTheoremGraphError> {
    match &decl.decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
            add_term_edges(
                state,
                source,
                *ty,
                CertificateTheoremGraphEdgeKind::MentionsType,
            )?;
        }
        DeclPayload::Def {
            ty,
            value,
            reducibility,
            ..
        }
        | DeclPayload::DefConstrained {
            ty,
            value,
            reducibility,
            ..
        } => {
            add_term_edges(
                state,
                source,
                *ty,
                CertificateTheoremGraphEdgeKind::MentionsType,
            )?;
            if *reducibility == CertReducibility::Reducible {
                add_term_edges(
                    state,
                    source,
                    *value,
                    CertificateTheoremGraphEdgeKind::UsesConstant,
                )?;
            }
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => {
            add_term_edges(
                state,
                source,
                *ty,
                CertificateTheoremGraphEdgeKind::MentionsType,
            )?;
            add_term_edges(
                state,
                source,
                *proof,
                CertificateTheoremGraphEdgeKind::UsesConstant,
            )?;
        }
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => {
            for binder in params.iter().chain(indices) {
                add_term_edges(
                    state,
                    source,
                    binder.ty,
                    CertificateTheoremGraphEdgeKind::MentionsType,
                )?;
            }
            for constructor in constructors {
                add_generated_node_and_type_edges(
                    state,
                    decl_index,
                    source,
                    constructor.name,
                    constructor.ty,
                )?;
            }
            if let Some(recursor) = recursor {
                add_generated_node_and_type_edges(
                    state,
                    decl_index,
                    source,
                    recursor.name,
                    recursor.ty,
                )?;
            }
        }
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                for binder in inductive.params.iter().chain(&inductive.indices) {
                    add_term_edges(
                        state,
                        source,
                        binder.ty,
                        CertificateTheoremGraphEdgeKind::MentionsType,
                    )?;
                }
                for constructor in &inductive.constructors {
                    add_generated_node_and_type_edges(
                        state,
                        decl_index,
                        source,
                        constructor.name,
                        constructor.ty,
                    )?;
                }
                if let Some(recursor) = &inductive.recursor {
                    add_generated_node_and_type_edges(
                        state,
                        decl_index,
                        source,
                        recursor.name,
                        recursor.ty,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn add_generated_node_and_type_edges(
    state: &mut GraphExtractionState<'_>,
    decl_index: usize,
    source: &CertificateTheoremGraphNodeId,
    generated_name: NameId,
    generated_ty: TermId,
) -> Result<(), CertificateTheoremGraphError> {
    let generated = local_generated_node(
        state.cert,
        &state.export_by_name,
        decl_index,
        generated_name,
    )?;
    state.edges.insert(CertificateTheoremGraphEdge {
        from: source.clone(),
        to: generated.id.clone(),
        kind: CertificateTheoremGraphEdgeKind::GeneratedDeclaration,
    });
    insert_node(&mut state.nodes, generated.clone());
    add_term_edges(
        state,
        &generated.id,
        generated_ty,
        CertificateTheoremGraphEdgeKind::MentionsType,
    )
}

fn add_axiom_edge(
    state: &mut GraphExtractionState<'_>,
    source: &CertificateTheoremGraphNodeId,
    axiom: &AxiomRef,
    kind: CertificateTheoremGraphEdgeKind,
) -> Result<(), CertificateTheoremGraphError> {
    let target = graph_node_for_global_ref(
        state.cert,
        &state.export_by_name,
        &state.import_modules,
        &axiom.global_ref,
        Some(axiom.decl_interface_hash),
        Some(CertificateTheoremGraphNodeKind::Axiom),
    )?;
    insert_node(&mut state.nodes, target.clone());
    state.edges.insert(CertificateTheoremGraphEdge {
        from: source.clone(),
        to: target.id,
        kind,
    });
    Ok(())
}

fn add_term_edges(
    state: &mut GraphExtractionState<'_>,
    source: &CertificateTheoremGraphNodeId,
    term_id: TermId,
    kind: CertificateTheoremGraphEdgeKind,
) -> Result<(), CertificateTheoremGraphError> {
    let mut refs = BTreeSet::new();
    let mut visited = BTreeSet::new();
    collect_const_refs(state.cert, term_id, &mut visited, &mut refs)?;
    for global_ref in refs {
        let target = graph_node_for_global_ref(
            state.cert,
            &state.export_by_name,
            &state.import_modules,
            &global_ref,
            None,
            None,
        )?;
        insert_node(&mut state.nodes, target.clone());
        state.edges.insert(CertificateTheoremGraphEdge {
            from: source.clone(),
            to: target.id,
            kind,
        });
    }
    Ok(())
}

fn collect_const_refs(
    cert: &ModuleCert,
    term_id: TermId,
    visited: &mut BTreeSet<TermId>,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<(), CertificateTheoremGraphError> {
    if !visited.insert(term_id) {
        return Ok(());
    }
    match term(cert, term_id)? {
        TermNode::Sort(_) | TermNode::BVar(_) => {}
        TermNode::Const { global_ref, .. } => {
            refs.insert(global_ref.clone());
        }
        TermNode::App(fun, arg) => {
            collect_const_refs(cert, *fun, visited, refs)?;
            collect_const_refs(cert, *arg, visited, refs)?;
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            collect_const_refs(cert, *ty, visited, refs)?;
            collect_const_refs(cert, *body, visited, refs)?;
        }
        TermNode::Let { ty, value, body } => {
            collect_const_refs(cert, *ty, visited, refs)?;
            collect_const_refs(cert, *value, visited, refs)?;
            collect_const_refs(cert, *body, visited, refs)?;
        }
    }
    Ok(())
}

fn local_decl_node(
    cert: &ModuleCert,
    export_by_name: &BTreeMap<Name, &ExportEntry>,
    decl_index: usize,
    decl: &DeclCert,
) -> Result<CertificateTheoremGraphNode, CertificateTheoremGraphError> {
    let name = decl_payload_name(cert, &decl.decl)?;
    let export = export_by_name.get(&name);
    let type_hash = export.map(|entry| entry.type_hash);
    let proof_hash = match &decl.decl {
        DeclPayload::Theorem { proof, .. } | DeclPayload::TheoremConstrained { proof, .. } => Some(
            term_hash(cert, *proof)
                .map_err(|_| CertificateTheoremGraphError::TermHash { term_id: *proof })?,
        ),
        _ => None,
    };
    let body_hash = match &decl.decl {
        DeclPayload::Def {
            value,
            reducibility,
            ..
        }
        | DeclPayload::DefConstrained {
            value,
            reducibility,
            ..
        } if *reducibility == CertReducibility::Reducible => Some(
            term_hash(cert, *value)
                .map_err(|_| CertificateTheoremGraphError::TermHash { term_id: *value })?,
        ),
        _ => None,
    };
    Ok(CertificateTheoremGraphNode {
        id: local_decl_node_id(cert, decl_index)?,
        kind: decl_payload_node_kind(&decl.decl),
        type_hash,
        proof_hash,
        body_hash,
        metadata: CertificateTheoremGraphNodeMetadata::default(),
    })
}

fn local_generated_node(
    cert: &ModuleCert,
    export_by_name: &BTreeMap<Name, &ExportEntry>,
    decl_index: usize,
    generated_name: NameId,
) -> Result<CertificateTheoremGraphNode, CertificateTheoremGraphError> {
    let name = name(cert, generated_name)?;
    let entry = export_by_name
        .get(&name)
        .ok_or_else(|| CertificateTheoremGraphError::MissingExport { name: name.clone() })?;
    Ok(CertificateTheoremGraphNode {
        id: CertificateTheoremGraphNodeId {
            scope: CertificateTheoremGraphNodeScope::LocalGenerated {
                source_decl_index: decl_index,
            },
            module: cert.header.module.clone(),
            name,
            decl_interface_hash: entry.decl_interface_hash,
        },
        kind: export_kind_to_node_kind(entry.kind),
        type_hash: Some(entry.type_hash),
        proof_hash: None,
        body_hash: entry.body_hash,
        metadata: CertificateTheoremGraphNodeMetadata::default(),
    })
}

fn graph_node_for_global_ref(
    cert: &ModuleCert,
    export_by_name: &BTreeMap<Name, &ExportEntry>,
    import_modules: &BTreeMap<Name, &VerifiedModule>,
    global_ref: &GlobalRef,
    decl_interface_hash: Option<Hash>,
    override_kind: Option<CertificateTheoremGraphNodeKind>,
) -> Result<CertificateTheoremGraphNode, CertificateTheoremGraphError> {
    match global_ref {
        GlobalRef::Builtin {
            name: name_id,
            decl_interface_hash,
        } => {
            let name = name(cert, *name_id)?;
            Ok(CertificateTheoremGraphNode {
                id: CertificateTheoremGraphNodeId {
                    scope: CertificateTheoremGraphNodeScope::Builtin,
                    module: Name::from_dotted("builtin"),
                    name,
                    decl_interface_hash: *decl_interface_hash,
                },
                kind: override_kind.unwrap_or(CertificateTheoremGraphNodeKind::Builtin),
                type_hash: None,
                proof_hash: None,
                body_hash: None,
                metadata: CertificateTheoremGraphNodeMetadata::default(),
            })
        }
        GlobalRef::Imported {
            import_index,
            name: name_id,
            decl_interface_hash: ref_interface_hash,
        } => {
            let import = cert.imports.get(*import_index).ok_or_else(|| {
                CertificateTheoremGraphError::MissingImportBinding {
                    module: Name::from_dotted("<invalid-import-index>"),
                }
            })?;
            let name = name(cert, *name_id)?;
            let verified = import_modules.get(&import.module).ok_or_else(|| {
                CertificateTheoremGraphError::MissingImportBinding {
                    module: import.module.clone(),
                }
            })?;
            let import_export = imported_export(verified, &import.module, &name)?;
            let expected_interface_hash = decl_interface_hash.unwrap_or(*ref_interface_hash);
            if expected_interface_hash != *ref_interface_hash
                || expected_interface_hash != import_export.decl_interface_hash
            {
                return Err(CertificateTheoremGraphError::DeclInterfaceHashMismatch { name });
            }
            Ok(CertificateTheoremGraphNode {
                id: CertificateTheoremGraphNodeId {
                    scope: CertificateTheoremGraphNodeScope::Imported {
                        import_export_hash: import.export_hash,
                        import_certificate_hash: import.certificate_hash,
                    },
                    module: import.module.clone(),
                    name,
                    decl_interface_hash: expected_interface_hash,
                },
                kind: override_kind.unwrap_or_else(|| export_kind_to_node_kind(import_export.kind)),
                type_hash: Some(import_export.type_hash),
                proof_hash: None,
                body_hash: import_export.body_hash,
                metadata: CertificateTheoremGraphNodeMetadata::default(),
            })
        }
        GlobalRef::Local { decl_index } => {
            let decl = cert.declarations.get(*decl_index).ok_or(
                CertificateTheoremGraphError::MissingDeclaration {
                    decl_index: *decl_index,
                },
            )?;
            let mut node = local_decl_node(cert, export_by_name, *decl_index, decl)?;
            if let Some(expected) = decl_interface_hash {
                if expected != node.id.decl_interface_hash {
                    return Err(CertificateTheoremGraphError::DeclInterfaceHashMismatch {
                        name: node.id.name,
                    });
                }
                node.id.decl_interface_hash = expected;
            }
            Ok(node)
        }
        GlobalRef::LocalGenerated {
            decl_index,
            name: name_id,
        } => {
            let mut node = local_generated_node(cert, export_by_name, *decl_index, *name_id)?;
            if let Some(expected) = decl_interface_hash {
                if expected != node.id.decl_interface_hash {
                    return Err(CertificateTheoremGraphError::DeclInterfaceHashMismatch {
                        name: node.id.name,
                    });
                }
                node.id.decl_interface_hash = expected;
            }
            Ok(node)
        }
    }
}

fn imported_export<'a>(
    import: &'a VerifiedModule,
    module: &Name,
    target: &Name,
) -> Result<&'a ExportEntry, CertificateTheoremGraphError> {
    for entry in import.export_block() {
        let Some(entry_name) = import.name_table().get(entry.name) else {
            return Err(CertificateTheoremGraphError::MissingImportedExport {
                module: module.clone(),
                name: target.clone(),
            });
        };
        if entry_name == target {
            return Ok(entry);
        }
    }
    Err(CertificateTheoremGraphError::MissingImportedExport {
        module: module.clone(),
        name: target.clone(),
    })
}

fn insert_node(
    nodes: &mut BTreeMap<CertificateTheoremGraphNodeId, CertificateTheoremGraphNode>,
    node: CertificateTheoremGraphNode,
) {
    nodes
        .entry(node.id.clone())
        .and_modify(|existing| {
            if existing.kind == CertificateTheoremGraphNodeKind::Unknown
                && node.kind != CertificateTheoremGraphNodeKind::Unknown
            {
                existing.kind = node.kind;
            }
            existing.type_hash = existing.type_hash.or(node.type_hash);
            existing.proof_hash = existing.proof_hash.or(node.proof_hash);
            existing.body_hash = existing.body_hash.or(node.body_hash);
            merge_node_metadata(&mut existing.metadata, node.metadata.clone());
        })
        .or_insert(node);
}

fn merge_node_metadata(
    existing: &mut CertificateTheoremGraphNodeMetadata,
    incoming: CertificateTheoremGraphNodeMetadata,
) {
    existing.usage_count = match (existing.usage_count, incoming.usage_count) {
        (Some(left), Some(right)) => Some(left.saturating_add(right)),
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    };
    for tag in incoming.domain_tags {
        if !existing.domain_tags.contains(&tag) {
            existing.domain_tags.push(tag);
        }
    }
    existing.domain_tags.sort();
}

fn local_decl_node_id(
    cert: &ModuleCert,
    decl_index: usize,
) -> Result<CertificateTheoremGraphNodeId, CertificateTheoremGraphError> {
    let decl = cert
        .declarations
        .get(decl_index)
        .ok_or(CertificateTheoremGraphError::MissingDeclaration { decl_index })?;
    Ok(CertificateTheoremGraphNodeId {
        scope: CertificateTheoremGraphNodeScope::Local,
        module: cert.header.module.clone(),
        name: decl_payload_name(cert, &decl.decl)?,
        decl_interface_hash: decl.hashes.decl_interface_hash,
    })
}

fn decl_payload_name(
    cert: &ModuleCert,
    decl: &DeclPayload,
) -> Result<Name, CertificateTheoremGraphError> {
    name(cert, decl_payload_name_id(decl))
}

fn decl_payload_name_id(decl: &DeclPayload) -> NameId {
    match decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn decl_payload_node_kind(decl: &DeclPayload) -> CertificateTheoremGraphNodeKind {
    match decl {
        DeclPayload::Axiom { .. } | DeclPayload::AxiomConstrained { .. } => {
            CertificateTheoremGraphNodeKind::Axiom
        }
        DeclPayload::Def { .. } | DeclPayload::DefConstrained { .. } => {
            CertificateTheoremGraphNodeKind::Definition
        }
        DeclPayload::Theorem { .. } | DeclPayload::TheoremConstrained { .. } => {
            CertificateTheoremGraphNodeKind::Theorem
        }
        DeclPayload::Inductive { .. }
        | DeclPayload::InductiveConstrained { .. }
        | DeclPayload::MutualInductiveBlock { .. } => CertificateTheoremGraphNodeKind::Inductive,
    }
}

fn export_kind_to_node_kind(kind: ExportKind) -> CertificateTheoremGraphNodeKind {
    match kind {
        ExportKind::Axiom => CertificateTheoremGraphNodeKind::Axiom,
        ExportKind::Def => CertificateTheoremGraphNodeKind::Definition,
        ExportKind::Theorem => CertificateTheoremGraphNodeKind::Theorem,
        ExportKind::Inductive => CertificateTheoremGraphNodeKind::Inductive,
        ExportKind::Constructor => CertificateTheoremGraphNodeKind::Constructor,
        ExportKind::Recursor => CertificateTheoremGraphNodeKind::Recursor,
    }
}

fn name(cert: &ModuleCert, name_id: NameId) -> Result<Name, CertificateTheoremGraphError> {
    cert.name_table
        .get(name_id)
        .cloned()
        .ok_or(CertificateTheoremGraphError::MissingName { name_id })
}

fn term(cert: &ModuleCert, term_id: TermId) -> Result<&TermNode, CertificateTheoremGraphError> {
    cert.term_table
        .get(term_id)
        .ok_or(CertificateTheoremGraphError::MissingTerm { term_id })
}

fn encode_node(out: &mut Vec<u8>, node: &CertificateTheoremGraphNode) {
    encode_node_id(out, &node.id);
    out.push(node_kind_tag(node.kind));
    encode_optional_hash(out, node.type_hash);
    encode_optional_hash(out, node.proof_hash);
    encode_optional_hash(out, node.body_hash);
    encode_node_metadata(out, &node.metadata);
}

fn encode_node_id(out: &mut Vec<u8>, id: &CertificateTheoremGraphNodeId) {
    encode_node_scope(out, &id.scope);
    encode_name(out, &id.module);
    encode_name(out, &id.name);
    out.extend(id.decl_interface_hash);
}

fn encode_node_scope(out: &mut Vec<u8>, scope: &CertificateTheoremGraphNodeScope) {
    match scope {
        CertificateTheoremGraphNodeScope::Builtin => out.push(0),
        CertificateTheoremGraphNodeScope::Imported {
            import_export_hash,
            import_certificate_hash,
        } => {
            out.push(1);
            out.extend(import_export_hash);
            encode_optional_hash(out, *import_certificate_hash);
        }
        CertificateTheoremGraphNodeScope::Local => out.push(2),
        CertificateTheoremGraphNodeScope::LocalGenerated { source_decl_index } => {
            out.push(3);
            encode_uvar(out, *source_decl_index as u64);
        }
    }
}

fn encode_name(out: &mut Vec<u8>, name: &Name) {
    encode_uvar(out, name.0.len() as u64);
    for component in &name.0 {
        encode_bytes(out, component.as_bytes());
    }
}

fn encode_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    encode_uvar(out, bytes.len() as u64);
    out.extend(bytes);
}

fn encode_optional_hash(out: &mut Vec<u8>, hash: Option<Hash>) {
    match hash {
        Some(hash) => {
            out.push(1);
            out.extend(hash);
        }
        None => out.push(0),
    }
}

fn encode_node_metadata(out: &mut Vec<u8>, metadata: &CertificateTheoremGraphNodeMetadata) {
    encode_optional_u64(out, metadata.usage_count);
    encode_uvar(out, metadata.domain_tags.len() as u64);
    for tag in &metadata.domain_tags {
        encode_bytes(out, tag.as_bytes());
    }
}

fn encode_optional_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            out.push(1);
            encode_uvar(out, value);
        }
        None => out.push(0),
    }
}

fn encode_uvar(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn node_kind_tag(kind: CertificateTheoremGraphNodeKind) -> u8 {
    match kind {
        CertificateTheoremGraphNodeKind::Axiom => 0,
        CertificateTheoremGraphNodeKind::Definition => 1,
        CertificateTheoremGraphNodeKind::Theorem => 2,
        CertificateTheoremGraphNodeKind::Inductive => 3,
        CertificateTheoremGraphNodeKind::Constructor => 4,
        CertificateTheoremGraphNodeKind::Recursor => 5,
        CertificateTheoremGraphNodeKind::Builtin => 6,
        CertificateTheoremGraphNodeKind::Unknown => 7,
    }
}

fn extractor_version_tag(version: CertificateTheoremGraphExtractorVersion) -> u8 {
    match version {
        CertificateTheoremGraphExtractorVersion::CertificateGraphV1 => 0,
    }
}

fn edge_kind_tag(kind: CertificateTheoremGraphEdgeKind) -> u8 {
    match kind {
        CertificateTheoremGraphEdgeKind::ImportsDeclaration => 0,
        CertificateTheoremGraphEdgeKind::MentionsType => 1,
        CertificateTheoremGraphEdgeKind::UsesConstant => 2,
        CertificateTheoremGraphEdgeKind::GeneratedDeclaration => 3,
        CertificateTheoremGraphEdgeKind::DependsOnDirectAxiom => 4,
        CertificateTheoremGraphEdgeKind::DependsOnTransitiveAxiom => 5,
        CertificateTheoremGraphEdgeKind::UsedBy => 6,
        CertificateTheoremGraphEdgeKind::SimilarStatement => 7,
        CertificateTheoremGraphEdgeKind::AxiomPath => 8,
    }
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update([0]);
    hasher.update(payload);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_cert::{
        build_module_cert, encode_module_cert, verify_module_cert, AxiomPolicy, CoreModule,
        VerifierSession,
    };
    use npa_kernel::{nat_inductive, Decl, Expr, Level, Reducibility};

    struct FixtureModule {
        verified: VerifiedModule,
        bytes: Vec<u8>,
    }

    fn fixture_module(module: CoreModule, imports: &[VerifiedModule]) -> FixtureModule {
        let cert = build_module_cert(module, imports).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let mut session = VerifierSession::new();
        for import in imports {
            session.register_verified_module(import.clone());
        }
        let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        FixtureModule { verified, bytes }
    }

    fn p() -> Expr {
        Expr::konst("Base.P", vec![])
    }

    fn id_p_type() -> Expr {
        Expr::pi("h", p(), p())
    }

    fn id_p_proof() -> Expr {
        Expr::lam("h", p(), Expr::bvar(0))
    }

    fn base_fixture() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Base"),
                declarations: vec![Decl::Axiom {
                    name: "Base.P".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
    }

    fn unused_fixture() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Unused"),
                declarations: vec![Decl::Axiom {
                    name: "Unused.R".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
    }

    fn alternate_base_fixture() -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Base"),
                declarations: vec![Decl::Axiom {
                    name: "Base.Q".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
    }

    fn client_fixture(base: &VerifiedModule) -> FixtureModule {
        client_fixture_with_imports(std::slice::from_ref(base))
    }

    fn client_fixture_with_imports(imports: &[VerifiedModule]) -> FixtureModule {
        fixture_module(
            CoreModule {
                name: Name::from_dotted("Client"),
                declarations: vec![
                    Decl::Def {
                        name: "Client.idP".to_owned(),
                        universe_params: Vec::new(),
                        ty: id_p_type(),
                        value: id_p_proof(),
                        reducibility: Reducibility::Reducible,
                    },
                    Decl::Theorem {
                        name: "Client.thmP".to_owned(),
                        universe_params: Vec::new(),
                        ty: id_p_type(),
                        proof: id_p_proof(),
                    },
                    Decl::Inductive {
                        name: "Nat".to_owned(),
                        universe_params: Vec::new(),
                        ty: Expr::sort(Level::succ(Level::zero())),
                        data: Box::new(nat_inductive()),
                    },
                ],
            },
            imports,
        )
    }

    fn node_id_by_name(
        snapshot: &CertificateTheoremGraphSnapshot,
        name: &str,
    ) -> CertificateTheoremGraphNodeId {
        snapshot
            .nodes
            .iter()
            .find(|node| node.id.name.as_dotted() == name)
            .map(|node| node.id.clone())
            .unwrap_or_else(|| panic!("missing node {name}"))
    }

    fn test_hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn graph_contract_fixture() -> (
        CertificateTheoremGraphSnapshot,
        Vec<CertificateTheoremGraphVerifiedIdentity>,
    ) {
        let base = base_fixture();
        let client = client_fixture(&base.verified);
        let mut snapshot = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::high_trust_certificate_hash_bound(),
        )
        .unwrap();
        let theorem = node_id_by_name(&snapshot, "Client.thmP");
        let def = node_id_by_name(&snapshot, "Client.idP");
        let imported_axiom = node_id_by_name(&snapshot, "Base.P");
        snapshot.edges.push(CertificateTheoremGraphEdge {
            from: def.clone(),
            to: theorem.clone(),
            kind: CertificateTheoremGraphEdgeKind::UsedBy,
        });
        snapshot.edges.push(CertificateTheoremGraphEdge {
            from: theorem.clone(),
            to: def,
            kind: CertificateTheoremGraphEdgeKind::SimilarStatement,
        });
        snapshot.edges.push(CertificateTheoremGraphEdge {
            from: theorem.clone(),
            to: imported_axiom,
            kind: CertificateTheoremGraphEdgeKind::AxiomPath,
        });
        let theorem_node = snapshot
            .nodes
            .iter_mut()
            .find(|node| node.id == theorem)
            .unwrap();
        theorem_node.metadata.usage_count = Some(12);
        theorem_node.metadata.domain_tags = vec!["logic".to_owned(), "nat:basic".to_owned()];
        snapshot.graph_hash = certificate_theorem_graph_snapshot_hash(&snapshot);
        let identities = certificate_theorem_graph_verified_identities(&snapshot).unwrap();
        (snapshot, identities)
    }

    #[test]
    fn theorem_graph_snapshot_sidecar_validates_inline_artifact_and_no_graph_profile() {
        let (snapshot, identities) = graph_contract_fixture();
        let options = CertificateTheoremGraphSnapshotValidationOptions {
            verified_identities: &identities,
            require_verified_identities: true,
        };

        let inline = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            options,
        )
        .unwrap()
        .unwrap();
        assert_eq!(inline.graph_snapshot_hash, snapshot.graph_hash);
        assert_eq!(inline.verified_identities, identities);

        let canonical_bytes = certificate_theorem_graph_snapshot_canonical_bytes(&snapshot);
        let artifact = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Artifact {
                snapshot: &snapshot,
                canonical_bytes: &canonical_bytes,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            options,
        )
        .unwrap()
        .unwrap();
        assert_eq!(artifact, inline);

        let absent = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Absent,
            options,
        )
        .unwrap();
        assert_eq!(absent, None);

        let features = CertificateTheoremGraphQueryFeatures {
            environment_hash: test_hash(1),
            goal_fingerprint: test_hash(2),
            local_context_hash: test_hash(3),
            query_profile_hash: test_hash(4),
            theorem_index_fingerprint: test_hash(5),
            graph_snapshot_hash: Some(snapshot.graph_hash),
        };
        let feature_hash = certificate_theorem_graph_query_features_hash(&features);
        assert_eq!(
            validate_certificate_theorem_graph_query_features_sidecar(
                CertificateTheoremGraphQueryFeaturesSidecar::Inline {
                    features: &features,
                    query_features_hash: feature_hash,
                },
            )
            .unwrap(),
            feature_hash
        );

        let feature_bytes = certificate_theorem_graph_query_features_canonical_bytes(&features);
        assert_eq!(
            validate_certificate_theorem_graph_query_features_sidecar(
                CertificateTheoremGraphQueryFeaturesSidecar::Artifact {
                    features: &features,
                    canonical_bytes: &feature_bytes,
                    query_features_hash: feature_hash,
                },
            )
            .unwrap(),
            feature_hash
        );

        let no_graph_features = CertificateTheoremGraphQueryFeatures {
            graph_snapshot_hash: None,
            ..features
        };
        let no_graph_hash = certificate_theorem_graph_query_features_hash(&no_graph_features);
        assert_eq!(
            validate_certificate_theorem_graph_query_features_sidecar(
                CertificateTheoremGraphQueryFeaturesSidecar::Inline {
                    features: &no_graph_features,
                    query_features_hash: no_graph_hash,
                },
            )
            .unwrap(),
            no_graph_hash
        );
    }

    #[test]
    fn theorem_graph_snapshot_rejects_stale_graph_and_query_feature_hashes() {
        let (snapshot, identities) = graph_contract_fixture();
        let options = CertificateTheoremGraphSnapshotValidationOptions {
            verified_identities: &identities,
            require_verified_identities: true,
        };
        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: test_hash(99),
            },
            options,
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::GraphSnapshotHashMismatch { .. }
        ));

        let mut stale_bytes = certificate_theorem_graph_snapshot_canonical_bytes(&snapshot);
        stale_bytes.push(0);
        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Artifact {
                snapshot: &snapshot,
                canonical_bytes: &stale_bytes,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            options,
        )
        .unwrap_err();
        assert_eq!(
            err,
            CertificateTheoremGraphError::GraphSnapshotBytesMismatch
        );

        let features = CertificateTheoremGraphQueryFeatures {
            environment_hash: test_hash(1),
            goal_fingerprint: test_hash(2),
            local_context_hash: test_hash(3),
            query_profile_hash: test_hash(4),
            theorem_index_fingerprint: test_hash(5),
            graph_snapshot_hash: Some(snapshot.graph_hash),
        };
        let err = validate_certificate_theorem_graph_query_features_sidecar(
            CertificateTheoremGraphQueryFeaturesSidecar::Inline {
                features: &features,
                query_features_hash: test_hash(88),
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::QueryFeaturesHashMismatch { .. }
        ));
    }

    #[test]
    fn theorem_graph_snapshot_rejects_same_name_different_theorem_identity() {
        let (mut snapshot, identities) = graph_contract_fixture();
        let node = snapshot
            .nodes
            .iter_mut()
            .find(|node| node.id.name.as_dotted() == "Base.P")
            .unwrap();
        node.type_hash = Some(test_hash(77));
        snapshot.graph_hash = certificate_theorem_graph_snapshot_hash(&snapshot);

        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            CertificateTheoremGraphSnapshotValidationOptions {
                verified_identities: &identities,
                require_verified_identities: true,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::VerifiedIdentityMismatch { .. }
        ));
    }

    #[test]
    fn theorem_graph_snapshot_rejects_missing_identity_and_unverified_candidate_node() {
        let (snapshot, identities) = graph_contract_fixture();
        let identities_without_base = identities
            .iter()
            .filter(|identity| identity.name.as_dotted() != "Base.P")
            .cloned()
            .collect::<Vec<_>>();
        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            CertificateTheoremGraphSnapshotValidationOptions {
                verified_identities: &identities_without_base,
                require_verified_identities: true,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::MissingVerifiedIdentity { .. }
        ));

        let mut snapshot = snapshot;
        let mut candidate_id = node_id_by_name(&snapshot, "Client.thmP");
        candidate_id.name = Name::from_dotted("Client.unverifiedCandidate");
        candidate_id.decl_interface_hash = test_hash(71);
        snapshot.nodes.push(CertificateTheoremGraphNode {
            id: candidate_id,
            kind: CertificateTheoremGraphNodeKind::Theorem,
            type_hash: None,
            proof_hash: None,
            body_hash: None,
            metadata: CertificateTheoremGraphNodeMetadata::default(),
        });
        snapshot.graph_hash = certificate_theorem_graph_snapshot_hash(&snapshot);

        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            CertificateTheoremGraphSnapshotValidationOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::UnverifiedCandidateNode { .. }
        ));
    }

    #[test]
    fn theorem_graph_snapshot_rejects_malformed_edge_references() {
        let (mut snapshot, identities) = graph_contract_fixture();
        let from = node_id_by_name(&snapshot, "Client.thmP");
        let mut missing = from.clone();
        missing.name = Name::from_dotted("Client.missing");
        missing.decl_interface_hash = test_hash(72);
        snapshot.edges.push(CertificateTheoremGraphEdge {
            from,
            to: missing,
            kind: CertificateTheoremGraphEdgeKind::SimilarStatement,
        });
        snapshot.graph_hash = certificate_theorem_graph_snapshot_hash(&snapshot);

        let err = validate_certificate_theorem_graph_snapshot_sidecar(
            CertificateTheoremGraphSnapshotSidecar::Inline {
                snapshot: &snapshot,
                graph_snapshot_hash: snapshot.graph_hash,
            },
            CertificateTheoremGraphSnapshotValidationOptions {
                verified_identities: &identities,
                require_verified_identities: true,
            },
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::MalformedEdgeReference { .. }
        ));
    }

    #[test]
    fn theorem_graph_extracts_certificate_edges_and_hash_deterministically() {
        let base = base_fixture();
        let client = client_fixture(&base.verified);
        let options = CertificateTheoremGraphOptions::high_trust_certificate_hash_bound();

        let first = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            options,
        )
        .unwrap();
        let second = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            options,
        )
        .unwrap();

        assert_eq!(first.graph_hash, second.graph_hash);
        assert_eq!(
            first.graph_hash,
            certificate_theorem_graph_snapshot_hash(&first)
        );
        assert_eq!(first.imports[0].module, Name::from_dotted("Base"));
        assert_eq!(first.imports[0].export_hash, base.verified.export_hash());
        assert_eq!(
            first.imports[0].certificate_hash,
            Some(base.verified.certificate_hash())
        );

        let theorem = node_id_by_name(&first, "Client.thmP");
        let imported_axiom = node_id_by_name(&first, "Base.P");
        assert!(first
            .direct_axiom_dependencies(&theorem)
            .contains(&imported_axiom));
        assert!(first
            .transitive_axiom_dependencies(&theorem)
            .contains(&imported_axiom));
        assert!(first
            .direct_dependency_targets(&theorem)
            .contains(&imported_axiom));

        let def = first.node(&node_id_by_name(&first, "Client.idP")).unwrap();
        assert!(def.body_hash.is_some());
        assert!(first.edges.iter().any(|edge| {
            edge.from == def.id
                && edge.to == imported_axiom
                && edge.kind == CertificateTheoremGraphEdgeKind::UsesConstant
        }));

        let nat = node_id_by_name(&first, "Nat");
        let nat_zero = node_id_by_name(&first, "Nat.zero");
        let nat_rec = node_id_by_name(&first, "Nat.rec");
        assert!(first.nodes.iter().any(|node| {
            node.id == nat_zero && node.kind == CertificateTheoremGraphNodeKind::Constructor
        }));
        assert!(first.nodes.iter().any(|node| {
            node.id == nat_rec && node.kind == CertificateTheoremGraphNodeKind::Recursor
        }));
        assert!(first.edges.iter().any(|edge| {
            edge.from == nat
                && edge.to == nat_zero
                && edge.kind == CertificateTheoremGraphEdgeKind::GeneratedDeclaration
        }));
        assert!(first.edges.iter().any(|edge| {
            edge.from == nat
                && edge.to == nat_rec
                && edge.kind == CertificateTheoremGraphEdgeKind::GeneratedDeclaration
        }));
        assert!(first.edges.iter().any(|edge| {
            edge.from == nat_rec && edge.kind == CertificateTheoremGraphEdgeKind::MentionsType
        }));
    }

    #[test]
    fn theorem_graph_hash_ignores_source_text_and_human_debug_metadata() {
        let base = base_fixture();
        let client = client_fixture(&base.verified);
        let source_text = "theorem thmP := by intro h; exact h";
        let human_debug_metadata = "pretty names, spans, tactic trace";
        let first = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap();

        let changed_source_text = format!("{source_text}\n-- edited comment");
        let changed_human_debug_metadata = format!("{human_debug_metadata}\nspan:changed");
        let second = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap();

        assert_ne!(source_text, changed_source_text);
        assert_ne!(human_debug_metadata, changed_human_debug_metadata);
        assert_eq!(first.graph_hash, second.graph_hash);
    }

    #[test]
    fn theorem_graph_checks_import_export_and_high_trust_certificate_bindings() {
        let base = base_fixture();
        let alternate = alternate_base_fixture();
        let client = client_fixture(&base.verified);

        let err = extract_certificate_theorem_graph(
            &client.bytes,
            &[alternate.verified],
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::ImportExportHashMismatch { .. }
        ));

        let mut cert = decode_module_cert(&client.bytes).unwrap();
        cert.imports[0].certificate_hash = None;
        let err = extract_certificate_theorem_graph_from_cert(
            &cert,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::high_trust_certificate_hash_bound(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::ImportCertificateHashMissing { .. }
        ));

        let mut cert = decode_module_cert(&client.bytes).unwrap();
        cert.declarations[0].dependencies[0].decl_interface_hash = [7; 32];
        let err = extract_certificate_theorem_graph_from_cert(
            &cert,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            CertificateTheoremGraphError::DeclInterfaceHashMismatch { .. }
        ));
    }

    #[test]
    fn theorem_graph_dependencies_related_and_query_are_deterministic_public_exports() {
        let base = base_fixture();
        let client = client_fixture(&base.verified);
        let snapshot = extract_certificate_theorem_graph(
            &client.bytes,
            std::slice::from_ref(&base.verified),
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap();

        let direct_request = CertificateTheoremGraphDependenciesRequest {
            declaration: Name::from_dotted("Client.thmP"),
            mode: CertificateTheoremGraphDependenciesMode::Direct,
        };
        let direct = certificate_theorem_graph_dependencies(&snapshot, &direct_request).unwrap();
        let direct_again =
            certificate_theorem_graph_dependencies(&snapshot, &direct_request).unwrap();
        assert_eq!(direct, direct_again);

        let base_p = node_id_by_name(&snapshot, "Base.P");
        assert!(direct.dependencies.contains(&base_p));
        assert_eq!(direct.axioms_used, vec![base_p.clone()]);
        assert!(direct.dependencies.iter().all(|node_id| {
            snapshot
                .node(node_id)
                .is_some_and(certificate_theorem_graph_node_is_certificate_bound_public_export)
        }));

        let transitive_request = CertificateTheoremGraphDependenciesRequest {
            declaration: Name::from_dotted("Client.thmP"),
            mode: CertificateTheoremGraphDependenciesMode::Transitive,
        };
        let transitive =
            certificate_theorem_graph_dependencies(&snapshot, &transitive_request).unwrap();
        assert!(transitive.dependencies.contains(&base_p));
        assert_eq!(transitive.axioms_used, vec![base_p]);

        let related_request = CertificateTheoremGraphRelatedRequest {
            declaration: Name::from_dotted("Client.thmP"),
            limit: 8,
        };
        let related = certificate_theorem_graph_related(&snapshot, &related_request).unwrap();
        let related_again = certificate_theorem_graph_related(&snapshot, &related_request).unwrap();
        assert_eq!(related, related_again);
        assert!(related
            .related
            .iter()
            .any(|entry| entry.node.name.as_dotted() == "Client.idP"));
        assert!(related.related.iter().all(|entry| {
            snapshot
                .node(&entry.node)
                .is_some_and(certificate_theorem_graph_node_is_certificate_bound_public_export)
        }));

        let rooted_query = certificate_theorem_graph_query(
            &snapshot,
            &CertificateTheoremGraphQueryRequest {
                roots: vec![Name::from_dotted("Client.thmP")],
                limit: 16,
            },
        )
        .unwrap();
        let rooted_query_again = certificate_theorem_graph_query(
            &snapshot,
            &CertificateTheoremGraphQueryRequest {
                roots: vec![Name::from_dotted("Client.thmP")],
                limit: 16,
            },
        )
        .unwrap();
        assert_eq!(rooted_query, rooted_query_again);
        assert!(rooted_query
            .nodes
            .iter()
            .any(|entry| entry.node.name.as_dotted() == "Client.thmP"));
        assert!(rooted_query.nodes.iter().all(|entry| {
            snapshot
                .node(&entry.node)
                .is_some_and(certificate_theorem_graph_node_is_certificate_bound_public_export)
        }));

        let all_public = certificate_theorem_graph_query(
            &snapshot,
            &CertificateTheoremGraphQueryRequest {
                roots: Vec::new(),
                limit: 128,
            },
        )
        .unwrap();
        assert!(!all_public.nodes.is_empty());
        assert!(!all_public.nodes.iter().any(|entry| {
            matches!(entry.node.scope, CertificateTheoremGraphNodeScope::Builtin)
                || snapshot
                    .node(&entry.node)
                    .is_some_and(|node| node.kind == CertificateTheoremGraphNodeKind::Unknown)
        }));
    }

    #[test]
    fn theorem_graph_unused_imports_proposes_prune_candidates_from_kept_declarations() {
        let base = base_fixture();
        let unused = unused_fixture();
        let imports = vec![base.verified.clone(), unused.verified.clone()];
        let client = client_fixture_with_imports(&imports);
        let snapshot = extract_certificate_theorem_graph(
            &client.bytes,
            &imports,
            CertificateTheoremGraphOptions::default(),
        )
        .unwrap();

        let response = certificate_theorem_graph_unused_imports(
            &snapshot,
            &CertificateTheoremGraphUnusedImportsRequest {
                kept_declarations: vec![Name::from_dotted("Client.thmP")],
            },
        )
        .unwrap();

        assert!(response
            .candidates
            .iter()
            .any(|candidate| candidate.module == Name::from_dotted("Unused")));
        assert!(!response
            .candidates
            .iter()
            .any(|candidate| candidate.module == Name::from_dotted("Base")));
        assert!(response.candidates.iter().all(|candidate| {
            candidate.reason
                == CertificateTheoremGraphImportPruneReason::NotReferencedByKeptDeclarations
        }));
    }
}
