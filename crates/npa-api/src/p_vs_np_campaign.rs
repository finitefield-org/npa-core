use crate::json::{JsonDocument, JsonValue};
use crate::types::format_hash_string;
use crate::{
    parse_barrier_audit_record, parse_claim_publication_gate_record, parse_research_dag,
    parse_research_target, parse_route_package_record, validate_barrier_audit_record,
    validate_claim_publication_gate_record, validate_research_dag, validate_research_target,
    validate_route_package_record, ClaimPublicationGateValidationErrorKind,
    ResearchDagArtifactKind, ResearchDagNodeKind, ResearchTargetState, RoutePackageTheoremStatus,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

const CAMPAIGN_FIXTURE_API_VERSION: &str = "npa.p-vs-np-campaign-fixture.v1";
const CAMPAIGN_FIXTURE_PATH: &str =
    "testdata/proof-using-agents/fixtures/pua-m16-campaign/p-vs-np-campaign-fixture.json";
const CAMPAIGN_NEGATIVE_FIXTURE_PATH: &str =
    "testdata/proof-using-agents/fixtures/pua-m16-campaign/top-level-resolution-without-prerequisites.json";

#[test]
fn p_vs_np_campaign_fixture() {
    let campaign = read_json_fixture(CAMPAIGN_FIXTURE_PATH);
    let root = object_map(campaign.root());
    assert_eq!(
        string_field(&root, "api_version"),
        CAMPAIGN_FIXTURE_API_VERSION
    );
    assert_eq!(string_field(&root, "fixture_kind"), "campaign_fixture");
    assert!(bool_field(
        &root,
        "top_level_target_remains_research_record"
    ));
    assert!(bool_field(
        &root,
        "useful_progress_without_final_resolution"
    ));
    assert!(!bool_field(&root, "creates_verified_artifacts"));
    assert!(!bool_field(&root, "releases_dependencies"));
    assert!(!bool_field(&root, "claims_p_equals_np_resolved"));
    assert!(!bool_field(&root, "claims_p_not_equals_np_resolved"));

    let target_candidates =
        validate_target_registrations(array_field(&root, "target_registrations"));
    validate_formalization_candidates(
        array_field(&root, "formalization_candidates"),
        &target_candidates,
    );
    validate_known_results(array_field(&root, "known_results"));
    validate_research_dag_ref(object_field(&root, "research_dag"));
    validate_route_package_ref(object_field(&root, "route_package"));
    validate_counterexample_first_checks(array_field(&root, "counterexample_first_checks"));
    validate_variants(array_field(&root, "variants"));
    validate_experiment_proof_separation(object_field(&root, "experiment_proof_separation"));
    validate_notebook_entries(array_field(&root, "notebook_entries"));
    validate_route_package_tasks(array_field(&root, "route_package_tasks"));
    validate_complexity_obligation_audit(object_field(&root, "complexity_obligation_audit"));
    validate_barrier_audit_refs(array_field(&root, "barrier_audits"));
    validate_route_review_ref(object_field(&root, "route_review"));
    validate_claim_gate_rejection_ref(object_field(&root, "claim_gate_rejection"));
    validate_authoring_commands(array_field(&root, "authoring_commands"));
    validate_proof_corpus_modules(array_field(&root, "proof_corpus_modules"));
    validate_negative_resolution_fixture();
}

fn validate_target_registrations(
    values: &[JsonValue<'_>],
) -> BTreeMap<String, BTreeSet<(String, String)>> {
    let mut target_keys = BTreeSet::new();
    let mut target_candidates = BTreeMap::new();
    for value in values {
        let target = object_map(value);
        let target_key = string_field(&target, "target_key");
        target_keys.insert(target_key.to_owned());
        assert!(bool_field(&target, "no_theorem_declaration"));
        assert!(!bool_field(&target, "creates_top_level_resolution_claim"));
        assert_linked_file_hash(&target, "artifact_path", "artifact_hash");

        let target_record_source = read_repo_file(&target_key_path(&target));
        let target_record = parse_research_target(&target_record_source)
            .expect("campaign target record should parse");
        validate_research_target(&target_record).expect("campaign target record should validate");
        assert_eq!(target_record.target_key, target_key);
        assert_eq!(
            target_record.target_state.wire(),
            string_field(&target, "target_state")
        );
        assert!(!matches!(
            target_record.target_state,
            ResearchTargetState::Resolved | ResearchTargetState::Refuted
        ));
        assert!(target_record
            .formalization_candidates
            .iter()
            .all(|candidate| candidate.no_theorem_declaration
                && candidate.proof_corpus_theorem_declaration.is_none()));
        let candidate_pairs = target_record
            .formalization_candidates
            .iter()
            .map(|candidate| {
                (
                    format_hash_string(&candidate.candidate_hash),
                    format_hash_string(&candidate.statement_hash),
                )
            })
            .collect::<BTreeSet<_>>();
        assert!(
            candidate_pairs.iter().any(|(candidate_hash, _)| {
                candidate_hash == string_field(&target, "formalization_candidate_hash")
            }),
            "target registration {target_key} references an unknown formalization candidate"
        );
        assert!(
            target_candidates
                .insert(target_key.to_owned(), candidate_pairs)
                .is_none(),
            "duplicate target registration {target_key}"
        );
    }

    assert_eq!(
        target_keys,
        BTreeSet::from(["PEqualsNP".to_owned(), "PNotEqualsNP".to_owned()])
    );
    target_candidates
}

fn validate_formalization_candidates(
    values: &[JsonValue<'_>],
    target_candidates: &BTreeMap<String, BTreeSet<(String, String)>>,
) {
    let mut target_keys = BTreeSet::new();
    for value in values {
        let candidate = object_map(value);
        let target_key = string_field(&candidate, "target_key");
        let candidate_hash = string_field(&candidate, "candidate_hash");
        let statement_hash = string_field(&candidate, "statement_hash");
        target_keys.insert(target_key.to_owned());
        assert_eq!(string_field(&candidate, "review_status"), "reviewed_exact");
        assert!(bool_field(&candidate, "no_theorem_declaration"));
        let linked_candidates = target_candidates
            .get(target_key)
            .unwrap_or_else(|| panic!("unknown target key {target_key}"));
        assert!(
            linked_candidates.contains(&(candidate_hash.to_owned(), statement_hash.to_owned())),
            "campaign formalization candidate for {target_key} is not in linked target record"
        );
    }
    assert_eq!(
        target_keys,
        BTreeSet::from(["PEqualsNP".to_owned(), "PNotEqualsNP".to_owned()])
    );
}

fn validate_known_results(values: &[JsonValue<'_>]) {
    let mut relationships = BTreeSet::new();
    let mut modules = BTreeSet::new();
    for value in values {
        let result = object_map(value);
        relationships.insert(string_field(&result, "relationship").to_owned());
        modules.insert(string_field(&result, "module_name").to_owned());
    }
    assert!(relationships.contains("completed_foundation"));
    assert!(relationships.contains("conditional_assumption"));
    assert!(relationships.contains("finite_or_special_case"));
    for module in [
        "Proofs.Ai.Complexity.CookLevin",
        "Proofs.Ai.Complexity.Sat",
        "Proofs.Ai.Complexity.PPoly",
        "Proofs.Ai.Complexity.AC0",
    ] {
        assert!(
            modules.contains(module),
            "missing known-result module {module}"
        );
    }
}

fn validate_research_dag_ref(value: &JsonValue<'_>) {
    let dag_ref = object_map(value);
    assert_linked_file_hash(&dag_ref, "artifact_path", "artifact_hash");
    assert!(bool_field(&dag_ref, "separates_experiments"));
    assert!(bool_field(&dag_ref, "separates_conditional_claims"));
    assert!(bool_field(&dag_ref, "separates_blockers"));
    assert!(bool_field(&dag_ref, "separates_verified_theorem_artifacts"));

    let dag_source = read_repo_file(string_field(&dag_ref, "artifact_path"));
    let dag = parse_research_dag(&dag_source).expect("campaign research DAG should parse");
    validate_research_dag(&dag).expect("campaign research DAG should validate");

    let node_kinds = dag
        .nodes
        .iter()
        .map(|node| node.node_kind)
        .collect::<BTreeSet<_>>();
    for kind in [
        ResearchDagNodeKind::ComputationalExperiment,
        ResearchDagNodeKind::ConditionalLemma,
        ResearchDagNodeKind::OpenBlocker,
        ResearchDagNodeKind::BarrierResult,
        ResearchDagNodeKind::CounterexampleSearch,
    ] {
        assert!(node_kinds.contains(&kind), "research DAG missing {kind:?}");
    }
    assert!(dag.artifact_references.iter().any(
        |artifact| artifact.artifact_kind == ResearchDagArtifactKind::VerifiedArtifactIdentity
    ));
    assert!(dag.nodes.iter().all(|node| !node.creates_verified_artifact));
    assert!(dag
        .nodes
        .iter()
        .all(|node| !node.upgrades_verified_artifact));
}

fn validate_route_package_ref(value: &JsonValue<'_>) {
    let route_ref = object_map(value);
    assert_linked_file_hash(&route_ref, "artifact_path", "artifact_hash");
    assert!(bool_field(&route_ref, "final_targets_are_research_records"));
    assert!(!bool_field(&route_ref, "creates_top_level_claim"));

    let package_source = read_repo_file(string_field(&route_ref, "artifact_path"));
    let package =
        parse_route_package_record(&package_source).expect("campaign route package should parse");
    validate_route_package_record(&package).expect("campaign route package should validate");

    assert!(package
        .final_question_targets
        .iter()
        .all(|target| target.no_theorem_declaration
            && target.proof_corpus_theorem_declaration.is_none()));
    assert!(package
        .theorem_cards
        .iter()
        .all(|card| !card.creates_top_level_claim));
    assert!(package
        .theorem_cards
        .iter()
        .any(|card| card.status == RoutePackageTheoremStatus::Conditional));
    assert!(package
        .theorem_cards
        .iter()
        .any(|card| card.status == RoutePackageTheoremStatus::Blocker));
    assert!(!package.creates_top_level_open_problem_claim);
    assert!(!package.creates_verified_artifacts);
    assert!(!package.releases_dependencies);
}

fn validate_counterexample_first_checks(values: &[JsonValue<'_>]) {
    assert!(!values.is_empty());
    for value in values {
        let check = object_map(value);
        assert_eq!(
            string_field(&check, "artifact_kind"),
            "counterexample_report"
        );
        assert!(!bool_field(&check, "proof_claim"));
    }
}

fn validate_variants(values: &[JsonValue<'_>]) {
    let mut relationships = BTreeSet::new();
    for value in values {
        let variant = object_map(value);
        relationships.insert(string_field(&variant, "relationship").to_owned());
        assert!(!bool_field(&variant, "top_level_claim"));
    }
    assert!(relationships.contains("conditional_progress"));
    assert!(relationships.contains("finite_or_special_case"));
}

fn validate_experiment_proof_separation(value: &JsonValue<'_>) {
    let separation = object_map(value);
    for field in [
        "experiment_artifacts_are_proof_evidence",
        "notebook_entries_are_proof_evidence",
        "barrier_audits_are_proof_evidence",
        "route_reviews_are_proof_evidence",
    ] {
        assert!(!bool_field(&separation, field), "{field} must stay false");
    }
}

fn validate_notebook_entries(values: &[JsonValue<'_>]) {
    assert!(!values.is_empty());
    for value in values {
        let entry = object_map(value);
        assert!(!bool_field(&entry, "proof_claim"));
    }
}

fn validate_route_package_tasks(values: &[JsonValue<'_>]) {
    let tasks = string_set(values);
    for task in [
        "layer-a.bitstring-codec-bridge",
        "layer-e.cook-levin-np-hardness",
        "layer-f.3sat-np-complete",
        "layer-i.barrier-audit",
    ] {
        assert!(tasks.contains(task), "missing route package task {task}");
    }
}

fn validate_complexity_obligation_audit(value: &JsonValue<'_>) {
    let audit = object_map(value);
    assert_eq!(string_field(&audit, "status"), "blocked");
    assert!(bool_field(&audit, "blocks_reduction_readiness"));
    assert!(!array_field(&audit, "missing_obligation_hashes").is_empty());
}

fn validate_barrier_audit_refs(values: &[JsonValue<'_>]) {
    assert!(!values.is_empty());
    for value in values {
        let audit_ref = object_map(value);
        assert_linked_file_hash(&audit_ref, "artifact_path", "artifact_hash");
        assert!(!bool_field(&audit_ref, "proof_evidence"));

        let audit_source = read_repo_file(string_field(&audit_ref, "artifact_path"));
        let audit =
            parse_barrier_audit_record(&audit_source).expect("campaign barrier audit should parse");
        validate_barrier_audit_record(&audit).expect("campaign barrier audit should validate");
        assert!(!audit.creates_certificate_evidence);
        assert!(!audit.creates_proof_acceptance);
        assert!(!audit.automatically_refutes_route);
        assert!(!audit.rejects_valid_checked_theorem_without_review);
    }
}

fn validate_route_review_ref(value: &JsonValue<'_>) {
    let route_review = object_map(value);
    assert_linked_file_hash(&route_review, "artifact_path", "artifact_hash");
    assert!(!bool_field(&route_review, "proof_evidence"));
    for field in [
        "names_completed_foundations",
        "names_blockers",
        "names_conditional_assumptions",
        "names_finite_or_special_cases",
        "names_route_specific_modules",
        "names_authoring_commands",
    ] {
        assert!(bool_field(&route_review, field), "{field} must be true");
    }

    let review_text = read_repo_file(string_field(&route_review, "artifact_path"));
    for needle in [
        "P versus NP",
        "PEqualsNP",
        "PNotEqualsNP",
        "route review",
        "claim gate rejection",
        "authoring commands",
    ] {
        assert!(
            review_text.contains(needle),
            "route review missing `{needle}`"
        );
    }
}

fn validate_claim_gate_rejection_ref(value: &JsonValue<'_>) {
    let claim_ref = object_map(value);
    assert_linked_file_hash(&claim_ref, "artifact_path", "artifact_hash");
    assert_eq!(
        string_field(&claim_ref, "expected_rejection"),
        "unresolved_blocker"
    );
    assert!(!bool_field(
        &claim_ref,
        "target_state_transition_authorized"
    ));
    assert_unresolved_blocker_claim_gate(string_field(&claim_ref, "artifact_path"));
}

fn validate_authoring_commands(values: &[JsonValue<'_>]) {
    let commands = string_set(values);
    assert!(commands
        .contains("cargo run -p npa-proof-corpus -- --changed-only --verified-cache authoring"));
    assert!(commands.contains("./scripts/check-corpus-authoring.sh"));
}

fn validate_proof_corpus_modules(values: &[JsonValue<'_>]) {
    let modules = string_set(values);
    for module in [
        "Proofs.Ai.Complexity.Encoding",
        "Proofs.Ai.Complexity.Machine",
        "Proofs.Ai.Complexity.Classes",
        "Proofs.Ai.Complexity.Circuit",
        "Proofs.Ai.Complexity.CookLevin",
        "Proofs.Ai.Complexity.Sat",
        "Proofs.Ai.Complexity.PPoly",
        "Proofs.Ai.Complexity.AC0",
    ] {
        assert!(
            modules.contains(module),
            "missing proof-corpus module {module}"
        );
    }
}

fn validate_negative_resolution_fixture() {
    let negative = read_json_fixture(CAMPAIGN_NEGATIVE_FIXTURE_PATH);
    let root = object_map(negative.root());
    assert_eq!(
        string_field(&root, "api_version"),
        CAMPAIGN_FIXTURE_API_VERSION
    );
    assert_eq!(
        string_field(&root, "fixture_kind"),
        "negative_resolution_attempt"
    );
    assert_eq!(string_field(&root, "claim_class"), "resolution");
    assert_eq!(string_field(&root, "attempted_target_state"), "resolved");
    assert_eq!(
        string_field(&root, "expected_rejection"),
        "unresolved_blocker"
    );
    assert!(!bool_field(&root, "accepted_as_resolution"));
    assert!(!bool_field(&root, "target_state_transition_authorized"));
    assert!(!bool_field(&root, "creates_top_level_theorem_declaration"));
    assert!(!bool_field(&root, "creates_verified_artifacts"));
    assert!(!bool_field(&root, "releases_dependencies"));
    assert_linked_file_hash(&root, "claim_gate_record_path", "claim_gate_record_hash");
    assert_unresolved_blocker_claim_gate(string_field(&root, "claim_gate_record_path"));

    let missing = string_set(array_field(&root, "missing_prerequisites"));
    for prerequisite in [
        "full_resolution_certificate",
        "source_free_reproduction_for_every_prerequisite",
        "independent_checker_confirmation",
        "closed_barrier_review",
        "human_mathematical_review",
    ] {
        assert!(
            missing.contains(prerequisite),
            "negative fixture missing prerequisite {prerequisite}"
        );
    }
}

fn assert_unresolved_blocker_claim_gate(path: &str) {
    let gate_source = read_repo_file(path);
    let gate = parse_claim_publication_gate_record(&gate_source)
        .expect("campaign claim gate record should parse");
    assert!(matches!(
        validate_claim_publication_gate_record(&gate).map_err(|error| error.kind().clone()),
        Err(ClaimPublicationGateValidationErrorKind::UnresolvedBlocker { .. })
    ));
}

fn assert_linked_file_hash(
    object: &BTreeMap<&str, &JsonValue<'_>>,
    path_field: &'static str,
    hash_field: &'static str,
) {
    let path = string_field(object, path_field);
    let expected_hash = string_field(object, hash_field);
    assert_eq!(file_sha256(path), expected_hash);
}

fn target_key_path(target: &BTreeMap<&str, &JsonValue<'_>>) -> String {
    string_field(target, "artifact_path").to_owned()
}

fn read_json_fixture(path: &str) -> JsonDocument<'static> {
    let source = read_repo_file(path);
    let leaked: &'static str = Box::leak(source.into_boxed_str());
    JsonDocument::parse(leaked).unwrap_or_else(|error| {
        panic!(
            "campaign JSON fixture {path} should parse at {}",
            error.offset
        )
    })
}

fn read_repo_file(path: &str) -> String {
    std::fs::read_to_string(repo_path(path))
        .unwrap_or_else(|error| panic!("failed to read {path}: {error}"))
}

fn file_sha256(path: &str) -> String {
    let bytes = std::fs::read(repo_path(path))
        .unwrap_or_else(|error| panic!("failed to read {path}: {error}"));
    let digest = Sha256::digest(bytes);
    let mut out = String::from("sha256:");
    for byte in digest {
        write!(&mut out, "{byte:02x}").expect("writing to string cannot fail");
    }
    out
}

fn repo_path(path: &str) -> PathBuf {
    let root = repo_root();
    let local_path = root.join(path);
    if local_path.exists() {
        return local_path;
    }
    if path.starts_with("develop/") {
        return root.join("../npa-core").join(path);
    }
    local_path
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("npa-api is under crates")
        .parent()
        .expect("crates is under repo root")
        .to_path_buf()
}

fn object_map<'value, 'src>(
    value: &'value JsonValue<'src>,
) -> BTreeMap<&'value str, &'value JsonValue<'src>> {
    let members = value.object_members().expect("expected JSON object");
    let mut out = BTreeMap::new();
    for member in members {
        assert!(
            out.insert(member.key(), member.value()).is_none(),
            "duplicate JSON key {}",
            member.key()
        );
    }
    out
}

fn object_field<'value, 'src>(
    object: &BTreeMap<&str, &'value JsonValue<'src>>,
    field: &'static str,
) -> &'value JsonValue<'src> {
    let value = required_field(object, field);
    assert!(
        value.object_members().is_some(),
        "{field} should be an object"
    );
    value
}

fn array_field<'value, 'src>(
    object: &BTreeMap<&str, &'value JsonValue<'src>>,
    field: &'static str,
) -> &'value [JsonValue<'src>] {
    required_field(object, field)
        .array_elements()
        .unwrap_or_else(|| panic!("{field} should be an array"))
}

fn string_field<'value>(
    object: &BTreeMap<&str, &'value JsonValue<'_>>,
    field: &'static str,
) -> &'value str {
    required_field(object, field)
        .string_value()
        .unwrap_or_else(|| panic!("{field} should be a string"))
}

fn bool_field(object: &BTreeMap<&str, &JsonValue<'_>>, field: &'static str) -> bool {
    required_field(object, field)
        .bool_value()
        .unwrap_or_else(|| panic!("{field} should be a bool"))
}

fn required_field<'value, 'src>(
    object: &BTreeMap<&str, &'value JsonValue<'src>>,
    field: &'static str,
) -> &'value JsonValue<'src> {
    object
        .get(field)
        .copied()
        .unwrap_or_else(|| panic!("missing JSON field {field}"))
}

fn string_set(values: &[JsonValue<'_>]) -> BTreeSet<String> {
    values
        .iter()
        .map(|value| {
            value
                .string_value()
                .unwrap_or_else(|| panic!("expected string array item"))
                .to_owned()
        })
        .collect()
}
