#!/bin/sh
set -eu

# Milestone 1 audit helper. This is intentionally tied to the pre-removal tree.
# Milestone 7 deletes this helper and the raw inventory after carrying the
# reviewed decisions into the implementation and release evidence.

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
evidence_dir="$repo_root/npa-core/docs/let-removal-milestone-1"
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/npa-let-m1-tags.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

# The committed ledger is also the reviewed allowlist for identities whose
# disposition is not one of the explicit let-removal rules below. Preserve it
# before regeneration so a newly discovered identity fails as unclassified
# instead of being silently labeled unrelated.
if [ -f "$evidence_dir/canonical-tag-disposition.tsv" ]; then
  cp "$evidence_dir/canonical-tag-disposition.tsv" "$tmp_dir/reviewed-decisions.tsv"
else
  printf 'identity\tdisposition\ttarget_identity\trationale\n' \
    > "$tmp_dir/reviewed-decisions.tsv"
fi

pattern='(?<=["\x27])(?:NPA-[A-Za-z0-9_.-]*[0-9]|npa[._-][A-Za-z0-9_.-]*[._-]v[0-9][A-Za-z0-9_.-]*|core-spec-v[0-9][A-Za-z0-9_.-]*|beta-delta-iota(?:-zeta)?\.v[0-9][A-Za-z0-9_.-]*|levels-imax-v[0-9][A-Za-z0-9_.-]*|builtin-(?:none|nat-eq-rec)-v[0-9][A-Za-z0-9_.-]*)(?=(?:\\0)?["\x27])'

cd "$repo_root"
rg --pcre2 -n -o --no-heading "$pattern" \
  npa-core/crates \
  npa-core/checkers \
  npa-core/scripts \
  npa-lean-exporter/crates \
  npa-lean-exporter/scripts \
  npa-agents/apps \
  npa-agents/crates \
  npa-agents/scripts \
  npa-web/src \
  tools \
  -g '*.rs' -g '*.ml' -g '*.mli' -g '*.sh' -g '*.ts' -g '*.tsx' -g '*.js' \
  | awk -F: '{ path=$1; line=$2; identity=substr($0, length(path)+length(line)+3); print identity "\t" path "\t" line }' \
  | LC_ALL=C sort -t '	' -k1,1 -k2,2 -k3,3n \
  > "$tmp_dir/occurrences.tsv"

cut -f1 "$tmp_dir/occurrences.tsv" | LC_ALL=C sort -u \
  > "$evidence_dir/canonical-identity-inventory.txt"

classify() {
  identity=$1
  disposition=unclassified
  target=-
  rationale=new_identity_requires_review

  reviewed_row=$(awk -F '\t' -v identity="$identity" '
    NR > 1 && $1 == identity {
      print $2 "\t" $3 "\t" $4
      exit
    }
  ' "$tmp_dir/reviewed-decisions.tsv")
  if [ -n "$reviewed_row" ]; then
    old_ifs=$IFS
    IFS='	'
    set -- $reviewed_row
    IFS=$old_ifs
    if [ "$#" -ne 3 ]; then
      echo "invalid reviewed disposition for $identity" >&2
      exit 1
    fi
    disposition=$1
    target=$2
    rationale=$3
  fi

  case "$identity" in
    NPA-CERT-0.1|NPA-CERT-0.1.2|NPA-CERT-0.2.0|NPA-CERT-0.3.0)
      disposition=bump
      target=NPA-CERT-0.4.0
      rationale=single_current_header_format_old_decoder_removed
      ;;
    NPA-Core-0.1|NPA-Core-0.1.2|NPA-Core-0.2.0|NPA-Core-0.3.0)
      disposition=bump
      target=NPA-Core-0.4.0
      rationale=single_current_header_core_old_decoder_removed
      ;;
    NPA-DECL-CERT-0.1|NPA-DECL-CERT-0.3.0)
      disposition=bump
      target=NPA-DECL-CERT-0.4.0
      rationale=declaration_certificate_semantic_epoch_and_header_pair_change
      ;;
    NPA-MODULE-CERT-0.1|NPA-MODULE-CERT-0.1.2|NPA-MODULE-CERT-0.2.0|NPA-MODULE-CERT-0.3.0)
      disposition=bump
      target=NPA-MODULE-CERT-0.4.0
      rationale=module_certificate_header_and_semantic_epoch_change
      ;;
    NPA-MODULE-EXPORT-0.1|NPA-MODULE-EXPORT-0.1.2)
      disposition=bump
      target=NPA-MODULE-EXPORT-0.2.0
      rationale=old_only_export_domain_removed_with_old_decoder
      ;;
    NPA-FRONTEND-MACHINE-TERM-CONTEXT-0.1)
      disposition=bump
      target=NPA-FRONTEND-MACHINE-TERM-CONTEXT-0.2
      rationale=inline_core_term_grammar_loses_let
      ;;
    NPA-DECLARATION-CLOSURE-PROJECTION-TERM-v1)
      disposition=bump
      target=NPA-DECLARATION-CLOSURE-PROJECTION-TERM-v2
      rationale=inline_projection_term_grammar_loses_tag_6
      ;;
    NPA-DECLARATION-CLOSURE-PROJECTION-v1)
      disposition=bump
      target=NPA-DECLARATION-CLOSURE-PROJECTION-v2
      rationale=embeds_changed_projection_term_hashes_in_canonical_bytes
      ;;
    NPA-L2-TRANSPORT-PROJECTION-v1)
      disposition=bump
      target=NPA-L2-TRANSPORT-PROJECTION-v2
      rationale=inline_transport_term_grammar_loses_tag_6
      ;;
    NPA-L2-TRANSPORT-CLOSURE-v1)
      disposition=bump
      target=NPA-L2-TRANSPORT-CLOSURE-v2
      rationale=hashes_changed_inline_transport_projection_bytes
      ;;
    core-spec-v0.1)
      disposition=bump
      target=core-spec-v0.2
      rationale=machine_kernel_profile_semantics_become_let_free
      ;;
    npa-kernel.core.v0.1)
      disposition=bump
      target=npa-kernel.core.v0.2
      rationale=machine_kernel_semantics_profile_loses_local_definitions_and_zeta
      ;;
    beta-delta-iota-zeta.v0.1)
      disposition=bump
      target=beta-delta-iota.v0.1
      rationale=zeta_removed_no_compatibility_alias
      ;;
    npa.frontend.human_authoring_interface_abi.v1)
      disposition=bump
      target=npa.frontend.human_authoring_interface_abi.v2
      rationale=human_source_grammar_and_local_shape_change
      ;;
    npa.frontend.machine-term-source.v1)
      disposition=bump
      target=npa.frontend.machine-term-source.v2
      rationale=inline_machine_term_ast_loses_let
      ;;
    npa.cert.local_authoring_producer_abi.v1)
      disposition=bump
      target=npa.cert.local_authoring_producer_abi.v2
      rationale=producer_can_no_longer_construct_let_certificates
      ;;
    npa.kernel.local_authoring_context_abi.v1)
      disposition=bump
      target=npa.kernel.local_authoring_context_abi.v2
      rationale=local_context_becomes_assumption_only
      ;;
    npa.machine-tactic.refine-term-source.v1|npa.machine-tactic.refine-term-source.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_refine_term_grammar_loses_let
      ;;
    npa.machine-tactic.machine-term-source.v1|npa.machine-tactic.machine-term-source.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=embedded_frontend_term_source_identity_changes
      ;;
    npa.machine-tactic.proof-expr.v1|npa.machine-tactic.proof-expr.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_proof_expression_grammar_loses_let
      ;;
    npa.machine-tactic.machine-local-decl.v1|npa.machine-tactic.machine-local-decl.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_local_value_field_removed
      ;;
    npa.machine-tactic.machine-local-context.v1|npa.machine-tactic.machine-local-context.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_local_declarations_become_assumption_only
      ;;
    npa.machine-tactic.diagnostic-local-context-summary.v1|npa.machine-tactic.diagnostic-local-context-summary.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=value_hash_and_value_summary_removed
      ;;
    npa.machine-api.api-diagnostic.v1)
      disposition=bump
      target=npa.machine-api.api-diagnostic.v2
      rationale=closed_error_vocabulary_adds_removed_term_let
      ;;
    npa.machine-diagnostic-tree.v1)
      disposition=bump
      target=npa.machine-diagnostic-tree.v2
      rationale=local_value_target_removed_and_removed_term_let_added
      ;;
    npa.failure_memory.v1)
      disposition=bump
      target=npa.failure_memory.v2
      rationale=inline_machine_api_error_vocabulary_changes
      ;;
    npa.failure-memory.key-hash.v1)
      disposition=bump
      target=npa.failure-memory.key-hash.v2
      rationale=hashes_changed_failure_memory_canonical_bytes
      ;;
    npa.hard_negative_export.v1)
      disposition=bump
      target=npa.hard_negative_export.v2
      rationale=inline_machine_api_error_vocabulary_changes
      ;;
    npa.machine-api.hard-negative-export.hash.v1)
      disposition=bump
      target=npa.machine-api.hard-negative-export.hash.v2
      rationale=hashes_changed_hard_negative_canonical_bytes
      ;;
    npa.proof.local-statement-generalization.v1)
      disposition=bump
      target=npa.proof.local-statement-generalization.v2
      rationale=value_hash_and_unfold_local_definitions_removed
      ;;
    npa.proof-skeleton.v1|npa.proof-skeleton.skeleton-hash.v1|npa.proof-skeleton.hole-hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=proof_skeleton_term_and_local_grammar_change
      ;;
    npa.core-expr.canonical-bytes.v0.1|npa.core-expr-artifact.v0.1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v0\.1$/.v0.2/')
      rationale=artifact_parser_schema_must_reject_retired_core_node
      ;;
    npa.machine-tactic.checked-decl-signature.v1|npa.machine-tactic.checked-decl-signature.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_core_expression_semantic_epoch_changes
      ;;
    npa.machine-api.current-core-decl-package.v1)
      disposition=bump
      target=npa.machine-api.current-core-decl-package.v2
      rationale=package_embeds_changed_term_table_bytes
      ;;
    npa.machine-api.current-core-decl-package.term-table.v1)
      disposition=bump
      target=npa.machine-api.current-core-decl-package.term-table.v2
      rationale=inline_term_table_grammar_loses_tag_6
      ;;
    npa.machine-api.checked-current-decl-package.v6)
      disposition=bump
      target=npa.machine-api.checked-current-decl-package.v7
      rationale=checked_package_semantic_epoch_and_embedded_core_change
      ;;
    npa.machine-api.checked-current-decl-package.canonical.v6.hex)
      disposition=bump
      target=npa.machine-api.checked-current-decl-package.canonical.v7.hex
      rationale=json_canonical_encoding_tracks_checked_package_v7
      ;;
    npa.lean.native.v0.2|npa.lean.export.v0.2)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v0\.2$/.v0.3/')
      rationale=exporter_accepts_only_v0_4_let_free_closures
      ;;
    npa.machine-tactic.machine-proof-delta.v1)
      disposition=bump
      target=npa.machine-tactic.machine-proof-delta.v2
      rationale=proof_state_semantic_epoch_changes
      ;;
    npa.machine-tactic.machine-proof-state.v1)
      disposition=bump
      target=npa.machine-tactic.machine-proof-state.v2
      rationale=inline_proof_expr_and_local_context_grammar_changes
      ;;
    npa.machine-tactic.machine-tactic-env.v2)
      disposition=bump
      target=npa.machine-tactic.machine-tactic-env.v3
      rationale=inline_checked_signatures_and_kernel_profile_change
      ;;
    npa.machine-tactic.kernel-check-profile.v1)
      disposition=bump
      target=npa.machine-tactic.kernel-check-profile.v2
      rationale=core_and_reduction_profile_members_change
      ;;
    npa.minimal_failing_artifact.v2)
      disposition=bump
      target=npa.minimal_failing_artifact.v3
      rationale=local_value_hash_removed
      ;;
    npa.machine-api.minimal-failing-artifact.hash.v2)
      disposition=bump
      target=npa.machine-api.minimal-failing-artifact.hash.v3
      rationale=hashes_changed_minimal_artifact_bytes
      ;;
    npa.focused_replay_failure_artifact.v2)
      disposition=bump
      target=npa.focused_replay_failure_artifact.v3
      rationale=embeds_changed_minimal_artifact_bytes_inline
      ;;
    npa.machine-api.focused-replay-failure-artifact.hash.v2)
      disposition=bump
      target=npa.machine-api.focused-replay-failure-artifact.hash.v3
      rationale=hashes_changed_focused_replay_artifact_bytes
      ;;
    npa.library-growth.lemma-generalization-input.v1|npa.library-growth.lemma-generalization-input.hash.v1|npa.library-growth.generalized-statement.v1|npa.library-growth.generalized-statement.hash.v1|npa.library-growth.statement-normalization-report.v1|npa.library-growth.statement-normalization-report.hash.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_local_value_hash_or_generalization_grammar_removed
      ;;
    npa.advanced-ai.candidate.v1|npa.advanced-ai.goal.v1|npa.advanced-ai.validation_result.v1|npa.advanced-ai.smt.problem.v1|npa.advanced-ai.smt.proof_payload.v1|npa.advanced-ai.smt.reconstruction_plan.v1|npa.advanced-ai.smt.command_id.v1|npa.advanced-ai.smt.nat_to_int_side_condition.v1|npa.advanced-ai.formalization.candidate_statement.v1|npa.advanced-ai.formalization.accepted_statement.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=advanced_ai_helper_trace_finds_inline_goal_local_or_expr_bytes
      ;;
    npa.machine-api.v1)
      disposition=bump
      target=npa.machine-api.v2
      rationale=public_protocol_local_shape_and_error_vocabulary_change
      ;;
    npa.machine-api.display.v1|npa.human-api.display.v1|npa.human-ide-api.v1|npa.machine-api.prompt-payload.v1|npa.machine-api.prompt-rendered-content.v1|npa.machine-api.stored-snapshot-view.v1|npa.machine-api.session-checked-current.v1)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/\.v1$/.v2/')
      rationale=inline_local_or_display_shape_becomes_assumption_only
      ;;
    npa.machine-api.session-root.v2)
      disposition=bump
      target=npa.machine-api.session-root.v3
      rationale=session_root_commits_new_protocol_and_context_epoch
      ;;
    npa.kernel-fuel-diagnostic.v0.1)
      disposition=bump
      target=npa.kernel-fuel-diagnostic.v0.2
      rationale=zeta_counter_and_let_head_removed
      ;;
    npa.performance.measurements.v0.8)
      disposition=bump
      target=npa.performance.measurements.v0.9
      rationale=zeta_steps_removed_and_physical_reductions_redefined
      ;;
    npa.package.command_result.v0.4)
      disposition=bump
      target=npa.package.command_result.v0.5
      rationale=current_nested_measurement_and_host_mapping_change
      ;;
    npa.package.theorem_premise_report.v0.1)
      disposition=bump
      target=npa.package.theorem_premise_report.v0.2
      rationale=let_value_use_site_removed_from_closed_vocabulary
      ;;
    npa.package.theorem_premise_report.v0.1.certificate_structural)
      disposition=bump
      target=npa.package.theorem_premise_report.v0.2.certificate_structural
      rationale=structural_report_profile_tracks_v0_2_report_vocabulary
      ;;
    npa.generated_artifact_release_manifest.v0.2)
      disposition=bump
      target=npa.generated_artifact_release_manifest.v0.3
      rationale=current_host_and_nested_schema_mapping_changes
      ;;
    npa.generated_artifact_release_manifest.validation.v0.1)
      disposition=bump
      target=npa.generated_artifact_release_manifest.validation.v0.2
      rationale=validator_rejects_retired_0_7_and_0_8_hosts
      ;;
    npa.checker_ext.toolchain_v0_7.*)
      disposition=bump
      target=removed_without_replacement
      rationale=unused_v0_7_toolchain_identity_deleted
      ;;
    npa.checker_ext.toolchain_v0_8|npa.checker_ext.toolchain_v0_8.*)
      disposition=bump
      target=$(printf '%s' "$identity" | sed 's/toolchain_v0_8/toolchain_v0_9/')
      rationale=temporary_v0_8_lane_replaced_by_single_v0_9_lane
      ;;
    npa-checker-ext-toolchain-v0-8-*|npa-checker-ext-toolchain-v0.8.0-fixture|npa-checker-ref-toolchain-v0-8-fixture|npa-fast-kernel-toolchain-v0-8-fixture|npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat-manifest.json|npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat.sha256|npa-mathlib-downstream-proofs-generated-toolchain-v0.8.0-compat.tar.gz)
      disposition=bump
      target=$(printf '%s' "$identity" | sed -e 's/v0-8/v0-9/g' -e 's/v0\.8\.0/v0.9.0/g')
      rationale=temporary_v0_8_toolchain_fixture_or_asset_name_replaced
      ;;
    npa-checker-ext-v0.7)
      disposition=bump
      target=removed_without_replacement
      rationale=unused_v0_7_toolchain_test_surface_deleted
      ;;
    npa-checker-ext-v0.8)
      disposition=bump
      target=npa-checker-ext-v0.9
      rationale=temporary_v0_8_toolchain_test_surface_replaced
      ;;

    NPA-TERM-0.1|NPA-CORE-EXPR-0.1|NPA-KERNEL-CORE-EXPR-0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=six_surviving_payloads_are_byte_identical_and_current_pair_or_parser_makes_tag_6_unreachable
      ;;
    NPA-DECL-IFACE-0.1|NPA-MODULE-EXPORT-0.2.0|NPA-AXIOM-REPORT-0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_public_layout_commits_current_term_interface_or_module_hash_children
      ;;
    NPA-GEN-REC-SIG-0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_recursor_signature_layout_commits_a_current_six_form_term_hash
      ;;
    NPA-LEVEL-0.1)
      disposition=unrelated
      target=-
      rationale=level_grammar_and_merkle_payload_do_not_encode_terms_local_values_diagnostics_or_zeta
      ;;
    NPA-UNIVERSE-CONSTRAINTS-0.1)
      disposition=unrelated
      target=-
      rationale=universe_parameter_and_level_constraint_payload_does_not_encode_term_or_local_context_shape
      ;;
    NPA-GEN-COMP-RULE-0.1)
      disposition=unrelated
      target=-
      rationale=payload_contains_only_recursor_presence_minor_start_and_major_index
      ;;
    NPA-BUILTIN-INTERFACE-0.1)
      disposition=unrelated
      target=-
      rationale=payload_is_a_fixed_builtin_name_tag_and_has_no_term_or_local_context_shape
      ;;
    NPA-AXIOM-POLICY-CANONICAL-BYTES-0.1|NPA-AXIOM-POLICY-HASH-0.1)
      disposition=unrelated
      target=-
      rationale=axiom_policy_payload_has_no_term_local_context_diagnostic_or_reduction_vocabulary
      ;;
    NPA-DECLARATION-CLOSURE-v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_declaration_and_module_certificate_hashes
      ;;
    NPA-HUMAN-DECLARATION-EXTRACTION-v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_source_projection_is_untrusted_and_reparsed_under_human_authoring_abi_v2
      ;;
    npa.human-api.compile-options.v2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_option_layout_embeds_the_new_kernel_profile_identity
      ;;
    npa.human-api.document-import-interface.v2|npa.human-api.document-source-decl.v2|npa.human-api.document-resolved-decl.v2|npa.human-api.document-core-decl.v2|npa.human-api.document-dependency-selective.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=incremental_document_hash_commits_the_new_pair_interface_hashes_or_v2_parser_boundary
      ;;
    npa.human-api.theorem-index.v1|npa.human-api.theorem-index-entry.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_index_layout_commits_rebuilt_certificate_or_core_child_hashes
      ;;
    npa.advanced-ai.env.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_import_certificate_hashes
      ;;
    npa.advanced-ai.smt.encoding.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_smt_problem_hash
      ;;
    npa.advanced-ai.smt.certificate_metadata.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_problem_proof_and_reconstruction_hashes
      ;;
    npa.advanced-ai.smt.solver_handoff.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_problem_and_encoding_hashes
      ;;
    npa.advanced-ai.formalization.proof_root.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_candidate_and_accepted_statement_hashes
      ;;
    npa.advanced-ai.theorem_graph.query_features.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_goal_fingerprint_hash
      ;;
    npa.advanced-ai.theorem_graph.snapshot.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_certificate_and_declaration_hashes
      ;;
    npa.ai-search.candidate-payload.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=raw_string_grammar_unchanged_and_all_use_reparses_under_machine_api_v2
      ;;
    npa.ai-search.training-trace.v1|npa.ai-search.training-negative-identity.v1|npa.ai-search.training-positive-identity.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=closed_training_vocabulary_unchanged_and_changed_diagnostics_or_candidates_are_hashed_children
      ;;
    npa.ai-search.focused-replay-payload.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_outer_json_commits_new_replay_and_premise_child_identities
      ;;
    npa.proof.local-context-binder-fingerprint.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=contains_only_new_machine_local_declaration_hashes
      ;;
    npa.machine-tactic.machine-tactic.v1|npa.machine-tactic.machine-tactic.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=term_fields_are_new_domain_separated_source_hashes_not_inline_terms
      ;;
    npa.machine-tactic.machine-tactic-cache-key.v1|npa.machine-tactic.machine-tactic-cache-key.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=state_and_tactic_fields_commit_new_child_hashes
      ;;
    npa.machine-tactic.current.checked-env.v2|npa.machine-tactic.current.prior-chain.v2|npa.machine-tactic.current.dependency-selective.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_layout_commits_new_pair_certificate_profile_or_signature_hashes
      ;;
    npa.machine-api.session-import-context.v2|npa.machine-api.session-direct-imports.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_session_subencoding_commits_new_pair_certificate_or_import_summary_hashes
      ;;
    npa.machine-api.current-core-decl-package.name-table.v1|npa.machine-api.current-core-decl-package.level-table.v1|npa.machine-api.current-core-decl-package.root-decl.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=subencoding_byte_grammar_unchanged_and_parent_package_or_term_table_is_bumped
      ;;
    npa.machine-api.stored-expr-view.v1|npa.machine-api.local-name-map.v1|npa.machine-api.goal-fingerprint.v1|npa.machine-api.retrieval-local-context.v1|npa.machine-api.checked-machine-proof-root.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=no_removed_field_and_changed_core_context_or_source_is_a_separated_hash
      ;;
    npa.machine_tactic_candidate.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=raw_json_grammar_unchanged_and_terms_reparse_under_machine_api_v2
      ;;
    npa.frontend.equation.lowered-core-artifact.v0|npa.frontend.equation.lowered-core-bundle.v0)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_artifact_layout_commits_core_expression_or_artifact_hashes
      ;;
    npa.certificate-theorem-graph.v2|npa.certificate-theorem-graph.query-features.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_graph_layout_is_rebuilt_from_v0_4_certificate_hashes
      ;;
    npa.package.timings.v0.2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=outer_timing_envelope_names_new_nested_measurement_schema
      ;;
    npa.package.audit_cache.v0.2|npa.package.audit_process_memo.v0.2|npa.package.audit_disk_memo.v0.2|npa.package.reference_summary_cache.v0.2|npa.package.import_context_export_cache.v0.2|npa.package.build_check_cache.v0.2|npa.package.build_check_cache_namespace.v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_cache_key_layout_commits_the_exact_new_pair_and_rebuilt_certificate_hashes
      ;;
    npa.package.audit_result.v0.2|npa.package.audit_disk_memo_result.v0.2|npa.package.reference_summary_cache_entry.v0.2|npa.package.import_context_export_cache_entry.v0.2|npa.package.build_check_result.v0.2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_untrusted_entry_layout_contains_a_recomputed_current_cache_key
      ;;
    npa.package.verified_export_summary.v0.2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_summary_layout_records_the_exact_new_pair_and_rebuilt_certificate_hashes
      ;;
    npa.package.build_check_tool_identity.v0.2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_tool_identity_layout_commits_the_new_executable_and_authoring_abi_hashes
      ;;
    npa.package.targeted_authoring_support_key.v0.1|npa.package.targeted_authoring_support_context.v0.1|npa.package.targeted_authoring_support_closure.v0.1|npa.package.targeted_authoring_external_leaf.v0.1|npa.package.targeted_authoring_human_interface.v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_targeted_authoring_layout_is_guarded_by_new_pair_abi_tool_and_certificate_hashes
      ;;
    npa.package.theorem_premise_report_chunks.v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=opaque_chunk_envelope_commits_new_report_hash
      ;;
    npa.independent-checker.checker_raw_result.v2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_result_shape_carries_new_checker_capability_and_input_pair
      ;;
    npa.lean.command_result.v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_envelope_commits_new_export_manifest_by_hash_and_path
      ;;
    npa.cli.targeted_authoring_abi.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=aggregate_key_separately_commits_bumped_frontend_producer_and_kernel_abis
      ;;
    npa-agent-platform.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=agent_platform_schema_is_unchanged_while_current_toolchain_and_certificate_pins_are_replaced
      ;;
    npa-client.request.v1|npa-client.tactic-batch.shared-setup.v1|npa-client.tactic-batch-result.semantic.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=client_hash_layout_is_unchanged_and_commits_rebuilt_candidate_state_certificate_or_diagnostic_hashes
      ;;
    npa-client.local-process-request.v1|npa-client.local-process-response.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=local_process_envelope_is_unchanged_and_nested_current_payloads_or_results_are_validated_by_their_owner
      ;;
    npa.package.theorem_index.v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=theorem_index_schema_is_untrusted_and_unchanged_while_rows_commit_rebuilt_certificate_and_export_hashes
      ;;
    npa-ai-proof-meta-v0.1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_untrusted_metadata_schema_commits_rebuilt_certificate_export_and_axiom_report_hashes
      ;;
    npa-ai-proof-replay-v0.1)
      disposition=unrelated
      target=-
      rationale=untrusted_replay_schema_carries_raw_strings_and_an_artifact_path_but_no_term_encoding_or_accepted_proof_identity
      ;;
    npa.proof-candidate.goal-fingerprint.v1|npa.proof-candidate.import-closure.v2|npa.proof-candidate.machine-feature-profile.v1|npa.proof-candidate.environment.v2|npa.proof-candidate.v1|npa.proof-candidate-identity.v1|npa.proof-candidate-identity.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_candidate_envelope_commits_new_state_pair_profile_or_certificate_hashes
      ;;
    npa.verified-artifact-identity.v1|npa.verified-artifact-identity.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_verified_artifact_layout_commits_new_candidate_certificate_and_verifier_hashes
      ;;
    npa.local-lemma.proof-task-identity.v1|npa.local-lemma.proof-task-identity.hash.v1|npa.local-lemma.source-free-verifier-result.v1|npa.local-lemma.source-free-verifier-result.hash.v1|npa.local-lemma.available-dependency-identity.v1|npa.local-lemma.available-dependency-identity.hash.v1|npa.local-lemma.proof-task-handoff.v1|npa.local-lemma.proof-task-handoff.hash.v1|npa.local-lemma.verified-artifact-record.v1|npa.local-lemma.verified-artifact-record.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_local_lemma_lifecycle_layout_commits_new_environment_candidate_certificate_or_verifier_hashes
      ;;
    npa.theorem-invention.artifact.v1|npa.theorem-invention.artifact-identity.hash.v1|npa.theorem-invention.typecheck.import-closure.v1|npa.theorem-invention.typecheck.import-closure.hash.v1|npa.theorem-invention.typecheck.witness.v1|npa.theorem-invention.typecheck.witness.hash.v1|npa.theorem-invention.typecheck.request.v1|npa.theorem-invention.typecheck.request.hash.v1|npa.theorem-invention.typecheck.handoff.v1|npa.theorem-invention.typecheck.handoff.hash.v1|npa.theorem-invention.typecheck.blocker.v1|npa.theorem-invention.typecheck.blocker.hash.v1|npa.theorem-invention.proof-task.handoff.v1|npa.theorem-invention.proof-task.handoff.hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_theorem_invention_envelope_commits_new_environment_import_certificate_or_parser_boundaries
      ;;
    npa.proof-hole.result-sharing-key.v1|npa.proof-hole.expected-output.v1|npa.proof-hole.work-plan.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_scheduler_hash_layout_commits_new_skeleton_environment_or_context_hashes
      ;;
    npa.proof-sketch.v1|npa.proof-sketch.sketch-hash.v1|npa.proof-sketch.local-lemma-proposal-hash.v1|npa.proof-sketch.revision-patch-hash.v1|npa.proof-sketch.revision-decision-hash.v1|npa.proof-sketch.minimization-record-hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_sketch_layout_commits_new_environment_context_candidate_or_diagnostic_hashes
      ;;
    npa.parent-proof.declaration-identity.v1|npa.parent-proof.import-identity.v1|npa.parent-proof.dependency-identity.v1|npa.parent-proof.import-closure.v1|npa.parent-proof.substitution.v1|npa.parent-proof.completed-candidate.v1|npa.parent-proof.integration-output.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_parent_proof_layout_commits_new_skeleton_environment_certificate_or_dependency_hashes
      ;;
    npa.machine-api.lazy-diagnostic-cache.v1|npa.machine-api.retrieval-cache-key.v1|npa.machine-api.repair-chain.candidate-identity.v1|npa.failure-memory.candidate-shape-hash.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_cache_or_candidate_identity_commits_new_diagnostic_state_context_or_reparsed_payload_hashes
      ;;
    npa.machine-api.focused-replay.declaration-interface.hash.v1|npa.machine-api.focused-replay.import-identity.hash.v2|npa.machine-api.focused-replay.checked-current-decls.hash.v2)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_focused_replay_subhash_commits_new_context_pair_certificate_or_checked_declaration_hashes
      ;;
    npa.certificate.canonical.v0.1.hex|npa.machine-api.axiom-ref-wire.v1|npa.stdlib-machine.v1|npa.stdlib.mvp.v1|npa.stdlib.prompt-metadata.mvp.v1|npa.stdlib.theorem-index.mvp.v1|npa.std-library.*|npa.independent-checker.std-library-audit-check.v1|npa.independent-checker.std-library-audit-report.v1|npa.independent-checker.std-library-loaded-release.v1|npa.independent-checker.stdlib-audit.mvp.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_standard_library_layout_commits_new_profiles_certificate_bytes_or_certificate_derived_hashes
      ;;
    npa.candidate-verification-metadata.v1)
      disposition=retain-with-domain-separated-child
      target="$identity"
      rationale=unchanged_agent_verification_metadata_commits_new_environment_snapshot_and_certificate_evidence_hashes
      ;;
  esac
}

printf 'identity\tdisposition\ttarget_identity\trationale\tfirst_path\tfirst_line\toccurrence_count\n' \
  > "$evidence_dir/canonical-tag-disposition.tsv"

awk -F '	' '
  {
    count[$1]++
    if (!($1 in first_path)) {
      first_path[$1]=$2
      first_line[$1]=$3
      order[++n]=$1
    }
  }
  END {
    for (i=1; i<=n; i++) {
      id=order[i]
      print id "\t" first_path[id] "\t" first_line[id] "\t" count[id]
    }
  }
' "$tmp_dir/occurrences.tsv" | while IFS='	' read -r identity first_path first_line occurrence_count; do
  classify "$identity"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$identity" "$disposition" "$target" "$rationale" \
    "$first_path" "$first_line" "$occurrence_count"
done >> "$evidence_dir/canonical-tag-disposition.tsv"

expected=$(wc -l < "$evidence_dir/canonical-identity-inventory.txt" | tr -d ' ')
actual=$(awk 'NR > 1 { count++ } END { print count + 0 }' "$evidence_dir/canonical-tag-disposition.tsv")
if [ "$actual" -ne "$expected" ]; then
  echo "ledger row count mismatch: inventory=$expected ledger=$actual" >&2
  exit 1
fi

if ! awk -F '	' 'NR > 1 && $2 != "bump" && $2 != "retain-with-domain-separated-child" && $2 != "unrelated" { exit 1 }' \
  "$evidence_dir/canonical-tag-disposition.tsv"; then
  echo "ledger contains an invalid or empty disposition" >&2
  awk -F '	' 'NR > 1 && $2 != "bump" && $2 != "retain-with-domain-separated-child" && $2 != "unrelated" { print $1 "\t" $2 }' \
    "$evidence_dir/canonical-tag-disposition.tsv" >&2
  exit 1
fi

printf 'generated %s classified canonical identities\n' "$actual"
