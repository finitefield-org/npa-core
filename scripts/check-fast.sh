#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Default development gate for core NPA changes. The proof corpus lives in the
# sibling npa-corpus repository.
echo "[1/3] Formatting check"
cargo fmt --all -- --check

echo "[2/3] Clippy workspace gate"
cargo clippy --workspace --all-targets -- -D warnings

echo "[3/3] Workspace tests"
cargo test --workspace -- \
  --skip proof_corpus \
  --skip proof_package \
  --skip package_artifact_ \
  --skip package_artifact_extraction_ \
  --skip package_artifacts_checked_in_generated_ \
  --skip package_axiom_report_ \
  --skip package_axiom_report_projection_ \
  --skip package_build_certs_check_read_through_ \
  --skip package_build_certs_check_rejects_checked_in_certificate_byte_drift \
  --skip package_cache_aware_dag_verifier_ \
  --skip package_check_hashes_ \
  --skip package_cli_smoke_ \
  --skip package_cli_source_free_ \
  --skip package_cli_temp_fixture_rejects_stale_source_certificate_and_lock \
  --skip package_export_summary_ \
  --skip package_fast_verifier_ \
  --skip package_generated_check_command_ \
  --skip package_import_context_export_cache_ \
  --skip package_index_ \
  --skip package_lock_builder_ \
  --skip package_lock_import_identity_ \
  --skip package_projection_ \
  --skip package_publish_ \
  --skip package_reference_summary_cache_key_ \
  --skip package_reference_verifier_ \
  --skip package_shared_snapshot_ \
  --skip package_phase8_ \
  --skip package_source_free_ \
  --skip package_theorem_index_projection_ \
  --skip package_verified_result_cache_key_ \
  --skip package_verify_certs_ \
  --skip package_verify_external_ \
  --skip package_verifier_
