#!/usr/bin/env bash
set -euo pipefail

scenario=
source_identity=
while (($#)); do
  (($# >= 2)) || exit 2
  case "$1" in
    --scenario) scenario=$2 ;;
    --source-identity) source_identity=$2 ;;
  esac
  shift 2
done
[[ -n "$scenario" && -n "$source_identity" ]] || exit 2
[[ "$source_identity" == aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ]] || {
  echo "source identity does not match fake embedded build" >&2
  exit 1
}
mode=${scenario##*.}

if [[ "${NPA_LINEAR_DAG_FAULT:-}" == missing_record && "$mode" == summary ]]; then
  exit 0
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == malformed_json && "$mode" == summary ]]; then
  echo '{'
  exit 0
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == wrong_id && "$mode" == summary ]]; then
  scenario=package.verifier.linear_dag_planning.v1.iut992.empty.j4.detailed
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == source_mismatch && "$mode" == summary ]]; then
  source_identity=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
fi
build_identity_hash=sha256:1111111111111111111111111111111111111111111111111111111111111111
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == build_mismatch && "$mode" == summary ]]; then
  build_identity_hash=sha256:2222222222222222222222222222222222222222222222222222222222222222
fi
measurements="{\"schema\":\"npa.performance.measurements.v0.9\",\"trusted\":false,\"proof_evidence\":false,\"mode\":\"$mode\",\"input_identity\":\"sha256:1212121212121212121212121212121212121212121212121212121212121212\",\"counters\":[{\"label\":\"package.cache_results\",\"unit\":\"count\",\"value\":0},{\"label\":\"package.certificate_bytes\",\"unit\":\"bytes\",\"value\":0},{\"label\":\"package.effective_jobs\",\"unit\":\"count\",\"value\":0},{\"label\":\"package.live_results\",\"unit\":\"count\",\"value\":0},{\"label\":\"package.memo_results\",\"unit\":\"count\",\"value\":0},{\"label\":\"package.modules_checked\",\"unit\":\"count\",\"value\":0},{\"label\":\"package.requested_jobs\",\"unit\":\"count\",\"value\":4}],\"modules\":[],\"module_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"declarations\":[],\"declaration_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"candidates\":[],\"candidate_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"workers\":[],\"worker_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"package_sharding\":null,\"package_layers\":[],\"package_layer_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"package_shards\":[],\"package_shard_details\":{\"attempted\":0,\"retained\":0,\"omitted\":0},\"detail_truncated\":false,\"overflowed\":false,\"clock\":{\"source\":\"fake\",\"resolution_ns\":1,\"coarse_stage_reads\":0}}"
baseline_hash='"sha256:3333333333333333333333333333333333333333333333333333333333333333"'
if [[ "$mode" == off ]]; then
  measurements=null
  baseline_hash=null
fi
extra=
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == extra_field && "$mode" == summary ]]; then
  extra=',"leak":"/private/tmp/secret"'
fi

printf '%s\n' "{\"schema\":\"npa.package_verifier.linear_dag_planning.iut_run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"$scenario\",\"fixture_manifest_hash\":\"sha256:4444444444444444444444444444444444444444444444444444444444444444\",\"baseline_hash\":$baseline_hash,\"source_identity\":\"$source_identity\",\"build_identity_hash\":\"$build_identity_hash\",\"cargo_lock_hash\":\"sha256:5555555555555555555555555555555555555555555555555555555555555555\",\"harness_source_hash\":\"sha256:9999999999999999999999999999999999999999999999999999999999999999\",\"production_source_set_hash\":\"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\",\"rustc_vv\":\"rustc\",\"cargo_profile\":\"release\",\"target\":\"test-target\",\"features\":[\"default\",\"planning-benchmark\"],\"rustflags\":\"\",\"verifier\":\"fast\",\"cache_policy\":\"disabled\",\"warmup\":1,\"sample_count\":7,\"samples_ns\":[1,2,3,4,5,6,7],\"elapsed_summary_ns\":{\"median\":4,\"median_absolute_deviation\":2,\"minimum\":1,\"maximum\":7},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":$measurements$extra}"
