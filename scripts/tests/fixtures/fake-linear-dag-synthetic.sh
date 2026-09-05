#!/usr/bin/env bash
set -euo pipefail

scenario=
source_identity=
baseline=
while (($#)); do
  (($# >= 2)) || exit 2
  case "$1" in
    --scenario) scenario=$2 ;;
    --source-identity) source_identity=$2 ;;
    --baseline) baseline=$2 ;;
  esac
  shift 2
done
[[ -n "$scenario" && -n "$source_identity" && -f "$baseline" ]] || exit 2
[[ "$source_identity" == aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ]] || {
  echo "source identity does not match fake embedded build" >&2
  exit 1
}
mode=${scenario##*.}
suffix=${scenario#package.verifier.linear_dag_planning.v1.}
shape=${suffix%.*}

if [[ "${NPA_LINEAR_DAG_FAULT:-}" == missing_record && "$shape.$mode" == chain4096.summary ]]; then
  exit 0
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == malformed_json && "$shape.$mode" == chain4096.summary ]]; then
  echo '{'
  exit 0
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == wrong_id && "$shape.$mode" == chain4096.summary ]]; then
  scenario=package.verifier.linear_dag_planning.v1.chain4096.detailed
fi
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == source_mismatch && "$shape.$mode" == chain4096.summary ]]; then
  source_identity=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
fi
build_identity_hash=sha256:6666666666666666666666666666666666666666666666666666666666666666
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == build_mismatch && "$shape.$mode" == chain4096.summary ]]; then
  build_identity_hash=sha256:7777777777777777777777777777777777777777777777777777777777777777
fi
extra=
if [[ "${NPA_LINEAR_DAG_FAULT:-}" == extra_field && "$shape.$mode" == chain4096.summary ]]; then
  extra=',"leak":"/private/tmp/secret"'
fi

profile=$(jq -c --arg scenario "$scenario" '
  .scenarios[] | select(.id == $scenario) |
  {shape, measurement_mode, shard_profile}
' "$baseline")
observation=$(jq -c --arg scenario "$scenario" '
  .scenarios[] | select(.id == $scenario) |
  {module_count, edge_count, selected_count, layer_count,
   critical_path_length, oracle_match, shard_profile, counters}
' "$baseline")

printf '%s\n' "{\"schema\":\"npa.package_verifier.linear_dag_planning.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"$scenario\",\"baseline_hash\":\"sha256:8888888888888888888888888888888888888888888888888888888888888888\",\"source_identity\":\"$source_identity\",\"build_identity_hash\":\"$build_identity_hash\",\"cargo_lock_hash\":\"sha256:5555555555555555555555555555555555555555555555555555555555555555\",\"harness_source_hash\":\"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",\"production_source_set_hash\":\"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\",\"rustc_vv\":\"rustc\",\"cargo_profile\":\"release\",\"target\":\"test-target\",\"features\":[\"default\",\"planning-benchmark\"],\"rustflags\":\"\",\"profile\":$profile,\"warmup\":1,\"sample_count\":7,\"samples_ns\":[1,2,3,4,5,6,7],\"elapsed_summary_ns\":{\"median\":4,\"median_absolute_deviation\":2,\"minimum\":1,\"maximum\":7},\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"observation\":$observation$extra}"
