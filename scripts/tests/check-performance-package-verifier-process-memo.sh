#!/usr/bin/env bash
set -euo pipefail

fake_benchmark() {
  local core_root
  core_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
  source "$core_root/scripts/check-performance.sh"
  local scenario=""
  local source_identity=""
  local memo_baseline=""
  local common_baseline=""
  local argument
  local value
  while [[ $# -gt 0 ]]; do
    argument=$1
    [[ $# -ge 2 ]] || exit 2
    value=$2
    case "$argument" in
      --scenario) scenario=$value ;;
      --source-identity) source_identity=$value ;;
      --memo-scope-baseline) memo_baseline=$value ;;
      --baseline) common_baseline=$value ;;
    esac
    shift 2
  done

  local state_path=${NPA_PROCESS_MEMO_FAKE_STATE:?}
  local call_index=0
  if [[ -s "$state_path" ]]; then
    IFS= read -r call_index <"$state_path"
  fi
  call_index=$((call_index + 1))
  printf '%s\n' "$call_index" >"$state_path"

  case "${NPA_PROCESS_MEMO_FAKE_MODE:-valid}" in
    missing)
      [[ "$call_index" != 5 ]] || exit 0
      ;;
    malformed)
      if [[ "$call_index" == 3 ]]; then
        printf '{'
        exit 0
      fi
      ;;
    generic)
      if [[ "$call_index" == 3 ]]; then
        printf '{"schema":"npa.performance.run.v0.1"}'
        exit 0
      fi
      ;;
    duplicate)
      if [[ "$call_index" == 2 ]]; then
        scenario=package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off
      fi
      ;;
    reordered)
      if [[ "$call_index" == 1 ]]; then
        scenario=package.verifier.process_memo_scope.v1.small.leaf.warm.j1.off
      fi
      ;;
    source-mismatch)
      if [[ "$call_index" == 4 ]]; then
        source_identity=ffffffffffffffffffffffffffffffffffffffff
      fi
      ;;
    build-mismatch | valid) ;;
    *) exit 2 ;;
  esac

  local build_hash=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  if [[ "${NPA_PROCESS_MEMO_FAKE_MODE:-valid}" == build-mismatch && "$call_index" == 4 ]]; then
    build_hash=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
  fi
  local baseline_row
  baseline_row="$(jq -c --arg id "$scenario" '.scenarios[] | select(.id == $id)' "$memo_baseline")"
  [[ -n "$baseline_row" ]] || exit 3
  local selection_kind selection_module closure_modules closure_bytes jobs measurement_mode memo_mode max_entries max_bytes
  selection_kind="$(jq -r '.selection.kind' <<<"$baseline_row")"
  selection_module="$(jq -c '.selection.module' <<<"$baseline_row")"
  closure_modules="$(jq -r '.selection.closure_module_count' <<<"$baseline_row")"
  closure_bytes="$(jq -r '.selection.closure_certificate_bytes' <<<"$baseline_row")"
  jobs="$(jq -r '.jobs' <<<"$baseline_row")"
  measurement_mode="$(jq -r '.measurement_mode' <<<"$baseline_row")"
  memo_mode="$(jq -r '.memo.mode' <<<"$baseline_row")"
  max_entries="$(jq -c '.memo.max_entries' <<<"$baseline_row")"
  max_bytes="$(jq -c '.memo.max_weighted_certificate_bytes' <<<"$baseline_row")"
  local baseline_memo_counters baseline_store
  baseline_memo_counters="$(jq -c '.measured_run_memo_counters' <<<"$baseline_row")"
  baseline_store="$(jq -c '.post_warmup_store' <<<"$baseline_row")"
  local common_hash=null
  local measurements=null
  if [[ "$measurement_mode" == summary ]]; then
    common_hash='"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"'
    common_counters="$(package_verifier_process_memo_summary_counters_json)"
    measurements="$(jq -cn --argjson counters "$common_counters" '{schema:"npa.performance.measurements.v0.9",trusted:false,proof_evidence:false,mode:"summary",input_identity:("sha256:"+("1"*64)),counters:$counters,modules:[],module_details:{attempted:0,retained:0,omitted:0},declarations:[],declaration_details:{attempted:0,retained:0,omitted:0},candidates:[],candidate_details:{attempted:0,retained:0,omitted:0},workers:[],worker_details:{attempted:0,retained:0,omitted:0},package_sharding:null,package_layers:[],package_layer_details:{attempted:0,retained:0,omitted:0},package_shards:[],package_shard_details:{attempted:0,retained:0,omitted:0},detail_truncated:false,overflowed:false,clock:{source:"std.monotonic.instant",resolution_ns:1,coarse_stage_reads:0}}')"
  fi
  local samples=""
  local sample_index
  for sample_index in 0 1 2 3 4 5 6; do
    [[ -z "$samples" ]] || samples+=","
    if [[ "$baseline_store" == null ]]; then
      store_stats=null
    else
      store_stats="$(jq -c --argjson hits "$((closure_modules * (sample_index + 1)))" '. + {cumulative_hits:(.cumulative_hits + $hits)}' <<<"$baseline_store")"
    fi
    samples+="{\"index\":$sample_index,\"elapsed_ns\":$((sample_index + 1)),\"status\":\"passed\",\"executed_module_count\":$closure_modules,\"memo_counters\":$baseline_memo_counters,\"store_stats\":$store_stats}"
  done

  printf '%s' "{\"schema\":\"npa.package_verifier.process_memo_scope.run.v0.2\",\"trusted\":false,\"proof_evidence\":false,\"scenario\":\"$scenario\",\"fixture_manifest_hash\":\"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\",\"memo_scope_baseline_hash\":\"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\",\"common_baseline_hash\":$common_hash,\"source_identity\":\"$source_identity\",\"build_identity_hash\":\"sha256:$build_hash\",\"cargo_lock_hash\":\"sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\",\"harness_source_hash\":\"sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee\",\"production_source_set_hash\":\"sha256:9999999999999999999999999999999999999999999999999999999999999999\",\"rustc_vv\":\"fake rustc -Vv\",\"cargo_profile\":\"release\",\"target\":\"x86_64-unknown-linux-gnu\",\"features\":[],\"rustflags\":\"\",\"verifier\":\"fast\",\"cache_policy\":\"disabled\",\"warmup\":1,\"sample_count\":7,\"profile\":{\"selection\":{\"kind\":\"$selection_kind\",\"module\":$selection_module,\"closure_module_count\":$closure_modules,\"closure_certificate_bytes\":$closure_bytes},\"jobs\":$jobs,\"measurement_mode\":\"$measurement_mode\",\"memo\":{\"mode\":\"$memo_mode\",\"max_entries\":$max_entries,\"max_weighted_certificate_bytes\":$max_bytes}},\"samples\":[$samples],\"elapsed_summary_ns\":{\"median\":4,\"median_absolute_deviation\":2,\"minimum\":1,\"maximum\":7},\"elapsed_profile\":null,\"elapsed_gate\":\"advisory\",\"status\":\"passed\",\"measurements\":$measurements}"
}

if [[ "${NPA_PROCESS_MEMO_FAKE_BENCHMARK:-0}" == 1 ]]; then
  fake_benchmark "$@"
  exit 0
fi

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
check_script="$repository_root/scripts/check-performance.sh"
test_root="$(mktemp -d "${TMPDIR:-/tmp}/npa-process-memo-script-test.XXXXXX")"
case "$test_root" in
  "${TMPDIR:-/tmp}"/npa-process-memo-script-test.*) ;;
  *)
    echo "unexpected test temporary path: $test_root" >&2
    exit 1
    ;;
esac
test_root="$(cd "$test_root" && pwd -P)"
trap 'if [[ -n "${test_root:-}" && -d "$test_root" ]]; then rm -rf -- "$test_root"; fi' EXIT
mkdir -p "$test_root/iut" "$test_root/output"

run_lane() {
  local mode=$1
  local output_path=$2
  local state_path=$3
  : >"$state_path"
  NPA_PROCESS_MEMO_FAKE_BENCHMARK=1 \
    NPA_PROCESS_MEMO_FAKE_MODE="$mode" \
    NPA_PROCESS_MEMO_FAKE_STATE="$state_path" \
    NPA_PROCESS_MEMO_BENCH_BINARY="${BASH_SOURCE[0]}" \
    NPA_PROCESS_MEMO_SKIP_BUILD=1 \
    bash "$check_script" \
      --package-verifier-process-memo-iut-root "$test_root/iut" \
      --output "$output_path"
}

expect_lane_failure() {
  local mode=$1
  local output_path="$test_root/output/$mode.json"
  if run_lane "$mode" "$output_path" "$test_root/$mode.state" >"$test_root/$mode.log" 2>&1; then
    echo "process-memo matrix lane unexpectedly accepted $mode" >&2
    exit 1
  fi
  if [[ -e "$output_path" ]]; then
    echo "failed process-memo matrix lane completed output for $mode" >&2
    exit 1
  fi
}

success_path="$test_root/output/success.json"
run_lane valid "$success_path" "$test_root/valid.state" >"$test_root/valid.log"
(
  cd "$repository_root"
  source scripts/check-performance.sh
  validate_package_verifier_process_memo_matrix "$success_path"
)
jq -e '
  .schema == "npa.package_verifier.process_memo_scope.matrix.v0.1"
  and (.catalog | length == 11)
  and .passes == ["forward", "reverse"]
  and (.records | length == 22)
  and [.records[].scenario] == (.catalog + (.catalog | reverse))
' "$success_path" >/dev/null

for mode in missing duplicate reordered generic source-mismatch build-mismatch malformed; do
  expect_lane_failure "$mode"
done

wrong_hash_path="$test_root/output/wrong-hash.json"
jq -c '.artifact_hash = "sha256:1111111111111111111111111111111111111111111111111111111111111111"' \
  "$success_path" >"$wrong_hash_path"
if (
  cd "$repository_root"
  source scripts/check-performance.sh
  validate_package_verifier_process_memo_matrix "$wrong_hash_path"
) >"$test_root/wrong-hash.log" 2>&1; then
  echo "process-memo matrix validator accepted a wrong self-hash" >&2
  exit 1
fi

rehash_matrix() {
  local input=$1
  local output=$2
  local zero_hash="sha256:0000000000000000000000000000000000000000000000000000000000000000"
  local zeroed
  local digest
  zeroed="$(jq -c --arg zero_hash "$zero_hash" '.artifact_hash = $zero_hash' "$input")"
  digest="sha256:$(printf '%s' "$zeroed" | shasum -a 256 | awk '{print $1}')"
  jq -c --arg digest "$digest" '.artifact_hash = $digest' "$input" >"$output"
}

for mutation in sample profile semantic-profile memo-counter measurement measurement-counter measurement-unknown measurement-unit measurement-order measurement-clock target features rustflags harness source-set row-order; do
  mutated_source="$test_root/output/nested-$mutation.source.json"
  mutated_path="$test_root/output/nested-$mutation.json"
  case "$mutation" in
    sample) jq -c '.records[0].samples[0].index = 6' "$success_path" >"$mutated_source" ;;
    profile) jq -c '.records[0].profile.jobs = 0' "$success_path" >"$mutated_source" ;;
    semantic-profile) jq -c '.records[0].profile.jobs = 4' "$success_path" >"$mutated_source" ;;
    memo-counter) jq -c '.records[1].samples[0].memo_counters.hits += 1' "$success_path" >"$mutated_source" ;;
    measurement) jq -c '.records[0].measurements = []' "$success_path" >"$mutated_source" ;;
    measurement-counter) jq -c '(.records[] | select(.profile.measurement_mode=="summary") | .measurements.counters[0].value) += 1' "$success_path" >"$mutated_source" ;;
    measurement-unknown) jq -c '(.records[] | select(.profile.measurement_mode=="summary") | .measurements.counters) += [{"label":"package.unknown","unit":"count","value":0}]' "$success_path" >"$mutated_source" ;;
    measurement-unit) jq -c '(.records[] | select(.profile.measurement_mode=="summary") | .measurements.counters[0].unit) = "bytes"' "$success_path" >"$mutated_source" ;;
    measurement-order) jq -c '(.records[] | select(.profile.measurement_mode=="summary") | .measurements.counters) |= reverse' "$success_path" >"$mutated_source" ;;
    measurement-clock) jq -c '(.records[] | select(.profile.measurement_mode=="summary") | .measurements.clock.coarse_stage_reads) = 1' "$success_path" >"$mutated_source" ;;
    target) jq -c '.records[1].target = "tampered-target"' "$success_path" >"$mutated_source" ;;
    features) jq -c '.records[1].features = ["tampered"]' "$success_path" >"$mutated_source" ;;
    rustflags) jq -c '.records[1].rustflags = "-Ctampered"' "$success_path" >"$mutated_source" ;;
    harness) jq -c '.records[1].harness_source_hash = "sha256:1111111111111111111111111111111111111111111111111111111111111111"' "$success_path" >"$mutated_source" ;;
    source-set) jq -c '.records[1].production_source_set_hash = "sha256:1111111111111111111111111111111111111111111111111111111111111111"' "$success_path" >"$mutated_source" ;;
    row-order) jq -c '.records[0] |= ({trusted} + del(.trusted))' "$success_path" >"$mutated_source" ;;
  esac
  rehash_matrix "$mutated_source" "$mutated_path"
  if (
    cd "$repository_root"
    source scripts/check-performance.sh
    validate_package_verifier_process_memo_matrix "$mutated_path"
  ) >"$test_root/nested-$mutation.log" 2>&1; then
    echo "process-memo matrix validator accepted rehashed nested $mutation tampering" >&2
    exit 1
  fi
done

preexisting_path="$test_root/output/preexisting.json"
printf 'sentinel\n' >"$preexisting_path"
if run_lane valid "$preexisting_path" "$test_root/preexisting.state" >"$test_root/preexisting.log" 2>&1; then
  echo "process-memo matrix lane replaced a preexisting output" >&2
  exit 1
fi
if [[ "$(<"$preexisting_path")" != sentinel ]]; then
  echo "process-memo matrix lane changed a preexisting output" >&2
  exit 1
fi

mkdir "$test_root/real-output-parent"
ln -s "$test_root/real-output-parent" "$test_root/output-parent-link"
if run_lane valid "$test_root/output-parent-link/matrix.json" \
  "$test_root/symlink-parent.state" >"$test_root/symlink-parent.log" 2>&1; then
  echo "process-memo matrix lane accepted a symbolic-link output parent" >&2
  exit 1
fi
unlink "$test_root/output-parent-link"

dangling_path="$test_root/output/dangling.json"
ln -s "$test_root/missing-output" "$dangling_path"
if run_lane valid "$dangling_path" "$test_root/dangling.state" >"$test_root/dangling.log" 2>&1; then
  echo "process-memo matrix lane accepted a dangling output symlink" >&2
  exit 1
fi
[[ -L "$dangling_path" ]]

if find "$test_root/output" -maxdepth 1 -type d -name '.npa-process-memo-matrix.*' | grep -q .; then
  echo "process-memo matrix lane left a temporary output directory" >&2
  exit 1
fi

echo "package-verifier process-memo performance script tests: passed"
