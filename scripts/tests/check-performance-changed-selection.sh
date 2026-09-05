#!/usr/bin/env bash
set -euo pipefail

workspace_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
cd "$workspace_root"
source scripts/check-performance.sh

test_root=$(mktemp -d)
test_root=$(cd "$test_root" && pwd -P)
fixed="$test_root/fixed128"
optimized="$test_root/optimized"
output="$test_root/comparison.json"
invocations="$test_root/invocations.tsv"
mkdir -p "$fixed" "$optimized"
cleanup() {
  rm -rf -- "$test_root"
}
trap cleanup EXIT INT TERM

make_bundle() {
  local directory=$1
  local revision=$2
  local benchmark_hash=$3
  local npa_hash=$4
  local baseline_byte=$5
  printf '%s' "$baseline_byte" >"$directory/changed-selection-baseline.json"
  cat >"$directory/npa" <<EOF
#!/usr/bin/env bash
set -euo pipefail
[[ \${1:-} == --build-provenance-json-v2 ]] || exit 2
printf '%s\\n' '{"schema":"npa.cli.build_provenance.v2","source_revision":"$revision","cargo_lock_sha256":"cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc","rustc_vv":"rustc-test","cargo_profile":"release","target":"test-target","cargo_features":[],"rustflags":"","npa_main_source_sha256":"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff","production_source_set_sha256":"9999999999999999999999999999999999999999999999999999999999999999"}'
EOF
  chmod +x "$directory/npa"
  cat >"$directory/provenance.json" <<EOF
{"schema":"npa.package.changed_selection.artifact_provenance.v3","source_revision":"$revision","benchmark_executable_sha256":"$benchmark_hash","npa_executable_sha256":"$npa_hash","cargo_lock_sha256":"cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc","rustc_vv":"rustc-test","cargo_profile":"release","cargo_features":[],"target":"test-target","rustflags":"","benchmark_source_sha256":"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee","npa_main_source_sha256":"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff","production_source_set_sha256":"9999999999999999999999999999999999999999999999999999999999999999","git_version":"git version test","build_identity_sha256":"dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"}
EOF
  cat >"$directory/bench_package_changed_selection" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
directory=$(cd "$(dirname "$0")" && pwd -P)
if [[ ${1:-} == --check-artifact-provenance ]]; then
  cat "$directory/provenance.json"
  exit
fi
scenario=""
population=""
baseline=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --scenario) scenario=$2; shift 2 ;;
    --population) population=$2; shift 2 ;;
    --deterministic-baseline) baseline=$2; shift 2 ;;
    *) shift 2 ;;
  esac
done
revision=$(basename "$directory")
printf '%s\t%s\t%s\n' "$revision" "$population" "$scenario" >>"${NPA_CHANGED_SELECTION_TEST_INVOCATIONS:?}"
artifact=$(cat "$directory/provenance.json")
baseline_hash=$(shasum -a 256 "$baseline" | awk '{print $1}')
if [[ "$population" == timing-off-total ]]; then
  samples='[{"ordinal":0,"status":"passed","elapsed_ns":1},{"ordinal":1,"status":"passed","elapsed_ns":2},{"ordinal":2,"status":"passed","elapsed_ns":3},{"ordinal":3,"status":"passed","elapsed_ns":4},{"ordinal":4,"status":"passed","elapsed_ns":5},{"ordinal":5,"status":"passed","elapsed_ns":6},{"ordinal":6,"status":"passed","elapsed_ns":7}]'
  summary='{"unit":"nanoseconds","median":4,"mad":2}'
  policy=unobserved
  charge=0
else
  observation='{"measurement_schema":"npa.performance.measurements.v0.9","overflowed":false,"batch_policy":"exec_budget","candidate_paths":1,"pathspec_payload_bytes":1,"effective_argv_charge_bytes":65536,"max_batch_payload_bytes":1,"max_batch_argv_charge_bytes":9,"pathspec_batches":1,"worktree_root_queries":1,"head_queries":1,"tracked_queries":1,"untracked_queries":1,"tracked_output_paths":0,"untracked_output_paths":0,"selected_paths":0}'
  samples="[{\"ordinal\":0,\"status\":\"passed\",\"selection_ms\":1,\"observation\":$observation},{\"ordinal\":1,\"status\":\"passed\",\"selection_ms\":2,\"observation\":$observation},{\"ordinal\":2,\"status\":\"passed\",\"selection_ms\":3,\"observation\":$observation},{\"ordinal\":3,\"status\":\"passed\",\"selection_ms\":4,\"observation\":$observation},{\"ordinal\":4,\"status\":\"passed\",\"selection_ms\":5,\"observation\":$observation},{\"ordinal\":5,\"status\":\"passed\",\"selection_ms\":6,\"observation\":$observation},{\"ordinal\":6,\"status\":\"passed\",\"selection_ms\":7,\"observation\":$observation}]"
  summary='{"unit":"milliseconds","median":4,"mad":2}'
  policy=exec_budget
  charge=65536
fi
jq -cn --arg scenario "$scenario" --arg population "$population" --arg policy "$policy" --arg baseline_hash "$baseline_hash" --argjson charge "$charge" --argjson artifact "$artifact" --argjson samples "$samples" --argjson summary "$summary" '{schema:"npa.package.changed_selection.benchmark_run.v3",trusted:false,proof_evidence:false,scenario_id:$scenario,population:$population,provenance:{schema:"npa.package.changed_selection.provenance.v3",artifact:($artifact|del(.schema)),workload:{fixture_manifest_sha256:("a"*64),deterministic_baseline_sha256:$baseline_hash,candidate_profile:"stub",environment_profile:"n64",change_profile:"none",command_lane:"vf",batch_policy:$policy,effective_argv_charge_bytes:$charge,cache_policy:"disabled",measurement_mode:$population}},warmup:1,sample_count:7,status:"passed",samples:$samples,summary:$summary,elapsed_gate:"advisory"}'
EOF
  chmod +x "$directory/bench_package_changed_selection"
}

make_bundle "$fixed" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa placeholder placeholder F
make_bundle "$optimized" bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb placeholder placeholder O
for bundle in "$fixed" "$optimized"; do
  benchmark_hash=$(sha256_file "$bundle/bench_package_changed_selection")
  npa_hash=$(sha256_file "$bundle/npa")
  jq -c --arg benchmark "$benchmark_hash" --arg npa "$npa_hash" \
    '.benchmark_executable_sha256 = $benchmark | .npa_executable_sha256 = $npa' \
    "$bundle/provenance.json" >"$bundle/provenance.updated.json"
  mv "$bundle/provenance.updated.json" "$bundle/provenance.json"
done

# The hermetic stubs intentionally self-report fixed hashes; comparison preflight
# exercises schema/build compatibility while run validation checks the 100 records.
export NPA_CHANGED_SELECTION_TEST_INVOCATIONS=$invocations
run_changed_selection_comparison "$fixed" "$optimized" "$output" >/dev/null

jq -e --argjson catalog "$(changed_selection_catalog_json)" '
  .schema == "npa.package.changed_selection.comparison.v3"
  and .catalog == $catalog
  and .run_order == ["fixed128.timing-off-total","optimized.timing-off-total","optimized.timing-summary-selection","fixed128.timing-summary-selection"]
  and (.records | length == 100)
  and all(.records[]; .sample_count == 7 and (.samples | length == 7))
  and .deterministic_gate == "passed"
  and .elapsed_gate == "advisory"
  and (.artifact_hash | test("^[0-9a-f]{64}$"))
' "$output" >/dev/null

expected="$test_root/expected.tsv"
: >"$expected"
for scenario in "${CHANGED_SELECTION_CATALOG[@]}"; do
  printf 'fixed128\ttiming-off-total\t%s\n' "$scenario" >>"$expected"
  printf 'optimized\ttiming-off-total\t%s\n' "$scenario" >>"$expected"
  printf 'optimized\ttiming-summary-selection\t%s\n' "$scenario" >>"$expected"
  printf 'fixed128\ttiming-summary-selection\t%s\n' "$scenario" >>"$expected"
done
cmp "$expected" "$invocations"

for mutation in wrong duplicate reordered; do
  bad_bundle="$test_root/bad-$mutation"
  cp -R "$fixed" "$bad_bundle"
  case "$mutation" in
    wrong)
      sed -i.bak 's/"cargo_profile":"release"/"cargo_profile":"dev"/' "$bad_bundle/npa"
      rm -f "$bad_bundle/npa.bak"
      ;;
    duplicate)
      sed -i.bak 's/{"schema"/{"schema":"npa.cli.build_provenance.v2","schema"/' "$bad_bundle/npa"
      rm -f "$bad_bundle/npa.bak"
      ;;
    reordered)
      sed -i.bak 's/{"schema":"npa.cli.build_provenance.v2","source_revision":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"/{"source_revision":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","schema":"npa.cli.build_provenance.v2"/' "$bad_bundle/npa"
      rm -f "$bad_bundle/npa.bak"
      ;;
  esac
  chmod +x "$bad_bundle/npa"
  bad_npa_hash=$(sha256_file "$bad_bundle/npa")
  jq -c --arg npa "$bad_npa_hash" '.npa_executable_sha256 = $npa' \
    "$bad_bundle/provenance.json" >"$bad_bundle/provenance.updated.json"
  mv "$bad_bundle/provenance.updated.json" "$bad_bundle/provenance.json"
  if validate_changed_selection_bundle "$bad_bundle" >/dev/null 2>&1; then
    echo "changed-selection bundle accepted $mutation npa attestation" >&2
    exit 1
  fi
done

rehash_comparison() {
  local input=$1
  local output_path=$2
  local zero=0000000000000000000000000000000000000000000000000000000000000000
  local zeroed
  local digest
  zeroed="$(jq -c --arg zero "$zero" '.artifact_hash = $zero' "$input")"
  digest="$(printf '%s\n' "$zeroed" | sha256_stream)"
  jq -c --arg digest "$digest" '.artifact_hash = $digest' "$input" >"$output_path"
}

for mutation in sample population provenance order; do
  source_path="$test_root/$mutation.source.json"
  tampered="$test_root/$mutation.json"
  case "$mutation" in
    sample) jq -c '.records[0].samples[0].ordinal = 6' "$output" >"$source_path" ;;
    population) jq -c '.records[1].population = "timing-summary-selection"' "$output" >"$source_path" ;;
    provenance) jq -c '.records[1].provenance.artifact.target = "tampered-target"' "$output" >"$source_path" ;;
    order) jq -c '.records[0:2] |= reverse' "$output" >"$source_path" ;;
  esac
  rehash_comparison "$source_path" "$tampered"
  if validate_changed_selection_comparison "$tampered" >/dev/null 2>&1; then
    echo "comparison validator accepted rehashed nested $mutation tampering" >&2
    exit 1
  fi
done

rm -f -- "$output"
printf '{}' >"$output"
if run_changed_selection_comparison "$fixed" "$optimized" "$output" >/dev/null 2>&1; then
  echo "expected preexisting output to fail" >&2
  exit 1
fi
[[ "$(<"$output")" == '{}' ]]

rm -f -- "$output"
mkdir "$test_root/real-output-parent"
ln -s "$test_root/real-output-parent" "$test_root/output-parent-link"
if run_changed_selection_comparison "$fixed" "$optimized" \
  "$test_root/output-parent-link/comparison.json" >/dev/null 2>&1; then
  echo "changed-selection comparison accepted a symbolic-link output parent" >&2
  exit 1
fi
unlink "$test_root/output-parent-link"
ln -s "$test_root/missing-output" "$output"
if run_changed_selection_comparison "$fixed" "$optimized" "$output" >/dev/null 2>&1; then
  echo "changed-selection comparison accepted a dangling output symlink" >&2
  exit 1
fi
[[ -L "$output" ]]
echo "changed-selection comparison hermetic tests passed"
