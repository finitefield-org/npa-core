#!/usr/bin/env bash
set -euo pipefail

workspace_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
cd "$workspace_root"
runner=scripts/bench-package-verifier-linear-dag-planning.sh
iut_runner=scripts/tests/fixtures/fake-linear-dag-iut.sh
synthetic_runner=scripts/tests/fixtures/fake-linear-dag-synthetic.sh
source_identity=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
test_root=$(mktemp -d)
test_output_root=target/performance/package-verifier-linear-dag-planning-tests.$$
output=$test_output_root/hermetic-matrix.$$.json
cleanup() {
  rm -f -- "$output"
  rm -rf -- "$test_output_root"
  rm -rf -- "$test_root"
}
trap cleanup EXIT INT TERM

run_harness() {
  NPA_LINEAR_DAG_TEST_MODE=1 \
  NPA_LINEAR_DAG_SKIP_BUILD=1 \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_FAULT=${1:-} \
    "$runner" \
      --linear-dag-iut-root "$test_root" \
      --source-identity "$source_identity" \
      --output "$output"
}

run_harness >/dev/null
jq -e '
  .schema == "npa.package_verifier.linear_dag_planning.matrix.v0.1" and
  (.catalog | length) == 12 and
  .passes == ["forward", "reverse"] and
  (.records | length) == 24 and
  ([.records[].scenario] == (.catalog + (.catalog | reverse))) and
  (.artifact_hash | test("^[0-9a-f]{64}$"))
' "$output" >/dev/null

rehash_matrix() {
  local input=$1
  local output_path=$2
  local zero=0000000000000000000000000000000000000000000000000000000000000000
  local zeroed
  local digest
  zeroed="$(jq -c --arg zero "$zero" '.artifact_hash = $zero' "$input")"
  if command -v shasum >/dev/null; then
    digest="$(printf '%s\n' "$zeroed" | shasum -a 256 | awk '{print $1}')"
  else
    digest="$(printf '%s\n' "$zeroed" | sha256sum | awk '{print $1}')"
  fi
  jq -c --arg digest "$digest" '.artifact_hash = $digest' "$input" >"$output_path"
}

matrix_tmp_before=$(find "$test_output_root" \
  -mindepth 1 -maxdepth 1 -type d -name '.matrix.tmp.*' -print | sort)
for mutation in sample profile target features rustflags harness source_set measurement order; do
  source_path="$test_root/$mutation.source.json"
  tampered="$test_root/$mutation.json"
  case "$mutation" in
    sample) jq -c '.records[0].samples_ns[0] = -1' "$output" >"$source_path" ;;
    profile) jq -c '.records[3].profile.measurement_mode = "detailed"' "$output" >"$source_path" ;;
    target) jq -c '.records[1].target = "tampered-target"' "$output" >"$source_path" ;;
    features) jq -c '.records[1].features = ["default","planning_benchmark"]' "$output" >"$source_path" ;;
    rustflags) jq -c '.records[1].rustflags = "-Ctampered"' "$output" >"$source_path" ;;
    harness) jq -c '.records[1].harness_source_hash = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"' "$output" >"$source_path" ;;
    source_set) jq -c '.records[1].production_source_set_hash = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"' "$output" >"$source_path" ;;
    measurement) jq -c '.records[1].measurements.counters[0].value += 1' "$output" >"$source_path" ;;
    order) jq -c '.records[0:2] |= reverse' "$output" >"$source_path" ;;
  esac
  rehash_matrix "$source_path" "$tampered"
  if NPA_LINEAR_DAG_TEST_MODE=1 \
    NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
    NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
    NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
    "$runner" --validate-output "$tampered" \
      --source-identity "$source_identity" >/dev/null 2>&1; then
    echo "production validator accepted rehashed nested $mutation tampering" >&2
    exit 1
  fi
done
matrix_tmp_after=$(find "$test_output_root" \
  -mindepth 1 -maxdepth 1 -type d -name '.matrix.tmp.*' -print | sort)
[[ "$matrix_tmp_after" == "$matrix_tmp_before" ]] || {
  echo "validation mode orphaned a matrix temporary directory" >&2
  exit 1
}

reordered_source="$test_root/reordered.source.json"
reordered="$test_root/reordered.json"
jq -c '{catalog,schema,passes,records,artifact_hash}' "$output" >"$reordered_source"
rehash_matrix "$reordered_source" "$reordered"
if NPA_LINEAR_DAG_TEST_MODE=1 \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  "$runner" --validate-output "$reordered" \
    --source-identity "$source_identity" >/dev/null 2>&1; then
  echo "production validator accepted reordered matrix fields" >&2
  exit 1
fi
rm -f -- "$output"

cleanup_fault_root="$test_root/cleanup-fault"
mkdir "$cleanup_fault_root"
if ! NPA_LINEAR_DAG_TEST_MODE=1 NPA_LINEAR_DAG_SKIP_BUILD=1 \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT=$cleanup_fault_root \
  "$runner" --linear-dag-iut-root "$test_root" \
  --source-identity "$source_identity" --output "$output" >/dev/null 2>&1; then
  echo "renamed-out residue reporting run failed" >&2
  exit 1
fi
[[ -f "$cleanup_fault_root/relocated/sentinel" ]]
replacement=$(<"$cleanup_fault_root/original-path")
[[ -d "$replacement" && ! -L "$replacement" ]]
rm -f -- "$output" "$cleanup_fault_root/relocated/sentinel" "$cleanup_fault_root/original-path"
rm -f -- "$cleanup_fault_root/relocated"/*
rmdir -- "$cleanup_fault_root/relocated" "$replacement" "$cleanup_fault_root"

for fault in missing_record wrong_id source_mismatch build_mismatch malformed_json extra_field; do
  if run_harness "$fault" >/dev/null 2>&1; then
    echo "expected $fault to fail" >&2
    exit 1
  fi
  [[ ! -e "$output" ]] || {
    echo "$fault left a partial output" >&2
    exit 1
  }
done

for identity in unbound bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb; do
  if NPA_LINEAR_DAG_TEST_MODE=1 NPA_LINEAR_DAG_SKIP_BUILD=1 \
    NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
    NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
    "$runner" --linear-dag-iut-root "$test_root" --source-identity "$identity" --output "$output" >/dev/null 2>&1; then
    echo "expected unbound or embedded-source-mismatched identity to fail: $identity" >&2
    exit 1
  fi
done

escape_output=$test_output_root/../../../linear-dag-escape.$$.json
if NPA_LINEAR_DAG_TEST_MODE=1 NPA_LINEAR_DAG_SKIP_BUILD=1 \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  "$runner" --linear-dag-iut-root "$test_root" \
  --source-identity "$source_identity" --output "$escape_output" >/dev/null 2>&1; then
  echo "expected traversal output to fail" >&2
  exit 1
fi

hidden_output=$test_output_root/.hidden-matrix.json
if NPA_LINEAR_DAG_TEST_MODE=1 NPA_LINEAR_DAG_SKIP_BUILD=1 \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  "$runner" --linear-dag-iut-root "$test_root" \
  --source-identity "$source_identity" --output "$hidden_output" >/dev/null 2>&1; then
  echo "expected hidden output basename to fail containment" >&2
  exit 1
fi
[[ ! -e "$hidden_output" ]] || {
  echo "hidden output basename created an artifact" >&2
  exit 1
}

if NPA_LINEAR_DAG_SKIP_BUILD=1 \
  NPA_LINEAR_DAG_IUT_RUNNER=$iut_runner \
  NPA_LINEAR_DAG_SYNTHETIC_RUNNER=$synthetic_runner \
  NPA_LINEAR_DAG_TEST_OUTPUT_ROOT=$test_output_root \
  "$runner" --linear-dag-iut-root "$test_root" \
  --source-identity "$source_identity" --output "$output" >/dev/null 2>&1; then
  echo "expected ungated runner overrides to fail" >&2
  exit 1
fi

: > "$output"
if run_harness >/dev/null 2>&1; then
  echo "expected preexisting output to fail" >&2
  exit 1
fi
[[ -f "$output" && ! -s "$output" ]] || {
  echo "preexisting output was modified" >&2
  exit 1
}
rm -f -- "$output"
ln -s "$test_root/missing-output" "$output"
if run_harness >/dev/null 2>&1; then
  echo "linear-DAG orchestration accepted a dangling output symlink" >&2
  exit 1
fi
[[ -L "$output" ]]
echo "linear-DAG orchestration hermetic tests passed"
