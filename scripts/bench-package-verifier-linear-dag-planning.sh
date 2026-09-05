#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 (--linear-dag-iut-root ROOT --output PATH | --validate-output PATH) --source-identity ID" >&2
  exit 2
}

linear_dag_iut_root=
source_identity=
output=
validate_output=
while (($#)); do
  (($# >= 2)) || usage
  case "$1" in
    --linear-dag-iut-root)
      [[ -z "$linear_dag_iut_root" ]] || usage
      linear_dag_iut_root=$2
      ;;
    --source-identity)
      [[ -z "$source_identity" ]] || usage
      source_identity=$2
      ;;
    --output)
      [[ -z "$output" ]] || usage
      output=$2
      ;;
    --validate-output)
      [[ -z "$validate_output" ]] || usage
      validate_output=$2
      ;;
    *) usage ;;
  esac
  shift 2
done

[[ "$source_identity" =~ ^[0-9a-f]{40}(-dirty)?$ ]] || usage
if [[ -n "$validate_output" ]]; then
  [[ -z "$linear_dag_iut_root" && -z "$output" ]] || usage
  [[ -f "$validate_output" && ! -L "$validate_output" ]] || usage
else
  [[ -n "$linear_dag_iut_root" && -d "$linear_dag_iut_root" ]] || usage
  [[ -n "$output" ]] || usage
fi
workspace_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
cd "$workspace_root"
output_root=target/performance/package-verifier-linear-dag-planning
if [[ -n "${NPA_LINEAR_DAG_TEST_OUTPUT_ROOT:-}" ]]; then
  [[ "${NPA_LINEAR_DAG_TEST_MODE:-0}" == 1 &&
    "$NPA_LINEAR_DAG_TEST_OUTPUT_ROOT" =~ ^target/performance/package-verifier-linear-dag-planning-tests\.[0-9]+$ ]] || {
    echo "test output-root override requires a scoped test-mode path" >&2
    exit 1
  }
  output_root=$NPA_LINEAR_DAG_TEST_OUTPUT_ROOT
fi
if [[ -z "$validate_output" ]]; then
  [[ "$(dirname -- "$output")" == "$output_root" ]] || usage
  output_name=$(basename -- "$output")
  [[ "$output_name" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] || usage
  [[ ! -e "$output" && ! -L "$output" ]] || {
    echo "refusing to overwrite existing output: $output" >&2
    exit 1
  }
fi
command -v jq >/dev/null || {
  echo "jq is required" >&2
  exit 1
}

for output_component in target target/performance "$output_root"; do
  [[ ! -L "$output_component" ]] || {
    echo "output directory component must not be a symbolic link: $output_component" >&2
    exit 1
  }
  [[ ! -e "$output_component" || -d "$output_component" ]] || {
    echo "output directory component is not a directory: $output_component" >&2
    exit 1
  }
done
mkdir -p "$output_root"
output_root_real=$(cd "$output_root" && pwd -P)
[[ "$output_root_real" == "$workspace_root/$output_root" ]] || {
  echo "output directory escaped the workspace: $output_root_real" >&2
  exit 1
}

fixture_manifest=testdata/performance/fixtures/manifest.v0.1.json
common_baseline=testdata/performance/baselines/measurements.v0.1.json
synthetic_baseline=testdata/performance/baselines/package-verifier-linear-dag-planning.v0.1.json

sha256_file() {
  if command -v shasum >/dev/null; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}

sha256_stream() {
  if command -v shasum >/dev/null; then
    shasum -a 256 | awk '{print $1}'
  else
    sha256sum | awk '{print $1}'
  fi
}

jq -e '
  .schema == "npa.performance.fixtures.v0.1" and
  ([.scenarios[] | select(.id | startswith("package.verifier.linear_dag_planning.v1.iut992."))] | length) == 3
' "$fixture_manifest" >/dev/null
jq -e '
  .schema == "npa.performance.baselines.v0.1" and
  ([.scenarios[] | select(.id | startswith("package.verifier.linear_dag_planning.v1.iut992."))] | length) == 2
' "$common_baseline" >/dev/null
jq -e '
  .schema == "npa.package_verifier.linear_dag_planning.baselines.v0.1" and
  (.scenarios | length) == 9
' "$synthetic_baseline" >/dev/null

if [[ -n "${NPA_LINEAR_DAG_IUT_RUNNER:-}" || -n "${NPA_LINEAR_DAG_SYNTHETIC_RUNNER:-}" || "${NPA_LINEAR_DAG_SKIP_BUILD:-0}" == 1 || -n "${NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT:-}" || -n "${NPA_LINEAR_DAG_TEST_OUTPUT_ROOT:-}" ]]; then
  [[ "${NPA_LINEAR_DAG_TEST_MODE:-0}" == 1 ]] || {
    echo "runner overrides and build skipping require NPA_LINEAR_DAG_TEST_MODE=1" >&2
    exit 1
  }
fi

if [[ -z "$validate_output" && "${NPA_LINEAR_DAG_SKIP_BUILD:-0}" != 1 ]]; then
  NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-api \
    --features planning-benchmark \
    --example bench_package_verifier --example bench_package_linear_dag
fi

iut_runner=${NPA_LINEAR_DAG_IUT_RUNNER:-target/release/examples/bench_package_verifier}
synthetic_runner=${NPA_LINEAR_DAG_SYNTHETIC_RUNNER:-target/release/examples/bench_package_linear_dag}
if [[ -z "$validate_output" ]]; then
  [[ -x "$iut_runner" && -x "$synthetic_runner" ]] || {
  echo "benchmark examples are unavailable" >&2
  exit 1
  }
fi

if [[ "${NPA_LINEAR_DAG_TEST_MODE:-0}" == 1 ]]; then
  expected_iut_harness_hash="sha256:9999999999999999999999999999999999999999999999999999999999999999"
  expected_synthetic_harness_hash="sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  expected_production_source_set_hash="sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
  expected_cargo_lock_hash="sha256:5555555555555555555555555555555555555555555555555555555555555555"
  expected_fixture_manifest_hash="sha256:4444444444444444444444444444444444444444444444444444444444444444"
  expected_common_baseline_hash="sha256:3333333333333333333333333333333333333333333333333333333333333333"
  expected_synthetic_baseline_hash="sha256:8888888888888888888888888888888888888888888888888888888888888888"
else
  expected_iut_harness_hash="sha256:$(sha256_file crates/npa-api/examples/bench_package_verifier.rs)"
  expected_synthetic_harness_hash="sha256:$(sha256_file crates/npa-api/examples/bench_package_linear_dag.rs)"
  # The production runners recompute and compare this value with their
  # build-time source-set attestation before emitting a row.  The controller
  # additionally requires one identical value across both runner kinds.
  expected_production_source_set_hash=
  expected_cargo_lock_hash="sha256:$(sha256_file Cargo.lock)"
  expected_fixture_manifest_hash="sha256:$(sha256_file "$fixture_manifest")"
  expected_common_baseline_hash="sha256:$(sha256_file "$common_baseline")"
  expected_synthetic_baseline_hash="sha256:$(sha256_file "$synthetic_baseline")"
fi

catalog=(
  package.verifier.linear_dag_planning.v1.iut992.empty.j4.off
  package.verifier.linear_dag_planning.v1.iut992.empty.j4.summary
  package.verifier.linear_dag_planning.v1.iut992.empty.j4.detailed
  package.verifier.linear_dag_planning.v1.chain4096.off
  package.verifier.linear_dag_planning.v1.chain4096.summary
  package.verifier.linear_dag_planning.v1.chain4096.detailed
  package.verifier.linear_dag_planning.v1.wide4096.off
  package.verifier.linear_dag_planning.v1.wide4096.summary
  package.verifier.linear_dag_planning.v1.wide4096.detailed
  package.verifier.linear_dag_planning.v1.diamond4096.off
  package.verifier.linear_dag_planning.v1.diamond4096.summary
  package.verifier.linear_dag_planning.v1.diamond4096.detailed
)

temp_dir=
temp_dir_identity=
cleanup() {
  local status=$?
  trap - EXIT HUP INT TERM
  set +e
  local current_identity=unavailable
  local state=path-missing-or-replaced
  if [[ -n "${temp_dir:-}" ]]; then
    current_identity=$(stat -f '%d:%i' "$temp_dir" 2>/dev/null || stat -c '%d:%i' "$temp_dir" 2>/dev/null || true)
    if [[ -d "$temp_dir" && ! -L "$temp_dir" && "$current_identity" == "$temp_dir_identity" ]]; then
      state=original-identity
    elif [[ -e "$temp_dir" || -L "$temp_dir" ]]; then
      state=identity-changed
    fi
    printf 'linear-DAG: preserving private residue; no cleanup attempted: path=%q state=%s expected_identity=%q observed_identity=%q\n' \
      "$temp_dir" "$state" "$temp_dir_identity" "$current_identity" >&2
  fi
  exit "$status"
}
identity=
iut_build_identity=
synthetic_build_identity=
iut_harness_identity=
synthetic_harness_identity=

validate_run_record() {
  local record_path=$1
  local scenario=$2
  local runner_kind=$3
  local mode=${scenario##*.}
  local expected_measurement_mode=$mode
  local expected_schema
  local expected_synthetic_profile=null
  local expected_synthetic_observation=null
  local expected_iut_counters=null
  local expected_baseline_hash
  if [[ "$runner_kind" == iut ]]; then
    expected_schema=npa.package_verifier.linear_dag_planning.iut_run.v0.2
  else
    expected_schema=npa.package_verifier.linear_dag_planning.run.v0.2
    expected_synthetic_profile=$(jq -c --arg scenario "$scenario" '
      .scenarios[] | select(.id == $scenario) |
      {shape, measurement_mode, shard_profile}
    ' "$synthetic_baseline")
    expected_synthetic_observation=$(jq -c --arg scenario "$scenario" '
      .scenarios[] | select(.id == $scenario) |
      {module_count, edge_count, selected_count, layer_count,
       critical_path_length, oracle_match, shard_profile, counters}
    ' "$synthetic_baseline")
  fi
  if [[ "$runner_kind" == iut && "$mode" != off ]]; then
    expected_iut_counters=$(jq -c --arg scenario "$scenario" '
      .scenarios[] | select(.id == $scenario) | .deterministic_counters
    ' "$common_baseline")
  fi
  if [[ "$runner_kind" == iut ]]; then
    if [[ "$mode" == off ]]; then
      expected_baseline_hash=null
    else
      expected_baseline_hash="\"$expected_common_baseline_hash\""
    fi
  else
    expected_baseline_hash="\"$expected_synthetic_baseline_hash\""
  fi
  jq -e \
    --arg schema "$expected_schema" \
    --arg scenario "$scenario" \
    --arg source "$source_identity" \
    --arg mode "$mode" \
    --arg kind "$runner_kind" \
    --arg cargo_lock_hash "$expected_cargo_lock_hash" \
    --arg fixture_manifest_hash "$expected_fixture_manifest_hash" \
    --arg iut_harness_hash "$expected_iut_harness_hash" \
    --arg synthetic_harness_hash "$expected_synthetic_harness_hash" \
    --arg production_source_set_hash "$expected_production_source_set_hash" \
    --argjson expected_baseline_hash "$expected_baseline_hash" \
    --argjson expected_iut_counters "$expected_iut_counters" \
    --argjson expected_synthetic_profile "$expected_synthetic_profile" \
    --argjson expected_synthetic_observation "$expected_synthetic_observation" '
      def uint: type == "number" and . >= 0 and floor == .;
      def sha256: type == "string" and test("^sha256:[0-9a-f]{64}$");
      def detail_counts:
        type == "object" and keys_unsorted == ["attempted","retained","omitted"] and
        all(.[]; uint);
      def measurements($expected; $mode):
        type == "object" and
        keys_unsorted == ["schema","trusted","proof_evidence","mode","input_identity","counters","modules","module_details","declarations","declaration_details","candidates","candidate_details","workers","worker_details","package_sharding","package_layers","package_layer_details","package_shards","package_shard_details","detail_truncated","overflowed","clock"] and
        .schema == "npa.performance.measurements.v0.9" and
        .trusted == false and .proof_evidence == false and .mode == $mode and
        (.input_identity | sha256) and
        (.counters as $counters |
         $counters | type == "array" and
          all(.[]; type == "object" and keys_unsorted == ["label","unit","value"] and
            (.label | type == "string" and length > 0) and
            (.unit == "count" or .unit == "bytes" or .unit == "nanoseconds") and
            (.value | uint)) and
          ([.[].label] | unique | length) == length and
          ([.[].label] == ([.[].label] | sort)) and
          length == ($expected | length) and
          all($expected | to_entries[];
            . as $entry | any($counters[]?;
              .label == $entry.key and .value == $entry.value))) and
        (.modules | type == "array") and (.module_details | detail_counts) and
        (.declarations | type == "array") and (.declaration_details | detail_counts) and
        (.candidates | type == "array") and (.candidate_details | detail_counts) and
        (.workers | type == "array") and (.worker_details | detail_counts) and
        ((.package_sharding == null) or (.package_sharding | type == "object")) and
        (.package_layers | type == "array") and (.package_layer_details | detail_counts) and
        (.package_shards | type == "array") and (.package_shard_details | detail_counts) and
        (.detail_truncated | type == "boolean") and (.overflowed | type == "boolean") and
        (.clock | type == "object" and keys_unsorted == ["source","resolution_ns","coarse_stage_reads"] and
          (.source | type == "string" and length > 0) and (.resolution_ns | uint) and
          (.coarse_stage_reads | uint));
      type == "object" and
      (if $kind == "iut" then
         keys_unsorted == ["schema","trusted","proof_evidence","scenario","fixture_manifest_hash","baseline_hash","source_identity","build_identity_hash","cargo_lock_hash","harness_source_hash","production_source_set_hash","rustc_vv","cargo_profile","target","features","rustflags","verifier","cache_policy","warmup","sample_count","samples_ns","elapsed_summary_ns","elapsed_profile","elapsed_gate","status","measurements"]
       else
         keys_unsorted == ["schema","trusted","proof_evidence","scenario","baseline_hash","source_identity","build_identity_hash","cargo_lock_hash","harness_source_hash","production_source_set_hash","rustc_vv","cargo_profile","target","features","rustflags","profile","warmup","sample_count","samples_ns","elapsed_summary_ns","elapsed_gate","status","observation"]
       end) and
      .schema == $schema and .trusted == false and .proof_evidence == false and
      .scenario == $scenario and .source_identity == $source and
      (.source_identity | test("^[0-9a-f]{40}(-dirty)?$")) and
      .cargo_profile == "release" and .features == ["default","planning-benchmark"] and
      (.target | type == "string" and length > 0) and (.rustflags | type == "string") and
      .warmup == 1 and .sample_count == 7 and
      (.samples_ns | type == "array" and length == 7 and all(.[]; uint)) and
      (.elapsed_summary_ns | type == "object" and
        keys_unsorted == ["median","median_absolute_deviation","minimum","maximum"] and
        all(.[]; uint)) and
      .elapsed_gate == "advisory" and .status == "passed" and
      (.build_identity_hash | sha256) and .cargo_lock_hash == $cargo_lock_hash and
      (.harness_source_hash | sha256) and
      (.production_source_set_hash | sha256) and
      ($production_source_set_hash == "" or
       .production_source_set_hash == $production_source_set_hash) and
      (.rustc_vv | type == "string" and length > 0) and
      ([.. | strings | select(startswith("/"))] | length == 0) and
      (if $kind == "iut" then
         .verifier == "fast" and .cache_policy == "disabled" and
         .fixture_manifest_hash == $fixture_manifest_hash and
         .baseline_hash == $expected_baseline_hash and
         .harness_source_hash == $iut_harness_hash and
         .elapsed_profile == null and
         (if $mode == "off" then .measurements == null
          else .measurements as $measurements |
            ($measurements | measurements($expected_iut_counters; $mode)) end)
       else
         .baseline_hash == $expected_baseline_hash and
         .harness_source_hash == $synthetic_harness_hash and
         .profile == $expected_synthetic_profile and
         .observation == $expected_synthetic_observation
       end)
    ' "$record_path" >/dev/null
}

validate_matrix() {
  local path=$1
  local catalog_json
  local record_index=0
  local scenario
  local kind
  local embedded_hash
  local zeroed
  local computed_hash
  catalog_json=$(jq -cn '$ARGS.positional' --args "${catalog[@]}")
  jq -e --argjson catalog "$catalog_json" '
    type == "object" and keys_unsorted == ["schema","catalog","passes","records","artifact_hash"] and
    .schema == "npa.package_verifier.linear_dag_planning.matrix.v0.1" and
    .catalog == $catalog and .passes == ["forward","reverse"] and
    [.records[].scenario] == ($catalog + ($catalog | reverse)) and
    (.records | length == 24) and
    ([.records[] | [.source_identity,.cargo_lock_hash,.production_source_set_hash,.rustc_vv,.cargo_profile,.target,.features,.rustflags]] | unique | length) == 1 and
    ([.records[] | select(.schema == "npa.package_verifier.linear_dag_planning.iut_run.v0.2") | [.build_identity_hash,.harness_source_hash,.production_source_set_hash]] | unique | length) == 1 and
    ([.records[] | select(.schema == "npa.package_verifier.linear_dag_planning.run.v0.2") | [.build_identity_hash,.harness_source_hash,.production_source_set_hash]] | unique | length) == 1 and
    (.artifact_hash | test("^[0-9a-f]{64}$")) and
    all(.. | strings; startswith("/") | not)
  ' "$path" >/dev/null || return 1
  while IFS= read -r scenario; do
    if [[ "$scenario" == package.verifier.linear_dag_planning.v1.iut992.* ]]; then
      kind=iut
    else
      kind=synthetic
    fi
    jq -c --argjson index "$record_index" '.records[$index]' "$path" \
      >"$temp_dir/validate-$record_index.json"
    validate_run_record "$temp_dir/validate-$record_index.json" "$scenario" "$kind" || return 1
    record_index=$((record_index + 1))
  done < <(printf '%s\n' "${catalog[@]}"; for ((record_index=${#catalog[@]} - 1; record_index >= 0; record_index--)); do printf '%s\n' "${catalog[record_index]}"; done)
  [[ "$(<"$path")" == "$(jq -c . "$path")" ]] || return 1
  embedded_hash=$(jq -r '.artifact_hash' "$path")
  zeroed=$(jq -c '.artifact_hash = "0000000000000000000000000000000000000000000000000000000000000000"' "$path")
  computed_hash=$(printf '%s\n' "$zeroed" | sha256_stream)
  [[ "$embedded_hash" == "$computed_hash" ]]
}

if [[ -n "$validate_output" ]]; then
  temp_dir=$(mktemp -d "$output_root/.validate.tmp.XXXXXX")
  case "$temp_dir" in
    "$output_root"/.validate.tmp.*) ;;
    *) echo "unexpected validation temporary directory: $temp_dir" >&2; exit 1 ;;
  esac
  temp_dir_identity=$(stat -f '%d:%i' "$temp_dir" 2>/dev/null || stat -c '%d:%i' "$temp_dir")
  trap cleanup EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  validate_matrix "$validate_output" || {
    echo "matrix failed strict nested validation: $validate_output" >&2
    exit 1
  }
  exit 0
fi

temp_dir=$(mktemp -d "$output_root/.matrix.tmp.XXXXXX")
case "$temp_dir" in
  "$output_root"/.matrix.tmp.*) ;;
  *)
    echo "unexpected matrix temporary directory: $temp_dir" >&2
    exit 1
    ;;
esac
chmod 700 "$temp_dir"
temp_dir_identity=$(stat -f '%d:%i' "$temp_dir" 2>/dev/null || stat -c '%d:%i' "$temp_dir")
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
records_path=$temp_dir/records.jsonl
: > "$records_path"

run_record() {
  local scenario=$1
  local mode=${scenario##*.}
  local record
  local expected_schema
  local runner_kind
  if [[ "$scenario" == package.verifier.linear_dag_planning.v1.iut992.* ]]; then
    runner_kind=iut
    expected_schema=npa.package_verifier.linear_dag_planning.iut_run.v0.2
    record=$(
      "$iut_runner" \
        --root "$linear_dag_iut_root" \
        --fixture-package-root external/npa-project-iut/proofs \
        --fixture-manifest "$fixture_manifest" \
        --baseline "$common_baseline" \
        --source-identity "$source_identity" --mode fast \
        --package-lock reconstructed --selection empty --jobs 4 \
        --measurements "$mode" --scenario "$scenario" --warmup 1 --samples 7
    )
  else
    runner_kind=synthetic
    expected_schema=npa.package_verifier.linear_dag_planning.run.v0.2
    record=$(
      "$synthetic_runner" \
        --baseline "$synthetic_baseline" \
        --source-identity "$source_identity" --scenario "$scenario" \
        --warmup 1 --samples 7
    )
  fi
  [[ -n "$record" && "$record" != *$'\n'* ]] || {
    echo "runner emitted zero or multiple records for $scenario" >&2
    return 1
  }
  local record_path="$temp_dir/record-$(wc -l <"$records_path" | tr -d ' ').json"
  printf '%s\n' "$record" >"$record_path"
  validate_run_record "$record_path" "$scenario" "$runner_kind" || {
    echo "invalid record for $scenario" >&2
    return 1
  }

  local next_identity
  next_identity=$(jq -c '[.source_identity,.cargo_lock_hash,.production_source_set_hash,.rustc_vv,.cargo_profile,.target,.features,.rustflags]' <<<"$record")
  if [[ -z "$identity" ]]; then
    identity=$next_identity
  elif [[ "$identity" != "$next_identity" ]]; then
    echo "cross-record build identity mismatch for $scenario" >&2
    return 1
  fi
  local next_build_identity
  next_build_identity=$(jq -r '.build_identity_hash' <<<"$record")
  if [[ "$runner_kind" == iut ]]; then
    local next_harness_identity
    next_harness_identity=$(jq -r '.harness_source_hash' <<<"$record")
    if [[ -z "$iut_harness_identity" ]]; then
      iut_harness_identity=$next_harness_identity
    elif [[ "$iut_harness_identity" != "$next_harness_identity" ]]; then
      echo "IUT harness source identity mismatch for $scenario" >&2
      return 1
    fi
    if [[ -z "$iut_build_identity" ]]; then
      iut_build_identity=$next_build_identity
    elif [[ "$iut_build_identity" != "$next_build_identity" ]]; then
      echo "IUT executable identity mismatch for $scenario" >&2
      return 1
    fi
  else
    local next_harness_identity
    next_harness_identity=$(jq -r '.harness_source_hash' <<<"$record")
    if [[ -z "$synthetic_harness_identity" ]]; then
      synthetic_harness_identity=$next_harness_identity
    elif [[ "$synthetic_harness_identity" != "$next_harness_identity" ]]; then
      echo "synthetic harness source identity mismatch for $scenario" >&2
      return 1
    fi
    if [[ -z "$synthetic_build_identity" ]]; then
      synthetic_build_identity=$next_build_identity
    elif [[ "$synthetic_build_identity" != "$next_build_identity" ]]; then
      echo "synthetic executable identity mismatch for $scenario" >&2
      return 1
    fi
  fi
  printf '%s\n' "$record" >> "$records_path"
}

for scenario in "${catalog[@]}"; do
  run_record "$scenario"
done
for ((index=${#catalog[@]} - 1; index >= 0; index--)); do
  run_record "${catalog[index]}"
done

catalog_json=$(jq -cn '$ARGS.positional' --args "${catalog[@]}")
records_json=$(jq -cs '.' "$records_path")
zeros=0000000000000000000000000000000000000000000000000000000000000000
zero_matrix=$temp_dir/matrix.zero.json
final_matrix=$temp_dir/matrix.final.json
verified_zero_matrix=$temp_dir/matrix.verified-zero.json
jq -n \
  --argjson catalog "$catalog_json" \
  --argjson records "$records_json" \
  --arg zeros "$zeros" '
    {schema:"npa.package_verifier.linear_dag_planning.matrix.v0.1",
     catalog:$catalog,
     passes:["forward","reverse"],
     records:$records,
     artifact_hash:$zeros}
  ' | jq -c . > "$zero_matrix"

artifact_hash=$(sha256_file "$zero_matrix")
jq -c --arg artifact_hash "$artifact_hash" '.artifact_hash = $artifact_hash' \
  "$zero_matrix" > "$final_matrix"
jq -c --arg zeros "$zeros" '.artifact_hash = $zeros' \
  "$final_matrix" > "$verified_zero_matrix"
[[ "$(sha256_file "$verified_zero_matrix")" == "$artifact_hash" ]] || {
  echo "matrix self-hash verification failed" >&2
  exit 1
}
validate_matrix "$final_matrix" || {
  echo "final matrix failed strict nested validation" >&2
  exit 1
}
[[ ! -e "$output" && ! -L "$output" ]] || {
  echo "output appeared during run: $output" >&2
  exit 1
}
ln "$final_matrix" "$output" || {
  echo "refusing to replace output that appeared during run: $output" >&2
  exit 1
}
if [[ -n "${NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT:-}" ]]; then
  [[ "${NPA_LINEAR_DAG_TEST_MODE:-0}" == 1 && -d "$NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT" && ! -L "$NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT" ]] || exit 1
  relocated="$NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT/relocated"
  mv -- "$temp_dir" "$relocated"
  mkdir -m 700 -- "$temp_dir"
  printf 'keep\n' >"$relocated/sentinel"
  printf '%s\n' "$temp_dir" >"$NPA_LINEAR_DAG_CLEANUP_FAULT_ROOT/original-path"
fi
echo "$output"
