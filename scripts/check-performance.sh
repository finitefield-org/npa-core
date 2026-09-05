#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

sha256_stream() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  else
    echo "neither shasum nor sha256sum is available" >&2
    return 1
  fi
}

sha256_file() {
  local path=$1
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$path" | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$path" | awk '{print $1}'
  else
    echo "neither shasum nor sha256sum is available" >&2
    return 1
  fi
}

require_snap_vmsp_controller_matrix_digest() {
  local label=$1
  local digest=$2
  [[ "$digest" =~ ^[0-9a-f]{64}$ ]] || {
    echo "$label controller returned an invalid matrix digest" >&2
    return 1
  }
}

current_source_identity() {
  local identity
  identity="$(/usr/bin/git rev-parse HEAD)"
  if [[ -n "$(/usr/bin/git status --porcelain --untracked-files=normal)" ]]; then
    identity="${identity}-dirty"
  fi
  printf '%s\n' "$identity"
}

canonical_new_output_path() {
  local requested=$1
  local parent
  local basename
  local requested_absolute
  local canonical_parent
  basename="$(basename -- "$requested")"
  parent="$(dirname -- "$requested")"
  [[ "$basename" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] || {
    echo "output basename is unsafe: $basename" >&2
    return 1
  }
  [[ -d "$parent" && ! -L "$parent" ]] || {
    echo "output parent must be an existing non-symlink directory: $parent" >&2
    return 1
  }
  if [[ "$requested" == /* ]]; then
    requested_absolute=$requested
  else
    requested_absolute="$(pwd -P)/$requested"
  fi
  case "$requested_absolute/" in
    *//*|*/./*|*/../*)
      echo "output path must be normalized: $requested" >&2
      return 1
      ;;
  esac
  canonical_parent="$(cd "$parent" && pwd -P)"
  [[ "$requested_absolute" == "$canonical_parent/$basename" ]] || {
    echo "output path contains a symlink or noncanonical parent: $requested" >&2
    return 1
  }
  [[ ! -e "$requested_absolute" && ! -L "$requested_absolute" ]] || {
    echo "refusing to replace output: $requested_absolute" >&2
    return 1
  }
  printf '%s\n' "$requested_absolute"
}

private_directory_identity() {
  local path=$1
  if stat -f '%d:%i:%u:%Lp' "$path" >/dev/null 2>&1; then
    stat -f '%d:%i:%u:%Lp' "$path"
  elif stat -c '%d:%i:%u:%a' "$path" >/dev/null 2>&1; then
    stat -c '%d:%i:%u:%a' "$path"
  else
    echo "stat cannot report a portable directory identity: $path" >&2
    return 1
  fi
}

canonical_private_temp_parent() {
  local parent=$1
  local canonical
  [[ -d "$parent" && ! -L "$parent" ]] || {
    echo "private temporary parent is not a real directory: $parent" >&2
    return 1
  }
  canonical="$(cd "$parent" && pwd -P)"
  [[ -d "$canonical" && ! -L "$canonical" ]] || return 1
  printf '%s\n' "$canonical"
}

make_private_temp_dir() {
  local parent=$1
  local prefix=$2
  local canonical_parent
  local path
  local basename
  local identity
  [[ "$prefix" =~ ^[A-Za-z0-9._-]+$ ]] || {
    echo "private temporary prefix is unsafe: $prefix" >&2
    return 1
  }
  canonical_parent="$(canonical_private_temp_parent "$parent")" || return 1
  path="$(umask 077; mktemp -d "$canonical_parent/${prefix}.XXXXXX")" || return 1
  basename="$(basename -- "$path")"
  case "$basename" in "$prefix".*) ;; *) return 1 ;; esac
  [[ -d "$path" && ! -L "$path" && "$(cd "$path" && pwd -P)" == "$path" ]] || return 1
  chmod 700 "$path"
  identity="$(private_directory_identity "$path")" || return 1
  [[ "$identity" == *:700 ]] || {
    echo "private temporary directory is not owner-only: $path" >&2
    return 1
  }
  printf '%s\t%s\t%s\n' "$path" "$canonical_parent" "$identity"
}

guarded_remove_private_temp_dir() {
  local path=$1
  local parent=$2
  local prefix=$3
  local identity=$4
  local basename
  local current_identity
  [[ -n "$path" && -n "$parent" && -n "$prefix" && -n "$identity" ]] || return 1
  basename="$(basename -- "$path")"
  case "$basename" in "$prefix".*) ;; *) return 1 ;; esac
  [[ "$path" == "$parent/$basename" ]] || return 1
  [[ -d "$parent" && ! -L "$parent" && "$(cd "$parent" && pwd -P)" == "$parent" ]] || return 1
  [[ -d "$path" && ! -L "$path" && "$(cd "$path" && pwd -P)" == "$path" ]] || return 1
  current_identity="$(private_directory_identity "$path")" || return 1
  [[ "$current_identity" == "$identity" ]] || {
    echo "refusing to remove replaced private temporary directory: $path" >&2
    return 1
  }
  if [[ -n "$(/usr/bin/find "$path" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
    echo "refusing recursive private-temp cleanup; caller must remove its exact catalog first: $path" >&2
    return 1
  fi
  rmdir -- "$path"
}

cleanup_private_temp_catalog() {
  local path=$1
  local parent=$2
  local prefix=$3
  local identity=$4
  shift 4
  local candidate
  local relative
  local current_identity

  [[ -e "$path" ]] || return 0
  [[ -d "$path" && ! -L "$path" ]] || {
    echo "refusing to clean a replaced private temporary directory: $path" >&2
    return 1
  }
  current_identity="$(private_directory_identity "$path")" || return 1
  [[ "$current_identity" == "$identity" ]] || {
    echo "refusing to clean a replaced private temporary directory: $path" >&2
    return 1
  }

  for candidate in "$@"; do
    case "$candidate" in
      "$path"/*) relative=${candidate#"$path"/} ;;
      *)
        echo "refusing private-temp cleanup outside the exact catalog root: $candidate" >&2
        return 1
        ;;
    esac
    if [[ -z "$relative" || "$relative" == */* ]]; then
      echo "refusing non-direct private-temp catalog entry: $candidate" >&2
      return 1
    fi
    if [[ -e "$candidate" || -L "$candidate" ]]; then
      if [[ ! -f "$candidate" || -L "$candidate" ]]; then
        echo "refusing to remove a replaced private-temp catalog entry: $candidate" >&2
        return 1
      fi
      current_identity="$(private_directory_identity "$path")" || return 1
      [[ "$current_identity" == "$identity" ]] || {
        echo "refusing to clean a replaced private temporary directory: $path" >&2
        return 1
      }
      rm -- "$candidate"
    fi
  done

  guarded_remove_private_temp_dir "$path" "$parent" "$prefix" "$identity"
}

guarded_remove_publication_lock() {
  local path=$1
  local parent=$2
  local identity=$3
  local basename
  local current_identity
  basename="$(basename -- "$path")"
  [[ "$basename" == *.publish-lock && "$path" == "$parent/$basename" ]] || return 1
  [[ -d "$parent" && ! -L "$parent" && "$(cd "$parent" && pwd -P)" == "$parent" ]] || return 1
  [[ -d "$path" && ! -L "$path" && "$(cd "$path" && pwd -P)" == "$path" ]] || return 1
  current_identity="$(private_directory_identity "$path")" || return 1
  [[ "$current_identity" == "$identity" ]] || {
    echo "refusing to remove replaced publication lock: $path" >&2
    return 1
  }
  rmdir "$path"
}

snapshot_tree_sha256() {
  local root=$1
  local absolute_root
  local canonical_root
  local component
  local cursor=
  local listing
  local path
  local relative
  local key
  local index
  local LC_ALL=C
  local -a paths=()
  if [[ "$root" == /* ]]; then
    absolute_root=$root
  else
    absolute_root="$(pwd -P)/$root"
  fi
  case "$absolute_root/" in
    *//*|*/./*|*/../*)
      echo "tree snapshot root must be a normalized path: $root" >&2
      return 1
      ;;
  esac
  IFS=/ read -r -a root_components <<<"${absolute_root#/}"
  for component in "${root_components[@]}"; do
    [[ -n "$component" ]] || continue
    cursor="$cursor/$component"
    [[ ! -L "$cursor" ]] || {
      echo "tree snapshot root contains a symbolic link: $cursor" >&2
      return 1
    }
  done
  [[ -d "$absolute_root" ]] || {
    echo "tree snapshot root is not a directory: $root" >&2
    return 1
  }
  canonical_root="$(cd "$absolute_root" && pwd -P)"
  [[ "$canonical_root" == "$absolute_root" ]] || {
    echo "tree snapshot root is not canonical: $root" >&2
    return 1
  }
  listing="$(mktemp "${TMPDIR:-/tmp}/npa-tree-list.XXXXXX")"
  /usr/bin/find "$canonical_root" -print0 >"$listing" || {
    rm -f -- "$listing"
    return 1
  }
  while IFS= read -r -d '' path; do
    paths+=("$path")
  done <"$listing"
  rm -f -- "$listing"
  for ((index = 1; index < ${#paths[@]}; index++)); do
    key=${paths[index]}
    local cursor=$index
    while ((cursor > 0)) && [[ ${paths[cursor - 1]} > "$key" ]]; do
      paths[cursor]=${paths[cursor - 1]}
      cursor=$((cursor - 1))
    done
    paths[cursor]=$key
  done
  for path in "${paths[@]}"; do
    if [[ "$path" == "$canonical_root" ]]; then
      relative=.
    else
      relative=${path#"$canonical_root"/}
      [[ "$relative" != "$path" ]] || {
        echo "tree snapshot entry escaped its root: $path" >&2
        return 1
      }
    fi
    if [[ -L "$path" ]]; then
      echo "tree snapshot rejects symbolic links: $relative" >&2
      return 1
    elif [[ -d "$path" ]]; then
      printf 'directory\0%s\0' "$relative"
    elif [[ -f "$path" ]]; then
      printf 'file\0%s\0%s\0' "$relative" "$(sha256_file "$path")"
    else
      echo "tree snapshot rejects special files: $relative" >&2
      return 1
    fi
  done
}

run_whnf_elapsed_profile_report() (
  local elapsed_profile=$1
  local output_path=$2
  local fixture
  local baseline
  local measure_process
  local package_harness
  local source_identity

  [[ -f "$elapsed_profile" && ! -L "$elapsed_profile" ]] || {
    echo "WHNF elapsed profile is not a regular file: $elapsed_profile" >&2
    return 1
  }
  elapsed_profile="$(cd "$(dirname "$elapsed_profile")" && pwd -P)/$(basename "$elapsed_profile")"
  output_path="$(canonical_new_output_path "$output_path")" || return 1
  fixture="$(cd testdata/performance/fixtures && pwd -P)/kernel-whnf-application-spine.v0.1.json"
  baseline="$(cd testdata/performance/baselines && pwd -P)/kernel-whnf-application-spine.measurements.v0.2.json"
  measure_process="$(pwd -P)/target/release/examples/measure_process"
  package_harness="$(pwd -P)/target/release/examples/check_whnf_application_spine_package"
  source_identity="$(current_source_identity)" || return 1
  NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-api \
    --example bench_whnf_application_spine \
    --example check_whnf_application_spine_package
  NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release \
    -p npa-cli --example measure_process
  target/release/examples/bench_whnf_application_spine \
    --controller \
    --phase candidate \
    --fixture-manifest "$fixture" \
    --baseline "$baseline" \
    --measure-process "$measure_process" \
    --package-harness "$package_harness" \
    --output "$output_path" \
    --elapsed-profile "$elapsed_profile" || {
      echo "WHNF application-spine controller failed" >&2
      return 1
    }
  target/release/examples/bench_whnf_application_spine \
    --validate-report "$output_path" \
    --phase candidate \
    --fixture-manifest "$fixture" \
    --baseline "$baseline" \
    --measure-process "$measure_process" \
    --package-harness "$package_harness" \
    --elapsed-profile "$elapsed_profile" || {
      echo "WHNF application-spine strict report validation failed" >&2
      return 1
    }
  echo "WHNF application-spine reviewed report: $output_path"
)

CHANGED_SELECTION_CATALOG=(
  package.changed_selection.git_batching.v1.empty0.clean
  package.changed_selection.git_batching.v1.tiny1.clean
  package.changed_selection.git_batching.v1.tiny1.tracked1
  package.changed_selection.git_batching.v1.tiny1.untracked1
  package.changed_selection.git_batching.v1.former127.clean
  package.changed_selection.git_batching.v1.former128.clean
  package.changed_selection.git_batching.v1.former129.clean
  package.changed_selection.git_batching.v1.count1023.clean
  package.changed_selection.git_batching.v1.count1024.clean
  package.changed_selection.git_batching.v1.count1025.clean
  package.changed_selection.git_batching.v1.byte65535.clean
  package.changed_selection.git_batching.v1.byte65536.clean
  package.changed_selection.git_batching.v1.byte65537.clean
  package.changed_selection.git_batching.v1.long32.mixed
  package.changed_selection.git_batching.v1.long128.mixed
  package.changed_selection.git_batching.v1.long1024.mixed
  package.changed_selection.git_batching.v1.fallback1.clean
  package.changed_selection.git_batching.v1.fallback129.clean
  package.changed_selection.git_batching.v1.fallback1024.clean
  package.changed_selection.git_batching.v1.inflated129.clean
  package.changed_selection.git_batching.v1.inflated992.clean
  package.changed_selection.git_batching.v1.iut1401.clean
  package.changed_selection.git_batching.v1.iut1401.tracked1
  package.changed_selection.git_batching.v1.iut1401.untracked1
  package.changed_selection.git_batching.v1.large4096.mixed
)

changed_selection_catalog_json() {
  printf '%s\n' "${CHANGED_SELECTION_CATALOG[@]}" | jq -Rsc 'split("\n")[:-1]'
}

validate_changed_selection_run() {
  local path=$1
  local scenario=$2
  local population=$3
  jq -e --arg scenario "$scenario" --arg population "$population" '
    def natural: type == "number" and isfinite and floor == . and . >= 0;
    def hash: type == "string" and test("^[0-9a-f]{64}$");
    . as $run |
    type == "object"
    and keys_unsorted == ["schema","trusted","proof_evidence","scenario_id","population","provenance","warmup","sample_count","status","samples","summary","elapsed_gate"]
    and .schema == "npa.package.changed_selection.benchmark_run.v3"
    and .trusted == false and .proof_evidence == false
    and .scenario_id == $scenario and .population == $population
    and .warmup == 1 and .sample_count == 7 and .status == "passed"
    and .elapsed_gate == "advisory"
    and (.samples | length == 7)
    and [.samples[].ordinal] == [0,1,2,3,4,5,6]
    and (.provenance | keys_unsorted == ["schema","artifact","workload"])
    and .provenance.schema == "npa.package.changed_selection.provenance.v3"
    and (.provenance.artifact | keys_unsorted == ["source_revision","benchmark_executable_sha256","npa_executable_sha256","cargo_lock_sha256","rustc_vv","cargo_profile","cargo_features","target","rustflags","benchmark_source_sha256","npa_main_source_sha256","production_source_set_sha256","git_version","build_identity_sha256"])
    and (.provenance.artifact.source_revision | test("^[0-9a-f]{40}(-dirty)?$"))
    and (.provenance.artifact.benchmark_executable_sha256 | hash)
    and (.provenance.artifact.npa_executable_sha256 | hash)
    and (.provenance.artifact.cargo_lock_sha256 | hash)
    and (.provenance.artifact.benchmark_source_sha256 | hash)
    and (.provenance.artifact.npa_main_source_sha256 | hash)
    and (.provenance.artifact.production_source_set_sha256 | hash)
    and (.provenance.artifact.build_identity_sha256 | hash)
    and (.provenance.artifact.rustc_vv | type == "string" and length > 0)
    and (.provenance.artifact.cargo_profile | type == "string" and length > 0)
    and (.provenance.artifact.target | type == "string" and length > 0)
    and (.provenance.artifact.rustflags | type == "string")
    and (.provenance.artifact.git_version | type == "string" and length > 0)
    and (.provenance.artifact.cargo_features | type == "array" and all(.[]; type == "string" and length > 0))
    and (.provenance.artifact.cargo_features == (.provenance.artifact.cargo_features | sort | unique))
    and (.provenance.workload | keys_unsorted == ["fixture_manifest_sha256","deterministic_baseline_sha256","candidate_profile","environment_profile","change_profile","command_lane","batch_policy","effective_argv_charge_bytes","cache_policy","measurement_mode"])
    and (.provenance.workload.fixture_manifest_sha256 | hash)
    and (.provenance.workload.deterministic_baseline_sha256 | hash)
    and .provenance.workload.command_lane == "vf"
    and .provenance.workload.cache_policy == "disabled"
    and .provenance.workload.measurement_mode == $population
    and (.summary | keys_unsorted == ["unit","median","mad"])
    and (.summary.median | natural) and (.summary.mad | natural)
    and (if $population == "timing-off-total" then
      .provenance.workload.batch_policy == "unobserved"
      and .provenance.workload.effective_argv_charge_bytes == 0
      and .summary.unit == "nanoseconds"
      and all(.samples[]; keys_unsorted == ["ordinal","status","elapsed_ns"] and .status == "passed" and (.elapsed_ns | natural))
    else
      (.provenance.workload.batch_policy == "not_selected" or .provenance.workload.batch_policy == "exec_budget" or .provenance.workload.batch_policy == "legacy128")
      and (.provenance.workload.effective_argv_charge_bytes | natural)
      and .summary.unit == "milliseconds"
      and all(.samples[];
        keys_unsorted == ["ordinal","status","selection_ms","observation"]
        and .status == "passed"
        and (.selection_ms | natural)
        and (.observation | keys_unsorted == ["measurement_schema","overflowed","batch_policy","candidate_paths","pathspec_payload_bytes","effective_argv_charge_bytes","max_batch_payload_bytes","max_batch_argv_charge_bytes","pathspec_batches","worktree_root_queries","head_queries","tracked_queries","untracked_queries","tracked_output_paths","untracked_output_paths","selected_paths"])
        and (.observation.measurement_schema == "npa.performance.measurements.v0.5" or .observation.measurement_schema == "npa.performance.measurements.v0.6" or .observation.measurement_schema == "npa.performance.measurements.v0.7" or .observation.measurement_schema == "npa.performance.measurements.v0.8" or .observation.measurement_schema == "npa.performance.measurements.v0.9")
        and .observation.overflowed == false
        and (.observation.batch_policy == "not_selected" or .observation.batch_policy == "exec_budget" or .observation.batch_policy == "legacy128")
        and all(.observation.candidate_paths,.observation.pathspec_payload_bytes,.observation.effective_argv_charge_bytes,.observation.max_batch_payload_bytes,.observation.max_batch_argv_charge_bytes,.observation.pathspec_batches,.observation.worktree_root_queries,.observation.head_queries,.observation.tracked_queries,.observation.untracked_queries,.observation.tracked_output_paths,.observation.untracked_output_paths,.observation.selected_paths; natural)
        and .observation.batch_policy == $run.provenance.workload.batch_policy
        and .observation.effective_argv_charge_bytes == $run.provenance.workload.effective_argv_charge_bytes)
      and ([.samples[].observation] | unique | length == 1)
    end)
    and all(.. | strings; startswith("/") | not)
  ' "$path" >/dev/null || return 1
}

validate_changed_selection_bundle() {
  local directory=$1
  local validator="$directory/bench_package_changed_selection"
  local npa_binary="$directory/npa"
  local provenance
  local attestation
  local expected_attestation
  [[ -d "$directory" && -x "$validator" && -x "$directory/npa" ]] || {
    echo "changed-selection artifact bundle is incomplete: $directory" >&2
    return 1
  }
  provenance="$("$validator" --check-artifact-provenance "$directory")" || return 1
  [[ -n "$provenance" && "$provenance" != *$'\n'* ]] || return 1
  jq -e '
    type == "object" and
    keys_unsorted == ["schema","source_revision","benchmark_executable_sha256","npa_executable_sha256","cargo_lock_sha256","rustc_vv","cargo_profile","cargo_features","target","rustflags","benchmark_source_sha256","npa_main_source_sha256","production_source_set_sha256","git_version","build_identity_sha256"] and
    .schema == "npa.package.changed_selection.artifact_provenance.v3"
  ' <<<"$provenance" >/dev/null || return 1
  [[ "$(sha256_file "$validator")" == "$(jq -r '.benchmark_executable_sha256' <<<"$provenance")" ]] || return 1
  [[ "$(sha256_file "$npa_binary")" == "$(jq -r '.npa_executable_sha256' <<<"$provenance")" ]] || return 1
  attestation="$("$npa_binary" --build-provenance-json-v2)" || return 1
  [[ -n "$attestation" && "$attestation" != *$'\n'* ]] || return 1
  jq -e --argjson provenance "$provenance" '
    type == "object" and
    keys_unsorted == ["schema","source_revision","cargo_lock_sha256","rustc_vv","cargo_profile","target","cargo_features","rustflags","npa_main_source_sha256","production_source_set_sha256"] and
    .schema == "npa.cli.build_provenance.v2" and
    .source_revision == $provenance.source_revision and
    .cargo_lock_sha256 == $provenance.cargo_lock_sha256 and
    .rustc_vv == $provenance.rustc_vv and
    .cargo_profile == $provenance.cargo_profile and
    .target == $provenance.target and
    .cargo_features == $provenance.cargo_features and
    .rustflags == $provenance.rustflags and
    .npa_main_source_sha256 == $provenance.npa_main_source_sha256 and
    .production_source_set_sha256 == $provenance.production_source_set_sha256
  ' <<<"$attestation" >/dev/null || return 1
  expected_attestation="$(jq -cn --argjson provenance "$provenance" '
    {schema:"npa.cli.build_provenance.v2",
     source_revision:$provenance.source_revision,
     cargo_lock_sha256:$provenance.cargo_lock_sha256,
     rustc_vv:$provenance.rustc_vv,
     cargo_profile:$provenance.cargo_profile,
     target:$provenance.target,
     cargo_features:$provenance.cargo_features,
     rustflags:$provenance.rustflags,
     npa_main_source_sha256:$provenance.npa_main_source_sha256,
     production_source_set_sha256:$provenance.production_source_set_sha256}
  ')"
  [[ "$attestation" == "$expected_attestation" ]] || return 1
  printf '%s\n' "$provenance"
}

validate_changed_selection_comparison() {
  local path=$1
  local catalog_json
  local embedded_hash
  local zero_hash=0000000000000000000000000000000000000000000000000000000000000000
  local zeroed
  local computed_hash
  catalog_json="$(changed_selection_catalog_json)"
  jq -e --argjson catalog "$catalog_json" '
    type == "object"
    and keys_unsorted == ["schema","trusted","proof_evidence","catalog","run_order","records","deterministic_gate","elapsed_gate","artifact_hash"]
    and .schema == "npa.package.changed_selection.comparison.v3"
    and .trusted == false and .proof_evidence == false
    and .catalog == $catalog
    and .run_order == ["fixed128.timing-off-total","optimized.timing-off-total","optimized.timing-summary-selection","fixed128.timing-summary-selection"]
    and (.records | length == 100)
    and .deterministic_gate == "passed" and .elapsed_gate == "advisory"
    and (.artifact_hash | test("^[0-9a-f]{64}$"))
  ' "$path" >/dev/null || return 1
  local record_index=0
  local scenario
  local descriptor
  local population
  for scenario in "${CHANGED_SELECTION_CATALOG[@]}"; do
    for descriptor in fixed128.timing-off-total optimized.timing-off-total optimized.timing-summary-selection fixed128.timing-summary-selection; do
      population=${descriptor#*.}
      validate_changed_selection_run \
        <(jq -c --argjson index "$record_index" '.records[$index]' "$path") \
        "$scenario" "$population" || {
          echo "changed-selection comparison contains an invalid nested run: $descriptor $scenario" >&2
          return 1
        }
      record_index=$((record_index + 1))
    done
  done
  jq -e '
    .records as $records
    | ($records[0].provenance.artifact) as $fixed
    | ($records[1].provenance.artifact) as $optimized
    | $fixed.source_revision != $optimized.source_revision
    and all(range(0;25); . as $scenario |
      ($records[$scenario * 4].provenance.artifact == $fixed)
      and ($records[$scenario * 4 + 3].provenance.artifact == $fixed)
      and ($records[$scenario * 4 + 1].provenance.artifact == $optimized)
      and ($records[$scenario * 4 + 2].provenance.artifact == $optimized)
      and ($records[$scenario * 4].provenance.workload.deterministic_baseline_sha256
        == $records[$scenario * 4 + 3].provenance.workload.deterministic_baseline_sha256)
      and ($records[$scenario * 4 + 1].provenance.workload.deterministic_baseline_sha256
        == $records[$scenario * 4 + 2].provenance.workload.deterministic_baseline_sha256))
  ' "$path" >/dev/null || return 1
  [[ "$(<"$path")" == "$(jq -c . "$path")" ]] || {
    echo "changed-selection comparison is not canonical compact JSON" >&2
    return 1
  }
  embedded_hash="$(jq -r '.artifact_hash' "$path")"
  zeroed="$(jq -c --arg zero_hash "$zero_hash" '.artifact_hash = $zero_hash' "$path")"
  computed_hash="$(printf '%s\n' "$zeroed" | sha256_stream)"
  [[ "$embedded_hash" == "$computed_hash" ]] || {
    echo "changed-selection comparison self-hash mismatch" >&2
    return 1
  }
}

run_changed_selection_comparison() (
  local fixed_directory=$1
  local optimized_directory=$2
  local output_path=$3
  local fixture_manifest="testdata/performance/fixtures/manifest.v0.1.json"
  local fixed_baseline="$fixed_directory/changed-selection-baseline.json"
  local optimized_baseline="$optimized_directory/changed-selection-baseline.json"
  local output_directory
  local temporary_root
  local temporary_parent
  local temporary_identity
  local fixed_provenance
  local optimized_provenance
  local catalog_json
  local temporary_files=()
  local run_order='["fixed128.timing-off-total","optimized.timing-off-total","optimized.timing-summary-selection","fixed128.timing-summary-selection"]'

  command -v jq >/dev/null || { echo "jq is required for changed-selection comparison" >&2; return 1; }
  output_path="$(canonical_new_output_path "$output_path")" || return 1
  [[ -f "$fixed_baseline" && -f "$optimized_baseline" ]] || {
    echo "changed-selection bundle baseline is missing" >&2
    return 1
  }
  fixed_provenance="$(validate_changed_selection_bundle "$fixed_directory")"
  optimized_provenance="$(validate_changed_selection_bundle "$optimized_directory")"
  jq -e --argjson right "$optimized_provenance" '
    .source_revision != $right.source_revision
    and .cargo_lock_sha256 == $right.cargo_lock_sha256
    and .rustc_vv == $right.rustc_vv
    and .cargo_profile == $right.cargo_profile
    and .cargo_features == $right.cargo_features
    and .target == $right.target
    and .rustflags == $right.rustflags
    and .benchmark_source_sha256 == $right.benchmark_source_sha256
    and .npa_main_source_sha256 == $right.npa_main_source_sha256
    and .git_version == $right.git_version
  ' <<<"$fixed_provenance" >/dev/null || {
    echo "changed-selection bundles are not distinct build-comparable revisions" >&2
    return 1
  }
  [[ "$(sha256_file "$fixed_baseline")" != "$(sha256_file "$optimized_baseline")" ]] || {
    echo "changed-selection revision-local baselines must differ" >&2
    return 1
  }
  output_directory="$(dirname "$output_path")"
  IFS=$'\t' read -r temporary_root temporary_parent temporary_identity \
    < <(make_private_temp_dir "$output_directory" ".npa-changed-selection")
  trap 'if [[ -n "${temporary_root:-}" && -e "$temporary_root" ]]; then cleanup_private_temp_catalog "$temporary_root" "$temporary_parent" ".npa-changed-selection" "$temporary_identity" "${temporary_files[@]}" || true; fi' EXIT

  local records=()
  local scenario
  local descriptor
  local revision
  local population
  local directory
  local baseline
  local source_revision
  local record
  local record_path
  for scenario in "${CHANGED_SELECTION_CATALOG[@]}"; do
    for descriptor in fixed128.timing-off-total optimized.timing-off-total optimized.timing-summary-selection fixed128.timing-summary-selection; do
      revision=${descriptor%%.*}
      population=${descriptor#*.}
      if [[ "$revision" == fixed128 ]]; then
        directory=$fixed_directory
        baseline=$fixed_baseline
        source_revision="$(jq -r '.source_revision' <<<"$fixed_provenance")"
      else
        directory=$optimized_directory
        baseline=$optimized_baseline
        source_revision="$(jq -r '.source_revision' <<<"$optimized_provenance")"
      fi
      record_path="$temporary_root/record-${#records[@]}.json"
      temporary_files+=("$record_path")
      "$directory/bench_package_changed_selection" \
        --scenario "$scenario" \
        --population "$population" \
        --fixture-manifest "$fixture_manifest" \
        --deterministic-baseline "$baseline" \
        --npa-binary "$directory/npa" \
        >"$record_path"
      validate_changed_selection_run "$record_path" "$scenario" "$population" || {
        echo "invalid changed-selection run: $descriptor $scenario" >&2
        return 1
      }
      record="$(<"$record_path")"
      local expected_provenance
      local expected_baseline_hash
      if [[ "$revision" == fixed128 ]]; then
        expected_provenance=$fixed_provenance
      else
        expected_provenance=$optimized_provenance
      fi
      expected_baseline_hash="$(sha256_file "$baseline")"
      jq -e --argjson expected "$expected_provenance" --arg baseline_hash "$expected_baseline_hash" '
        .provenance.artifact == ($expected | del(.schema))
        and .provenance.workload.deterministic_baseline_sha256 == $baseline_hash
      ' <<<"$record" >/dev/null || {
        echo "changed-selection run provenance disagrees with preserved bundle: $descriptor $scenario" >&2
        return 1
      }
      records+=("$record_path")
    done
  done

  catalog_json="$(changed_selection_catalog_json)"
  local records_json
  records_json="$(jq -sc '.' "${records[@]}")"
  local placeholder="$temporary_root/comparison.placeholder.json"
  local completed="$temporary_root/comparison.completed.json"
  temporary_files+=("$placeholder" "$completed")
  local zero_hash=0000000000000000000000000000000000000000000000000000000000000000
  jq -cn --argjson catalog "$catalog_json" --argjson run_order "$run_order" --argjson records "$records_json" --arg hash "$zero_hash" \
    '{schema:"npa.package.changed_selection.comparison.v3",trusted:false,proof_evidence:false,catalog:$catalog,run_order:$run_order,records:$records,deterministic_gate:"passed",elapsed_gate:"advisory",artifact_hash:$hash}' >"$placeholder"
  local artifact_hash
  artifact_hash="$(sha256_file "$placeholder")"
  jq -c --arg artifact_hash "$artifact_hash" '.artifact_hash = $artifact_hash' "$placeholder" >"$completed"
  validate_changed_selection_comparison "$completed"
  if [[ -L "$output_path" ]] || ! ln "$completed" "$output_path"; then
    echo "refusing to replace changed-selection output: $output_path" >&2
    return 1
  fi
  echo "changed-selection comparison: $output_path"
)

run_changed_selection_default_lane() (
  local fixture_manifest="testdata/performance/fixtures/manifest.v0.1.json"
  local baseline="testdata/performance/baselines/measurements.v0.1.json"
  local benchmark="target/release/examples/bench_package_changed_selection"
  local npa="target/release/npa"
  local source_revision
  local scenario
  local population
  local record
  local paired_benchmark=""
  local paired_npa=""
  source_revision="$(/usr/bin/git rev-parse HEAD)"
  if [[ -n "$(/usr/bin/git status --porcelain --untracked-files=normal)" ]]; then
    source_revision="${source_revision}-dirty"
  fi
  NPA_BENCH_SOURCE_IDENTITY="$source_revision" cargo build --locked --offline --release \
    -p npa-cli --bin npa --example bench_package_changed_selection
  for scenario in "${CHANGED_SELECTION_CATALOG[@]}"; do
    for population in timing-off-total timing-summary-selection; do
      record="$(mktemp "${TMPDIR:-/tmp}/npa-changed-selection-run.XXXXXX")"
      trap 'rm -f -- "$record"' EXIT
      "$benchmark" --scenario "$scenario" --population "$population" \
        --fixture-manifest "$fixture_manifest" --deterministic-baseline "$baseline" \
        --npa-binary "$npa" >"$record"
      validate_changed_selection_run "$record" "$scenario" "$population"
      if [[ "$population" == timing-off-total ]]; then
        paired_benchmark="$(jq -r '.provenance.artifact.benchmark_executable_sha256' "$record")"
        paired_npa="$(jq -r '.provenance.artifact.npa_executable_sha256' "$record")"
      elif [[ "$(jq -r '.provenance.artifact.benchmark_executable_sha256' "$record")" != "$paired_benchmark" ]] ||
        [[ "$(jq -r '.provenance.artifact.npa_executable_sha256' "$record")" != "$paired_npa" ]]; then
        echo "changed-selection population pair has different executable identities: $scenario" >&2
        return 1
      fi
      jq -c . "$record"
      rm -f -- "$record"
    done
  done
)

PACKAGE_VERIFIER_PROCESS_MEMO_CATALOG=(
  package.verifier.process_memo_scope.v1.small.empty.disabled.j1.off
  package.verifier.process_memo_scope.v1.small.leaf.warm.j1.off
  package.verifier.process_memo_scope.v1.small.full.disabled.j1.off
  package.verifier.process_memo_scope.v1.small.full.disabled.j4.off
  package.verifier.process_memo_scope.v1.small.full.warm.j1.off
  package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.off
  package.verifier.process_memo_scope.v1.iut.empty.disabled.j4.summary
  package.verifier.process_memo_scope.v1.iut.leaf.warm.j1.off
  package.verifier.process_memo_scope.v1.iut.leaf.warm.j4.off
  package.verifier.process_memo_scope.v1.iut.full.warm.j1.off
  package.verifier.process_memo_scope.v1.iut.full.warm.j4.off
)

package_verifier_process_memo_catalog_json() {
  local catalog_json=""
  local scenario
  for scenario in "${PACKAGE_VERIFIER_PROCESS_MEMO_CATALOG[@]}"; do
    [[ -n "$catalog_json" ]] && catalog_json+=","
    catalog_json+="\"$scenario\""
  done
  printf '[%s]' "$catalog_json"
}

package_verifier_process_memo_summary_counters_json() {
  jq -cn '[
    ["certificate.term_compound_root_clones","count",0],
    ["certificate.term_leaf_root_clones","count",0],
    ["certificate.term_materialization_capacity_stops","count",0],
    ["certificate.term_materialization_charged_bytes","bytes",0],
    ["certificate.term_materialization_legacy_fallbacks","count",0],
    ["certificate.term_materialization_slots","count",0],
    ["certificate.term_owned_root_handoffs","count",0],
    ["certificate.term_reused_child_arcs","count",0],
    ["certificate.term_root_requests","count",0],
    ["certificate.term_selected_edges","count",0],
    ["certificate.term_unique_nodes_materialized","count",0],
    ["package.avoided_base_context_clone_bytes","bytes",0],
    ["package.avoided_base_context_clones","count",0],
    ["package.avoided_module_payload_clone_bytes","bytes",0],
    ["package.cache_results","count",0],
    ["package.certificate_bytes","bytes",0],
    ["package.coordinator_merge_elapsed","nanoseconds",0],
    ["package.dag_critical_path_layers","count",0],
    ["package.dag_layer_elapsed","nanoseconds",0],
    ["package.dag_layer_width","count",0],
    ["package.declarations","count",0],
    ["package.decode_cache_capacity_stops","count",0],
    ["package.decode_cache_hits","count",0],
    ["package.decode_cache_misses","count",0],
    ["package.decode_cache_peak_retained_bytes","bytes",0],
    ["package.decode_cache_retained_bytes","bytes",0],
    ["package.effective_jobs","count",0],
    ["package.imports","count",0],
    ["package.live_results","count",0],
    ["package.memo_results","count",0],
    ["package.module_payload_handle_clones","count",0],
    ["package.module_payload_unique_bytes","bytes",0],
    ["package.module_payloads_frozen","count",0],
    ["package.modules_checked","count",0],
    ["package.modules_decoded","count",0],
    ["package.process_memo_payload_handle_clones","count",0],
    ["package.requested_jobs","count",4],
    ["package.session_index_cow_copies","count",0],
    ["package.session_index_cow_entries","count",0],
    ["package.session_snapshot_clones","count",0],
    ["package.shard_bytes","bytes",0],
    ["package.shard_elapsed","nanoseconds",0],
    ["package.shard_estimated_cost","count",0],
    ["package.shard_modules","count",0],
    ["package.shared_base_context_bytes","bytes",0],
    ["package.worker_active_elapsed","nanoseconds",0],
    ["package.worker_idle_elapsed","nanoseconds",0]
  ] | map({label:.[0],unit:.[1],value:.[2]})'
}

validate_package_verifier_process_memo_run_record() {
  local record_path=$1
  local expected_scenario=$2
  local expected_source_identity=$3
  local expected_summary_counters
  expected_summary_counters="$(package_verifier_process_memo_summary_counters_json)"

  jq -e \
    --slurpfile memo_baseline testdata/performance/baselines/package-verifier-process-memo-scope.v0.1.json \
    --slurpfile common_baseline testdata/performance/baselines/measurements.v0.1.json \
    --argjson expected_summary_counters "$expected_summary_counters" \
    --arg scenario "$expected_scenario" \
    --arg source_identity "$expected_source_identity" '
      def sha256: type == "string" and test("^sha256:[0-9a-f]{64}$");
      def natural: type == "number" and isfinite and floor == . and . >= 0;
      def store:
        type == "object"
        and keys_unsorted == [
          "retained_entries",
          "retained_weighted_certificate_bytes",
          "cumulative_hits",
          "cumulative_misses",
          "cumulative_inserted",
          "cumulative_evicted",
          "cumulative_rejected_oversize"
        ]
        and all(.[]; natural);
      ($memo_baseline[0].scenarios[] | select(.id == $scenario)) as $expected
      | ([$common_baseline[0].scenarios[] | select(.id == $scenario) | .deterministic_counters][0] // {}) as $common_counters
      | . as $run
      | type == "object"
      and keys_unsorted == [
        "schema",
        "trusted",
        "proof_evidence",
        "scenario",
        "fixture_manifest_hash",
        "memo_scope_baseline_hash",
        "common_baseline_hash",
        "source_identity",
        "build_identity_hash",
        "cargo_lock_hash",
        "harness_source_hash",
        "production_source_set_hash",
        "rustc_vv",
        "cargo_profile",
        "target",
        "features",
        "rustflags",
        "verifier",
        "cache_policy",
        "warmup",
        "sample_count",
        "profile",
        "samples",
        "elapsed_summary_ns",
        "elapsed_profile",
        "elapsed_gate",
        "status",
        "measurements"
      ]
      and .schema == "npa.package_verifier.process_memo_scope.run.v0.2"
      and .trusted == false
      and .proof_evidence == false
      and .scenario == $scenario
      and (.fixture_manifest_hash | sha256)
      and (.memo_scope_baseline_hash | sha256)
      and (.common_baseline_hash == null or (.common_baseline_hash | sha256))
      and .source_identity == $source_identity
      and (.source_identity | test("^[0-9a-f]{40}(-dirty)?$"))
      and (.build_identity_hash | sha256)
      and (.cargo_lock_hash | sha256)
      and (.harness_source_hash | sha256)
      and (.production_source_set_hash | sha256)
      and (.rustc_vv | type == "string" and length > 0)
      and .cargo_profile == "release"
      and (.target | type == "string" and length > 0)
      and (.features | type == "array")
      and .features == (.features | sort | unique)
      and all(.features[]; type == "string")
      and (.rustflags | type == "string")
      and .verifier == "fast"
      and .cache_policy == "disabled"
      and .warmup == 1
      and .sample_count == 7
      and (.profile | type == "object")
      and (.profile | keys_unsorted == ["selection", "jobs", "measurement_mode", "memo"])
      and (.profile.selection | type == "object")
      and (.profile.selection | keys_unsorted == ["kind", "module", "closure_module_count", "closure_certificate_bytes"])
      and (.profile.selection.kind == "empty"
        or .profile.selection.kind == "leaf"
        or .profile.selection.kind == "full")
      and ((.profile.selection.kind == "leaf" and (.profile.selection.module | type == "string" and length > 0))
        or (.profile.selection.kind != "leaf" and .profile.selection.module == null))
      and (.profile.selection.closure_module_count | natural)
      and (.profile.selection.closure_certificate_bytes | natural)
      and (.profile.jobs | natural and . > 0)
      and (.profile.measurement_mode == "off" or .profile.measurement_mode == "summary")
      and (.profile.memo | type == "object")
      and (.profile.memo | keys_unsorted == ["mode", "max_entries", "max_weighted_certificate_bytes"])
      and .profile == {selection:$expected.selection,jobs:$expected.jobs,measurement_mode:$expected.measurement_mode,memo:$expected.memo}
      and ((.profile.memo.mode == "disabled"
          and .profile.memo.max_entries == null
          and .profile.memo.max_weighted_certificate_bytes == null)
        or (.profile.memo.mode == "warm"
          and (.profile.memo.max_entries | natural and . > 0)
          and (.profile.memo.max_weighted_certificate_bytes | natural and . > 0)))
      and (.samples | type == "array" and length == 7)
      and [.samples[].index] == [0, 1, 2, 3, 4, 5, 6]
      and all(.samples[];
        type == "object"
        and keys_unsorted == ["index", "elapsed_ns", "status", "executed_module_count", "memo_counters", "store_stats"]
        and (.elapsed_ns | natural)
        and .status == "passed"
        and (.executed_module_count | natural)
        and (.memo_counters | type == "object")
        and (.memo_counters | keys_unsorted == [
          "hits",
          "misses",
          "inserted",
          "keys_built",
          "certificate_bytes_hashed",
          "evicted",
          "rejected_oversize",
          "bypassed_store_unavailable"
        ])
        and all(.memo_counters[]; natural)
        and .memo_counters == $expected.measured_run_memo_counters
        and (.store_stats == null or (.store_stats | store))
        and (if $expected.post_warmup_store == null then .store_stats == null
             else .store_stats == ($expected.post_warmup_store + {cumulative_hits:($expected.post_warmup_store.cumulative_hits + (($expected.selection.closure_module_count) * (.index + 1)))}) end))
      and (.elapsed_summary_ns | type == "object")
      and (.elapsed_summary_ns | keys_unsorted == ["median", "median_absolute_deviation", "minimum", "maximum"])
      and all(.elapsed_summary_ns[]; natural)
      and .elapsed_profile == null
      and .elapsed_gate == "advisory"
      and .status == "passed"
      and ((.profile.measurement_mode == "off"
          and .common_baseline_hash == null
          and .measurements == null)
        or (.profile.measurement_mode == "summary"
          and (.common_baseline_hash | sha256)
          and (.measurements | type == "object"
            and keys_unsorted == ["schema","trusted","proof_evidence","mode","input_identity","counters","modules","module_details","declarations","declaration_details","candidates","candidate_details","workers","worker_details","package_sharding","package_layers","package_layer_details","package_shards","package_shard_details","detail_truncated","overflowed","clock"]
            and .schema == "npa.performance.measurements.v0.9" and .trusted == false and .proof_evidence == false and .mode == "summary"
            and (.input_identity | sha256)
            and .counters == $expected_summary_counters
            and all($common_counters|to_entries[]; . as $entry | any($expected_summary_counters[]; .label==$entry.key and .value==$entry.value))
            and (.modules == []) and .module_details == {attempted:0,retained:0,omitted:0}
            and (.declarations == []) and .declaration_details == {attempted:0,retained:0,omitted:0}
            and (.candidates == []) and .candidate_details == {attempted:0,retained:0,omitted:0}
            and (.workers == []) and .worker_details == {attempted:0,retained:0,omitted:0}
            and .package_sharding == null
            and (.package_layers == []) and .package_layer_details == {attempted:0,retained:0,omitted:0}
            and (.package_shards == []) and .package_shard_details == {attempted:0,retained:0,omitted:0}
            and .detail_truncated == false and .overflowed == false
            and .clock == {source:"std.monotonic.instant",resolution_ns:1,coarse_stage_reads:0})))
      and all(.. | strings; startswith("/") | not)
    ' "$record_path" >/dev/null || return 1
}

validate_package_verifier_process_memo_matrix() {
  local matrix_path=$1
  local catalog_json
  local contents
  local canonical
  local embedded_hash
  local zero_hash="sha256:0000000000000000000000000000000000000000000000000000000000000000"
  local zeroed
  local computed_hash

  catalog_json="$(package_verifier_process_memo_catalog_json)"
  jq -e --argjson catalog "$catalog_json" '
      type == "object"
      and keys_unsorted == ["schema", "catalog", "passes", "records", "artifact_hash"]
      and .schema == "npa.package_verifier.process_memo_scope.matrix.v0.1"
      and .catalog == $catalog
      and .passes == ["forward", "reverse"]
      and (.records | type == "array" and length == 22)
      and [.records[].scenario] == ($catalog + ($catalog | reverse))
      and all(.records[];
        type == "object"
        and .schema == "npa.package_verifier.process_memo_scope.run.v0.2")
      and ([.records[].source_identity] | unique | length) == 1
      and ([.records[].build_identity_hash] | unique | length) == 1
      and ([.records[].cargo_lock_hash] | unique | length) == 1
      and ([.records[].harness_source_hash] | unique | length) == 1
      and ([.records[].production_source_set_hash] | unique | length) == 1
      and ([.records[].rustc_vv] | unique | length) == 1
      and ([.records[].cargo_profile] | unique | length) == 1
      and ([.records[].target] | unique | length) == 1
      and ([.records[].features] | unique | length) == 1
      and ([.records[].rustflags] | unique | length) == 1
      and (.artifact_hash | type == "string" and test("^sha256:[0-9a-f]{64}$"))
      and all(.. | strings; startswith("/") | not)
  ' "$matrix_path" >/dev/null || return 1

  local record_index=0
  local scenario
  local validation_root
  local validation_parent
  local validation_identity
  IFS=$'\t' read -r validation_root validation_parent validation_identity \
    < <(make_private_temp_dir "${TMPDIR:-/tmp}" "npa-process-memo-validator")
  while IFS= read -r scenario; do
    local record_path="$validation_root/${record_index}.json"
    (umask 077; set -o noclobber; jq -c --argjson index "$record_index" '.records[$index]' "$matrix_path" >"$record_path") || { rm -f -- "$record_path"; guarded_remove_private_temp_dir "$validation_root" "$validation_parent" "npa-process-memo-validator" "$validation_identity" || true; return 1; }
    if ! validate_package_verifier_process_memo_run_record \
      "$record_path" "$scenario" "$(jq -r '.records[0].source_identity' "$matrix_path")"; then
      rm -f -- "$record_path"
      guarded_remove_private_temp_dir "$validation_root" "$validation_parent" "npa-process-memo-validator" "$validation_identity" || true
      echo "process-memo matrix contains an invalid nested run: $scenario" >&2
      return 1
    fi
    rm -f -- "$record_path"
    record_index=$((record_index + 1))
  done < <(jq -r '.catalog[]' "$matrix_path"; \
    jq -r '.catalog | reverse[]' "$matrix_path")
  guarded_remove_private_temp_dir "$validation_root" "$validation_parent" "npa-process-memo-validator" "$validation_identity"

  contents="$(<"$matrix_path")"
  canonical="$(jq -c . "$matrix_path")"
  if [[ "$contents" != "$canonical" ]]; then
    echo "process-memo matrix is not canonical compact JSON: $matrix_path" >&2
    return 1
  fi
  embedded_hash="$(jq -r '.artifact_hash' "$matrix_path")"
  zeroed="$(jq -c --arg zero_hash "$zero_hash" '.artifact_hash = $zero_hash' "$matrix_path")"
  computed_hash="sha256:$(printf '%s' "$zeroed" | sha256_stream)"
  if [[ "$embedded_hash" != "$computed_hash" ]]; then
    echo "process-memo matrix self-hash mismatch: $matrix_path" >&2
    return 1
  fi
}

run_package_verifier_process_memo_matrix() (
  local iut_root=$1
  local output_path=$2
  local output_directory
  local benchmark_binary="${NPA_PROCESS_MEMO_BENCH_BINARY:-target/release/examples/bench_package_verifier}"
  local fixture_manifest="testdata/performance/fixtures/manifest.v0.1.json"
  local memo_baseline="testdata/performance/baselines/package-verifier-process-memo-scope.v0.1.json"
  local common_baseline="testdata/performance/baselines/measurements.v0.1.json"
  local source_identity
  local temporary_root
  local temporary_parent
  local temporary_identity
  local placeholder_path
  local completed_path
  local artifact_hash
  local first_identity=""
  local first_build=""
  local first_lock=""
  local first_harness=""
  local first_source_set=""
  local first_rustc=""
  local first_profile=""
  local first_target=""
  local first_features=""
  local first_rustflags=""
  local temporary_files=()

  command -v jq >/dev/null || {
    echo "jq is required for the process-memo matrix lane" >&2
    return 1
  }

  output_path="$(canonical_new_output_path "$output_path")" || return 1
  if [[ ! -d "$iut_root" ]]; then
    echo "process-memo IUT root is not a directory: $iut_root" >&2
    return 1
  fi
  source_identity="$(/usr/bin/git rev-parse HEAD)"
  if [[ -n "$(/usr/bin/git status --porcelain --untracked-files=normal)" ]]; then
    source_identity="${source_identity}-dirty"
  fi
  if [[ "${NPA_PROCESS_MEMO_SKIP_BUILD:-0}" != 1 ]]; then
    NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release \
      -p npa-api --example bench_package_verifier
  fi
  if [[ ! -x "$benchmark_binary" ]]; then
    echo "process-memo benchmark executable is unavailable: $benchmark_binary" >&2
    return 1
  fi

  output_directory="$(dirname "$output_path")"
  IFS=$'\t' read -r temporary_root temporary_parent temporary_identity \
    < <(make_private_temp_dir "$output_directory" ".npa-process-memo-matrix")
  trap 'if [[ -n "${temporary_root:-}" && -e "$temporary_root" ]]; then cleanup_private_temp_catalog "$temporary_root" "$temporary_parent" ".npa-process-memo-matrix" "$temporary_identity" "${temporary_files[@]}" || true; fi' EXIT

  local catalog=("${PACKAGE_VERIFIER_PROCESS_MEMO_CATALOG[@]}")
  local reverse_catalog=()
  local index
  for ((index=${#catalog[@]} - 1; index >= 0; index--)); do
    reverse_catalog+=("${catalog[index]}")
  done

  local record_paths=()
  local pass
  local scenario
  local record_path
  local record
  local observed
  for pass in forward reverse; do
    local selected_catalog=()
    if [[ "$pass" == forward ]]; then
      selected_catalog=("${catalog[@]}")
    else
      selected_catalog=("${reverse_catalog[@]}")
    fi
    for scenario in "${selected_catalog[@]}"; do
      record_path="$temporary_root/${pass}-${#record_paths[@]}.json"
      temporary_files+=("$record_path")
      "$benchmark_binary" \
        --fixture-manifest "$fixture_manifest" \
        --baseline "$common_baseline" \
        --memo-scope-baseline "$memo_baseline" \
        --memo-scope-iut-root "$iut_root" \
        --source-identity "$source_identity" \
        --scenario "$scenario" \
        --warmup 1 \
        --samples 7 >"$record_path"
      record="$(<"$record_path")"
      if ! validate_package_verifier_process_memo_run_record \
        "$record_path" "$scenario" "$source_identity"; then
        echo "invalid process-memo run record for $scenario ($pass)" >&2
        return 1
      fi
      for field in source_identity build_identity_hash cargo_lock_hash harness_source_hash production_source_set_hash rustc_vv cargo_profile target rustflags; do
        observed="$(jq -c ".$field" "$record_path")"
        if [[ -z "$observed" ]]; then
          echo "process-memo record is missing $field: $scenario" >&2
          return 1
        fi
        case "$field" in
          source_identity) [[ -z "$first_identity" ]] && first_identity=$observed; [[ "$observed" == "$first_identity" ]] || return 1 ;;
          build_identity_hash) [[ -z "$first_build" ]] && first_build=$observed; [[ "$observed" == "$first_build" ]] || return 1 ;;
          cargo_lock_hash) [[ -z "$first_lock" ]] && first_lock=$observed; [[ "$observed" == "$first_lock" ]] || return 1 ;;
          harness_source_hash) [[ -z "$first_harness" ]] && first_harness=$observed; [[ "$observed" == "$first_harness" ]] || return 1 ;;
          production_source_set_hash) [[ -z "$first_source_set" ]] && first_source_set=$observed; [[ "$observed" == "$first_source_set" ]] || return 1 ;;
          rustc_vv) [[ -z "$first_rustc" ]] && first_rustc=$observed; [[ "$observed" == "$first_rustc" ]] || return 1 ;;
          cargo_profile) [[ -z "$first_profile" ]] && first_profile=$observed; [[ "$observed" == "$first_profile" ]] || return 1 ;;
          target) [[ -z "$first_target" ]] && first_target=$observed; [[ "$observed" == "$first_target" ]] || return 1 ;;
          rustflags) [[ -z "$first_rustflags" ]] && first_rustflags=$observed; [[ "$observed" == "$first_rustflags" ]] || return 1 ;;
        esac
      done
      observed="$(jq -c '.features' "$record_path")"
      [[ -z "$first_features" ]] && first_features=$observed
      if [[ -z "$observed" || "$observed" != "$first_features" ]]; then
        echo "process-memo record feature identity disagrees: $scenario" >&2
        return 1
      fi
      jq -c '{scenario,source_identity,build_identity_hash,cargo_lock_hash,harness_source_hash,production_source_set_hash,rustc_vv,cargo_profile,target,features,rustflags,profile,samples:[.samples[]|{index,memo_counters}],elapsed_summary_ns}' \
        "$record_path"
      record_paths+=("$record_path")
    done
  done

  local catalog_json=""
  for scenario in "${catalog[@]}"; do
    [[ -n "$catalog_json" ]] && catalog_json+=","
    catalog_json+="\"$scenario\""
  done
  local records_json=""
  for record_path in "${record_paths[@]}"; do
    [[ -n "$records_json" ]] && records_json+=","
    records_json+="$(<"$record_path")"
  done
  placeholder_path="$temporary_root/matrix.placeholder.json"
  temporary_files+=("$placeholder_path")
  printf '{"schema":"npa.package_verifier.process_memo_scope.matrix.v0.1","catalog":[%s],"passes":["forward","reverse"],"records":[%s],"artifact_hash":"sha256:%064d"}' \
    "$catalog_json" "$records_json" 0 >"$placeholder_path"
  artifact_hash="$(sha256_file "$placeholder_path")"
  completed_path="$temporary_root/matrix.completed.json"
  temporary_files+=("$completed_path")
  sed "s/sha256:0000000000000000000000000000000000000000000000000000000000000000/sha256:$artifact_hash/" \
    "$placeholder_path" >"$completed_path"
  validate_package_verifier_process_memo_matrix "$completed_path"
  if [[ -L "$output_path" ]] || ! ln "$completed_path" "$output_path"; then
    echo "refusing to replace existing process-memo matrix output: $output_path" >&2
    return 1
  fi
  echo "package-verifier process-memo matrix: $output_path"
)

run_package_artifact_snapshot_matrix() (
  local published_directory=$1
  local benchmark_binary="${NPA_SNAPSHOT_BENCH_BINARY:-target/release/examples/bench_package_artifact_snapshot}"
  local measure_binary="${NPA_MEASURE_PROCESS_BINARY:-target/release/examples/measure_process}"
  local fixture_manifest="testdata/performance/fixtures/manifest.v0.2.json"
  local baseline="testdata/performance/baselines/measurements.v0.1.json"
  local oracle="testdata/performance/fixture-generator.v1.tsv"
  local source_identity
  local matrix_hash

  published_directory="$(canonical_new_output_path "$published_directory")" || return 1
  source_identity="$(current_source_identity)" || return 1
  if [[ "${NPA_SNAPSHOT_SKIP_BUILD:-0}" != 1 ]]; then
    NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-cli \
      --example bench_package_artifact_snapshot --example measure_process || return 1
  fi
  [[ -x "$benchmark_binary" && -x "$measure_binary" ]] || {
    echo "snapshot benchmark or process-measurement executable is unavailable" >&2
    return 1
  }
  matrix_hash="$("$measure_binary" --run-snap-vmsp-controller \
    --kind snapshot \
    --manifest "$fixture_manifest" \
    --baseline "$baseline" \
    --oracle "$oracle" \
    --benchmark "$benchmark_binary" \
    --source-identity "$source_identity" \
    --output "$published_directory")" || return 1
  require_snap_vmsp_controller_matrix_digest snapshot "$matrix_hash" || return 1
  "$measure_binary" --validate-snap-vmsp-sealed-run \
    --kind snapshot \
    --manifest "$fixture_manifest" \
    --baseline "$baseline" \
    --oracle "$oracle" \
    --benchmark "$benchmark_binary" \
    --source-identity "$source_identity" \
    --output "$published_directory" || return 1
  echo "snapshot matrix sha256: $matrix_hash"
)

run_shared_payload_matrix() (
  local published_directory=$1
  local benchmark_binary="${NPA_SHARED_PAYLOAD_BENCH_BINARY:-target/release/examples/bench_shared_payload}"
  local measure_binary="${NPA_MEASURE_PROCESS_BINARY:-target/release/examples/measure_process}"
  local fixture_manifest="testdata/performance/fixtures/manifest.v0.2.json"
  local baseline="testdata/performance/baselines/measurements.v0.1.json"
  local oracle="testdata/performance/fixture-generator.v1.tsv"
  local source_identity
  local matrix_hash

  published_directory="$(canonical_new_output_path "$published_directory")" || return 1
  source_identity="$(current_source_identity)" || return 1
  if [[ "${NPA_SHARED_PAYLOAD_SKIP_BUILD:-0}" != 1 ]]; then
    NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-api \
      --example bench_shared_payload || return 1
    NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-cli \
      --example measure_process || return 1
  fi
  [[ -x "$benchmark_binary" && -x "$measure_binary" ]] || {
    echo "shared-payload benchmark or process-measurement executable is unavailable" >&2
    return 1
  }
  matrix_hash="$("$measure_binary" --run-snap-vmsp-controller \
    --kind shared-payload \
    --manifest "$fixture_manifest" \
    --baseline "$baseline" \
    --oracle "$oracle" \
    --benchmark "$benchmark_binary" \
    --source-identity "$source_identity" \
    --output "$published_directory")" || return 1
  require_snap_vmsp_controller_matrix_digest shared-payload "$matrix_hash" || return 1
  "$measure_binary" --validate-snap-vmsp-sealed-run \
    --kind shared-payload \
    --manifest "$fixture_manifest" \
    --baseline "$baseline" \
    --oracle "$oracle" \
    --benchmark "$benchmark_binary" \
    --source-identity "$source_identity" \
    --output "$published_directory" || return 1
  echo "shared-payload matrix sha256: $matrix_hash"
)

run_term_dag_materialization_matrix() (
  local output_path=$1
  local manifest
  local baseline
  local checked_root
  local measure_process
  local source_identity
  local generated_root
  local generated_parent
  local generated_identity

  manifest="$(cd testdata/performance/fixtures && pwd -P)/certificate-term-dag-materialization.v0.1.json"
  baseline="$(cd testdata/performance/baselines && pwd -P)/certificate-term-dag-materialization.measurements.v0.1.json"
  checked_root="$(cd testdata/performance && pwd -P)/certificate-term-dag-materialization"
  output_path="$(canonical_new_output_path "$output_path")"
  measure_process="$(pwd -P)/target/release/examples/measure_process"
  source_identity="$(current_source_identity)"

  [[ ! -e "$output_path" ]] || {
    echo "refusing to replace term-DAG report: $output_path" >&2
    return 1
  }
  IFS=$'\t' read -r generated_root generated_parent generated_identity \
    < <(make_private_temp_dir "${TMPDIR:-/tmp}" "npa-tdag-fixtures")
  trap 'if [[ -n "${generated_root:-}" && -e "$generated_root" ]]; then guarded_remove_private_temp_dir "$generated_root" "$generated_parent" "npa-tdag-fixtures" "$generated_identity" || true; fi' EXIT

  cargo test --locked --offline -p npa-api \
    --example generate_certificate_term_dag_materialization_fixtures || return $?
  cargo test --locked --offline -p npa-api \
    --example bench_certificate_term_dag_materialization || return $?
  cargo build --locked --offline -p npa-api \
    --example generate_certificate_term_dag_materialization_fixtures || return $?
  target/debug/examples/generate_certificate_term_dag_materialization_fixtures \
    --output "$generated_root" || return $?
  diff -ru "$checked_root" "$generated_root" || return $?
  target/debug/examples/generate_certificate_term_dag_materialization_fixtures \
    --clean-output "$generated_root" || return $?
  generated_root=""
  NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-api \
    --example bench_certificate_term_dag_materialization || return $?
  NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-cli \
    --example measure_process || return $?
  target/release/examples/bench_certificate_term_dag_materialization \
    --validate-all --manifest "$manifest" --baseline "$baseline" || return $?
  target/release/examples/bench_certificate_term_dag_materialization \
    --controller --manifest "$manifest" --baseline "$baseline" \
    --measure-process "$measure_process" \
    --output "$output_path" || return $?
  target/release/examples/bench_certificate_term_dag_materialization \
    --validate-report --manifest "$manifest" --baseline "$baseline" \
    --measure-process "$measure_process" \
    --output "$output_path" || return $?
  echo "certificate term-DAG report: $output_path (elapsed/RSS advisory)"
)

if [[ "${BASH_SOURCE[0]}" != "$0" ]]; then
  return 0
fi

if [[ $# -gt 0 ]]; then
  if [[ ${1:-} == "--test-targeted-build-certs-controlled-error" ]]; then
    shift
    [[ $# -eq 1 ]] || {
      echo "--test-targeted-build-certs-controlled-error requires the benchmark executable" >&2
      exit 2
    }
    targeted_error_output="$("$1" --invalid-private-test-argument 2>&1)" && {
      echo "targeted build-certs benchmark accepted invalid arguments" >&2
      exit 1
    }
    targeted_error_status=$?
    [[ "$targeted_error_status" -eq 2 ]] || {
      echo "targeted build-certs benchmark did not use controlled exit 2" >&2
      exit 1
    }
    [[ "$targeted_error_output" == "targeted build-certs benchmark failed: usage:"* ]] || {
      echo "targeted build-certs benchmark emitted an unexpected diagnostic" >&2
      exit 1
    }
    [[ "$targeted_error_output" != *panicked* && "$(printf '%s\n' "$targeted_error_output" | wc -l | tr -d ' ')" -eq 1 ]] || {
      echo "targeted build-certs benchmark emitted a panic or multiline diagnostic" >&2
      exit 1
    }
    exit 0
  fi
  process_memo_iut_root=""
  process_memo_output=""
  whnf_elapsed_profile=""
  changed_selection_fixed=""
  changed_selection_optimized=""
  changed_selection_output=""
  term_dag_requested=false
  term_dag_output=""
  snapshot_requested=false
  shared_payload_requested=false
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --help)
        cat <<'EOF'
Usage:
  scripts/check-performance.sh
  scripts/check-performance.sh --changed-selection-compare <fixed128-dir> <optimized-dir> --output <path>
  scripts/check-performance.sh --term-dag-materialization --output <path>
  scripts/check-performance.sh --package-artifact-snapshot --output <directory>
  scripts/check-performance.sh --shared-payload --output <directory>
  scripts/check-performance.sh --package-verifier-process-memo-iut-root <root> --output <path>
  scripts/check-performance.sh --elapsed-profile <path> --output <path>
EOF
        exit
        ;;
      --changed-selection-compare)
        [[ $# -ge 3 ]] || { echo "missing two directories for $1" >&2; exit 2; }
        [[ -z "$changed_selection_fixed" && -z "$changed_selection_optimized" ]] || {
          echo "duplicate $1" >&2
          exit 2
        }
        changed_selection_fixed=$2
        changed_selection_optimized=$3
        shift 3
        ;;
      --package-verifier-process-memo-iut-root)
        [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
        process_memo_iut_root=$2
        shift 2
        ;;
      --term-dag-materialization)
        [[ "$term_dag_requested" == false ]] || { echo "duplicate $1" >&2; exit 2; }
        term_dag_requested=true
        shift
        ;;
      --package-artifact-snapshot)
        [[ "$snapshot_requested" == false ]] || { echo "duplicate $1" >&2; exit 2; }
        snapshot_requested=true
        shift
        ;;
      --shared-payload)
        [[ "$shared_payload_requested" == false ]] || { echo "duplicate $1" >&2; exit 2; }
        shared_payload_requested=true
        shift
        ;;
      --output)
        [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
        [[ -z "$process_memo_output" && -z "$changed_selection_output" && -z "$term_dag_output" ]] || {
          echo "duplicate --output" >&2
          exit 2
        }
        process_memo_output=$2
        changed_selection_output=$2
        term_dag_output=$2
        shift 2
        ;;
      --elapsed-profile)
        [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
        whnf_elapsed_profile=$2
        shift 2
        ;;
      *)
        echo "unknown performance option: $1" >&2
        exit 2
        ;;
    esac
  done
  if [[ -n "$changed_selection_fixed" || -n "$changed_selection_optimized" ]]; then
    if [[ -n "$process_memo_iut_root" || -n "$whnf_elapsed_profile" || "$term_dag_requested" == true || "$snapshot_requested" == true || "$shared_payload_requested" == true ]]; then
      echo "--changed-selection-compare cannot be combined with another performance lane" >&2
      exit 2
    fi
    if [[ -z "$changed_selection_fixed" || -z "$changed_selection_optimized" || -z "$changed_selection_output" ]]; then
      echo "changed-selection comparison requires two directories and --output" >&2
      exit 2
    fi
    run_changed_selection_comparison \
      "$changed_selection_fixed" "$changed_selection_optimized" "$changed_selection_output" || exit $?
    exit 0
  fi
  if [[ "$term_dag_requested" == true ]]; then
    if [[ -n "$process_memo_iut_root" || -n "$whnf_elapsed_profile" || "$snapshot_requested" == true || "$shared_payload_requested" == true ]]; then
      echo "--term-dag-materialization cannot be combined with another performance lane" >&2
      exit 2
    fi
    [[ -n "$term_dag_output" ]] || {
      echo "--term-dag-materialization requires --output" >&2
      exit 2
    }
    run_term_dag_materialization_matrix "$term_dag_output" || exit $?
    exit 0
  fi
  if [[ "$snapshot_requested" == true || "$shared_payload_requested" == true ]]; then
    if [[ "$snapshot_requested" == true && "$shared_payload_requested" == true ]] ||
      [[ -n "$process_memo_iut_root" || -n "$whnf_elapsed_profile" ]]; then
      echo "the snapshot/shared-payload lane cannot be combined with another performance lane" >&2
      exit 2
    fi
    [[ -n "$process_memo_output" ]] || {
      echo "the snapshot/shared-payload lane requires --output" >&2
      exit 2
    }
    if [[ "$snapshot_requested" == true ]]; then
      run_package_artifact_snapshot_matrix "$process_memo_output" || exit $?
    else
      run_shared_payload_matrix "$process_memo_output" || exit $?
    fi
    exit 0
  fi
  if [[ -n "$whnf_elapsed_profile" ]]; then
    if [[ -n "$process_memo_iut_root" ]]; then
      echo "--elapsed-profile cannot be combined with the process-memo lane" >&2
      exit 2
    fi
    [[ -n "$process_memo_output" ]] || {
      echo "--elapsed-profile requires --output" >&2
      exit 2
    }
    run_whnf_elapsed_profile_report "$whnf_elapsed_profile" "$process_memo_output" || exit $?
    exit 0
  fi
  if [[ -z "$process_memo_iut_root" || -z "$process_memo_output" ]]; then
    echo "the process-memo lane requires --package-verifier-process-memo-iut-root and --output" >&2
    exit 2
  fi
  run_package_verifier_process_memo_matrix "$process_memo_iut_root" "$process_memo_output" || exit $?
  exit 0
fi

echo "[1/11] Build performance harnesses (locked, offline)"
source_identity="$(current_source_identity)"
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline -p npa-api --example bench_package_verifier
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline -p npa-api --example bench_true_batching
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline -p npa-api --example bench_whnf_application_spine
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline -p npa-api --example check_whnf_application_spine_package
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-api --example bench_shared_payload
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline -p npa-cli --example targeted_build_certs_bench
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-cli --example measure_process

echo "[2/11] Verify deterministic observability contracts"
cargo test --locked --offline -p npa-api performance_measurement
cargo test --locked --offline -p npa-api performance_gate
cargo test --locked --offline -p npa-api opaque_definition_performance
cargo test --locked --offline -p npa-api tactic_batch_deterministic_counter_gate_covers_required_candidate_counts
cargo test --locked --offline -p npa-cert prepared_candidate_chain_counters_cover_required_candidate_counts
cargo test --locked --offline -p npa-cert opaque_definition_determinism
cargo test --locked --offline -p npa-kernel optional_work_meter
cargo test --locked --offline -p npa-kernel whnf_machine_
cargo test --locked --offline -p npa-api --example bench_whnf_application_spine
cargo test --locked --offline -p npa-api --example check_whnf_application_spine_package
cargo test --locked --offline -p npa-api --example bench_shared_payload
cargo test --locked --offline -p npa-cli targeted_build_certs_bench_fixture

whnf_fixture="testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
whnf_baseline="testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
while IFS= read -r whnf_scenario; do
  case "$whnf_scenario" in
    checked-package.*) continue ;;
  esac
  target/debug/examples/bench_whnf_application_spine \
    --child \
    --phase candidate \
    --fixture-manifest "$whnf_fixture" \
    --baseline "$whnf_baseline" \
    --scenario-id "$whnf_scenario" \
    --sample-index 0 >/dev/null
done < <(target/debug/examples/bench_whnf_application_spine \
  --fixture-manifest "$whnf_fixture" \
  --baseline "$whnf_baseline" \
  --list)
target/debug/examples/check_whnf_application_spine_package \
  --root testdata/package/proofs \
  --fixture-manifest "$whnf_fixture" \
  --baseline "$whnf_baseline" \
  --kernel-mode compare >/dev/null

echo "[3/11] Run compact checked-artifact fixture"
performance_output="$(target/debug/examples/bench_package_verifier \
  --root testdata/package/npa-std \
  --fixture-manifest testdata/performance/fixtures/manifest.v0.1.json \
  --baseline testdata/performance/baselines/measurements.v0.1.json \
  --source-identity "$source_identity" \
  --mode fast \
  --measurements detailed \
  --scenario compact-package-fast \
  --warmup 1 \
  --samples 3)"
performance_dir="$(mktemp -d "${TMPDIR:-/tmp}/npa-performance.XXXXXX")"
performance_path="$performance_dir/compact-package-fast.json"
printf '%s\n' "$performance_output" > "$performance_path"

target/debug/examples/bench_package_verifier \
  --root testdata/package/npa-std \
  --fixture-manifest testdata/performance/fixtures/manifest.v0.1.json \
  --baseline testdata/performance/baselines/measurements.v0.1.json \
  --source-identity "$source_identity" \
  --mode fast \
  --measurements detailed \
  --scenario compact-package-fast \
  --warmup 1 \
  --samples 3 \
  --validate-legacy-report "$performance_path"

echo "$performance_output"
echo "performance report: $performance_path"

echo "[4/11] Run immutable shared-payload fixture matrix"
shared_payload_dir="$performance_dir/shared-payload"
run_shared_payload_matrix "$shared_payload_dir"
echo "shared-payload reports: $shared_payload_dir"

echo "[5/11] Run proof-authoring true-batching fixtures"
true_batching_output="$(target/debug/examples/bench_true_batching \
  --source-identity "$source_identity" \
  --warmup 1 \
  --samples 3)"
true_batching_path="$performance_dir/true-batching.json"
printf '%s\n' "$true_batching_output" > "$true_batching_path"

target/debug/examples/bench_true_batching \
  --source-identity "$source_identity" \
  --warmup 1 \
  --samples 3 \
  --validate-report "$true_batching_path"

echo "$true_batching_output"
echo "true-batching report: $true_batching_path"

echo "[6/11] Run fresh-process targeted build-certs rollout matrix"
targeted_build_certs_output="$(target/debug/examples/targeted_build_certs_bench \
  --scenario all \
  --verify)"
targeted_build_certs_path="$performance_dir/targeted-build-certs-rollout.json"
printf '%s\n' "$targeted_build_certs_output" >"$targeted_build_certs_path"
target/debug/examples/targeted_build_certs_bench \
  --validate-report "$targeted_build_certs_path"

echo "$targeted_build_certs_output"
echo "targeted build-certs report: $targeted_build_certs_path"

echo "[7/11] Run changed-selection paired populations"
run_changed_selection_default_lane

echo "[8/11] Run certificate term-DAG materialization matrix"
run_term_dag_materialization_matrix \
  "$performance_dir/certificate-term-dag-materialization.run.v0.2.json"

echo "[9/11] Run operation-owned artifact snapshot matrix"
run_package_artifact_snapshot_matrix "$performance_dir/package-artifact-snapshot"

echo "[10/11] Prebuild release npa-cli outside the measured interval"
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline --release -p npa-cli --bin npa --example measure_process

echo "[11/11] Run kernel-fuel authoring rollout scenario"
kernel_fuel_binary="target/release/npa"
kernel_fuel_measure="target/release/examples/measure_process"
kernel_fuel_package="testdata/package/proofs"
kernel_fuel_samples=5
kernel_fuel_raw="$performance_dir/kernel-fuel-authoring-samples.tsv"
kernel_fuel_summary="$performance_dir/kernel-fuel-authoring-summary.tsv"
kernel_fuel_package_before="$performance_dir/kernel-fuel-package.before"
kernel_fuel_package_after="$performance_dir/kernel-fuel-package.after"
printf 'series\tfuel\tround\twall_seconds\tpeak_rss_kib\n' >"$kernel_fuel_raw"

snapshot_kernel_fuel_package() {
  snapshot_tree_sha256 "$kernel_fuel_package"
}

run_kernel_fuel_command() {
  local fuel_mode=$1
  local timing_mode=$2
  local output_path=$3
  "$kernel_fuel_binary" package build-certs \
    --root "$kernel_fuel_package" \
    --check \
    --build-check-cache off \
    --kernel-fuel-report "$fuel_mode" \
    --timings "$timing_mode" \
    --json >"$output_path"
}

measure_kernel_fuel_command() {
  local series=$1
  local fuel_mode=$2
  local timing_mode=$3
  local round=$4
  local output_path="$performance_dir/kernel-fuel-${series}-${fuel_mode}-${round}.json"
  local time_path="$performance_dir/kernel-fuel-${series}-${fuel_mode}-${round}.time"
  local measurement
  local wall_seconds
  local peak_rss_kib
  local exit_code

  measurement="$("$kernel_fuel_measure" \
    --output "$output_path" \
    --stderr "$time_path" \
    -- "$kernel_fuel_binary" package build-certs \
    --root "$kernel_fuel_package" \
    --check \
    --build-check-cache off \
    --kernel-fuel-report "$fuel_mode" \
    --timings "$timing_mode" \
    --json)"
  IFS=$'\t' read -r wall_seconds peak_rss_kib exit_code <<<"$measurement"

  if [[ -z "$wall_seconds" || -z "$peak_rss_kib" || "$exit_code" != 0 ]] ||
    [[ $(<"$output_path") != *'"status":"passed"'* ]]; then
    echo "kernel-fuel performance sample failed: series=$series fuel=$fuel_mode round=$round exit=$exit_code" >&2
    cat "$time_path" >&2
    cat "$output_path" >&2
    exit 1
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$series" "$fuel_mode" "$round" "$wall_seconds" "$peak_rss_kib" >>"$kernel_fuel_raw"
}

kernel_fuel_median_wall() {
  local series=$1
  local fuel_mode=$2
  awk -F '\t' -v series="$series" -v fuel="$fuel_mode" \
    '$1 == series && $2 == fuel { print $4 }' "$kernel_fuel_raw" |
    sort -n |
    sed -n '3p'
}

kernel_fuel_max_rss() {
  local series=$1
  local fuel_mode=$2
  awk -F '\t' -v series="$series" -v fuel="$fuel_mode" \
    '$1 == series && $2 == fuel { if ($5 > maximum) maximum = $5 } END { print maximum + 0 }' \
    "$kernel_fuel_raw"
}

kernel_fuel_wall_delta_percent() {
  awk -v baseline="$1" -v measured="$2" \
    'BEGIN { if (baseline <= 0) exit 2; printf "%.6f", ((measured - baseline) / baseline) * 100 }'
}

snapshot_kernel_fuel_package >"$kernel_fuel_package_before"

for fuel_mode in off failure detailed; do
  run_kernel_fuel_command \
    "$fuel_mode" off "$performance_dir/kernel-fuel-timing-off-${fuel_mode}-warmup.json"
done

for round in 1 2 3 4 5; do
  case $((round % 3)) in
    1) fuel_order=(off failure detailed) ;;
    2) fuel_order=(failure detailed off) ;;
    0) fuel_order=(detailed off failure) ;;
  esac
  for fuel_mode in "${fuel_order[@]}"; do
    measure_kernel_fuel_command timing-off "$fuel_mode" off "$round"
  done
done

kernel_fuel_expected_json="$performance_dir/kernel-fuel-timing-off-off-1.json"
for output_path in "$performance_dir"/kernel-fuel-timing-off-*.json; do
  if ! cmp -s "$kernel_fuel_expected_json" "$output_path"; then
    echo "kernel-fuel timing-off JSON changed across fuel modes or repeated runs: $output_path" >&2
    diff -u "$kernel_fuel_expected_json" "$output_path" >&2 || true
    exit 1
  fi
done
if [[ $(<"$kernel_fuel_expected_json") == *'"kernel_fuel"'* ]] ||
  [[ $(<"$kernel_fuel_expected_json") == *'"timings"'* ]]; then
  echo "kernel-fuel timing-off success unexpectedly emitted fuel or timing telemetry" >&2
  exit 1
fi

for fuel_mode in off detailed; do
  run_kernel_fuel_command \
    "$fuel_mode" detailed "$performance_dir/kernel-fuel-joint-detailed-${fuel_mode}-warmup.json"
done
for round in 1 2 3 4 5; do
  if ((round % 2 == 1)); then
    fuel_order=(off detailed)
  else
    fuel_order=(detailed off)
  fi
  for fuel_mode in "${fuel_order[@]}"; do
    measure_kernel_fuel_command joint-detailed "$fuel_mode" detailed "$round"
  done
done

snapshot_kernel_fuel_package >"$kernel_fuel_package_after"
if ! cmp -s "$kernel_fuel_package_before" "$kernel_fuel_package_after"; then
  echo "kernel-fuel performance scenario changed the fixed package fixture" >&2
  diff -u "$kernel_fuel_package_before" "$kernel_fuel_package_after" >&2 || true
  exit 1
fi

off_wall="$(kernel_fuel_median_wall timing-off off)"
failure_wall="$(kernel_fuel_median_wall timing-off failure)"
detailed_wall="$(kernel_fuel_median_wall timing-off detailed)"
off_rss="$(kernel_fuel_max_rss timing-off off)"
failure_rss="$(kernel_fuel_max_rss timing-off failure)"
detailed_rss="$(kernel_fuel_max_rss timing-off detailed)"
failure_wall_delta="$(kernel_fuel_wall_delta_percent "$off_wall" "$failure_wall")"
detailed_wall_delta="$(kernel_fuel_wall_delta_percent "$off_wall" "$detailed_wall")"
failure_rss_delta=$((failure_rss - off_rss))
detailed_rss_delta=$((detailed_rss - off_rss))

joint_off_wall="$(kernel_fuel_median_wall joint-detailed off)"
joint_detailed_wall="$(kernel_fuel_median_wall joint-detailed detailed)"
joint_off_rss="$(kernel_fuel_max_rss joint-detailed off)"
joint_detailed_rss="$(kernel_fuel_max_rss joint-detailed detailed)"
joint_wall_delta="$(kernel_fuel_wall_delta_percent "$joint_off_wall" "$joint_detailed_wall")"
joint_rss_delta=$((joint_detailed_rss - joint_off_rss))

{
  printf 'scenario\tfuel\ttimings\tsamples\tmedian_wall_seconds\tmax_peak_rss_kib\twall_delta_percent\tadditional_peak_rss_kib\n'
  printf 'kernel-fuel-authoring\toff\toff\t%s\t%s\t%s\t0.000000\t0\n' \
    "$kernel_fuel_samples" "$off_wall" "$off_rss"
  printf 'kernel-fuel-authoring\tfailure\toff\t%s\t%s\t%s\t%s\t%s\n' \
    "$kernel_fuel_samples" "$failure_wall" "$failure_rss" "$failure_wall_delta" "$failure_rss_delta"
  printf 'kernel-fuel-authoring\tdetailed\toff\t%s\t%s\t%s\t%s\t%s\n' \
    "$kernel_fuel_samples" "$detailed_wall" "$detailed_rss" "$detailed_wall_delta" "$detailed_rss_delta"
  printf 'kernel-fuel-authoring\toff\tdetailed\t%s\t%s\t%s\t0.000000\t0\n' \
    "$kernel_fuel_samples" "$joint_off_wall" "$joint_off_rss"
  printf 'kernel-fuel-authoring\tdetailed\tdetailed\t%s\t%s\t%s\t%s\t%s\n' \
    "$kernel_fuel_samples" "$joint_detailed_wall" "$joint_detailed_rss" "$joint_wall_delta" "$joint_rss_delta"
} >"$kernel_fuel_summary"

cat "$kernel_fuel_raw"
cat "$kernel_fuel_summary"
echo "kernel-fuel raw samples: $kernel_fuel_raw"
echo "kernel-fuel summary: $kernel_fuel_summary"

if ! awk -v value="$failure_wall_delta" 'BEGIN { exit !(value <= 3.0) }' ||
  ((failure_rss_delta > 1024)); then
  echo "kernel-fuel failure mode exceeded 3% wall or 1 MiB peak-RSS budget" >&2
  exit 1
fi
if ! awk -v value="$detailed_wall_delta" 'BEGIN { exit !(value <= 10.0) }' ||
  ((detailed_rss_delta > 8192)); then
  echo "kernel-fuel detailed mode exceeded 10% wall or 8 MiB peak-RSS budget" >&2
  exit 1
fi
