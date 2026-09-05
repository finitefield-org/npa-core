#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: validate-performance-fixture-activation.sh --task-doc PATH --activation-task ID --kind KIND --expected-count N" >&2
  exit 2
}

[[ $# -eq 8 ]] || usage
[[ $1 == --task-doc && $3 == --activation-task && $5 == --kind && $7 == --expected-count ]] || usage
task_doc=$2
activation_task=$4
kind=$6
expected_count=$8
[[ -f $task_doc && $expected_count =~ ^[1-9][0-9]*$ ]] || usage

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
record=$(awk -v task="### ${activation_task} " '
  index($0, task) == 1 { active=1; next }
  active && /^### / { exit }
  active && /^- audited_schema: `/ { record=1 }
  record && /^$/ { exit }
  record { print }
' "$task_doc")

expected_keys=(audited_schema prior_variants union_state selected_schema selected_manifest_path selected_type_suffix selected_schema_constant selected_selection_type selected_version_variant selected_parser defining_task_or_commit)
[[ $(wc -l <<<"$record" | tr -d ' ') -eq ${#expected_keys[@]} ]] || {
  echo "activation record must contain exactly ${#expected_keys[@]} keys" >&2
  exit 1
}
for index in "${!expected_keys[@]}"; do
  line=$(sed -n "$((index + 1))p" <<<"$record")
  [[ $line == "- ${expected_keys[index]}: \`"*"\`" ]] || {
    echo "activation record key order mismatch at ${expected_keys[index]}" >&2
    exit 1
  }
done

value() {
  sed -n 's/^- '"$1"': `\(.*\)`$/\1/p' <<<"$record"
}
selected_schema=$(value selected_schema)
selected_path=$(value selected_manifest_path)
audited_schema=$(value audited_schema)
union_state=$(value union_state)
selected_type_suffix=$(value selected_type_suffix)
selected_schema_constant=$(value selected_schema_constant)
selected_selection_type=$(value selected_selection_type)
selected_version_variant=$(value selected_version_variant)
selected_parser=$(value selected_parser)

schema_prefix=npa.performance.fixtures.v0.
[[ $audited_schema == "$schema_prefix"* && $selected_schema == "$schema_prefix"* ]] || {
  echo "activation schemas must use the fixture v0.N namespace" >&2
  exit 1
}
audited_version=${audited_schema#"$schema_prefix"}
selected_version=${selected_schema#"$schema_prefix"}
[[ $audited_version =~ ^[0-9]+$ && $selected_version =~ ^[0-9]+$ ]] || {
  echo "activation schema suffixes must be natural numbers" >&2
  exit 1
}
case $union_state in
  co-landed)
    [[ $selected_version -eq $((audited_version + 1)) ]] || {
      echo "co-landed fixture schema must be the immediate successor" >&2
      exit 1
    }
    ;;
  reused)
    [[ $selected_version -eq $audited_version ]] || {
      echo "reused fixture schema must equal the audited schema" >&2
      exit 1
    }
    ;;
  *)
    echo "activation union_state is unsupported" >&2
    exit 1
    ;;
esac

expected_suffix="V0${selected_version}"
[[ $selected_path == "npa-core/testdata/performance/fixtures/manifest.v0.${selected_version}.json" &&
  $selected_type_suffix == "$expected_suffix" &&
  $selected_schema_constant == "PERFORMANCE_FIXTURES_SCHEMA_V0_${selected_version}" &&
  $selected_selection_type == "PerformanceFixtureSelection${expected_suffix}" &&
  $selected_version_variant == "VersionedPerformanceFixtureSelection::${expected_suffix}" &&
  $selected_parser == "validate_performance_fixture_selection_v0${selected_version}" ]] || {
  echo "activation successor path or Rust identifiers are inconsistent" >&2
  exit 1
}
[[ $selected_path == npa-core/testdata/performance/fixtures/* && $selected_path != *..* && $selected_path != /* ]] || {
  echo "selected manifest path is outside the performance fixture directory" >&2
  exit 1
}
manifest="$repository_root/$selected_path"
fixture_root="$repository_root/npa-core/testdata/performance/fixtures"
cursor=$repository_root
IFS=/ read -r -a selected_components <<<"$selected_path"
for component in "${selected_components[@]}"; do
  cursor="$cursor/$component"
  [[ ! -L $cursor ]] || {
    echo "selected manifest path contains a symlink: $selected_path" >&2
    exit 1
  }
done
[[ -d $fixture_root && -f $manifest && ! -L $manifest ]] || {
  echo "selected manifest is missing or not a regular file: $selected_path" >&2
  exit 1
}
jq -e --arg schema "$selected_schema" --arg kind "$kind" --argjson expected "$expected_count" '
  type == "object"
  and keys_unsorted == ["schema", "scenarios"]
  and .schema == $schema
  and (.scenarios | type == "array")
  and ([.scenarios[] | select(.kind == $kind)] | length) == $expected
' "$manifest" >/dev/null
