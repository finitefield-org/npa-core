#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/update-whnf-application-spine-performance-baseline.sh \
  --elapsed-profile PATH --reason TEXT --archived-artifact PATH

Validate an identity-bound archived pre-switch recursive artifact and install a
canonical reviewed Linux x86_64 WHNF application-spine elapsed baseline.

The script asks the archived checkout's own controller to collect recursive
rows. The current post-switch binary only validates and seals that fresh
evidence; it never executes --phase recursive.
EOF
}

elapsed_profile=""
review_reason=""
archived_artifact=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --elapsed-profile)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      elapsed_profile=$2
      shift 2
      ;;
    --reason)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      review_reason=$2
      shift 2
      ;;
    --archived-artifact)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      archived_artifact=$2
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[[ -n "$elapsed_profile" ]] || { echo "--elapsed-profile is required" >&2; exit 2; }
[[ -n "${review_reason//[[:space:]]/}" ]] || { echo "--reason must be nonempty" >&2; exit 2; }
[[ -n "$archived_artifact" ]] || { echo "--archived-artifact is required" >&2; exit 2; }
[[ -f "$elapsed_profile" ]] || { echo "elapsed profile is not a file: $elapsed_profile" >&2; exit 2; }
[[ -f "$archived_artifact" ]] || { echo "archived artifact is not a file: $archived_artifact" >&2; exit 2; }

repository_root=$(cd "$(/usr/bin/git rev-parse --show-toplevel)" && pwd -P)
current_directory=$(pwd -P)
[[ "$current_directory" == "$repository_root/npa-core" ]] || {
  echo "run this script from the npa-core directory" >&2
  exit 2
}
[[ -z "$(/usr/bin/git status --porcelain --untracked-files=all)" ]] || {
  echo "reviewed baseline update requires a clean checkout" >&2
  exit 2
}
source_identity=$(/usr/bin/git rev-parse HEAD)
[[ "$source_identity" =~ ^[0-9a-f]{40}$ ]] || {
  echo "current source identity must be a lowercase 40-digit Git OID" >&2
  exit 2
}

fixture_manifest="testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
deterministic_baseline="testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
baseline_output="testdata/performance/baselines/elapsed/kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1.baseline.v0.1.json"

host_target=$(rustc -Vv | sed -n 's/^host: //p')
[[ "$host_target" == "x86_64-unknown-linux-gnu" ]] || {
  echo "reviewed baseline update requires x86_64-unknown-linux-gnu, got: $host_target" >&2
  exit 2
}
jq -e \
  --arg expected_baseline "$baseline_output" \
  '.schema == "npa.kernel-whnf-application-spine.elapsed-profile.v0.1" and
   .profile_id == "kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1" and
   .target == "x86_64-unknown-linux-gnu" and
   .cargo_profile == "release" and
   .baseline_path == $expected_baseline and
   (.review_reason | type == "string" and length > 0)' \
  "$elapsed_profile" >/dev/null

archive_root_raw=$(jq -er '.archive_root | select(type == "string" and startswith("/"))' "$archived_artifact")
[[ -d "$archive_root_raw" ]] || {
  echo "archived artifact root is not a directory: $archive_root_raw" >&2
  exit 2
}
[[ ! -L "$archive_root_raw" ]] || {
  echo "archived artifact root must not be a symbolic link: $archive_root_raw" >&2
  exit 2
}
archive_root=$(cd -- "$archive_root_raw" && pwd -P)
[[ "$archive_root_raw" == "$archive_root" ]] || {
  echo "archived artifact root must be an absolute canonical path: $archive_root_raw" >&2
  exit 2
}

resolve_archived_regular_file() (
  local relative_path=$1
  local cursor=$archive_root
  local component
  local components=()
  IFS='/' read -r -a components <<<"$relative_path"
  [[ ${#components[@]} -gt 0 ]] || {
    echo "empty archived artifact file path" >&2
    return 2
  }
  for component in "${components[@]}"; do
    [[ -n "$component" && "$component" != "." && "$component" != ".." ]] || {
      echo "archived artifact path contains a non-normal component: $relative_path" >&2
      return 2
    }
    cursor="$cursor/$component"
    [[ ! -L "$cursor" ]] || {
      echo "archived artifact path must not contain symbolic links: $cursor" >&2
      return 2
    }
  done
  [[ -f "$cursor" && ! -d "$cursor" ]] || {
    echo "archived artifact path is not a regular file: $cursor" >&2
    return 2
  }
  local leaf=${cursor##*/}
  local parent=${cursor%/*}
  local canonical_parent
  canonical_parent=$(cd -- "$parent" && pwd -P)
  case "$canonical_parent/$leaf" in
    "$archive_root"/*) ;;
    *)
      echo "archived artifact path escapes its canonical root: $relative_path" >&2
      return 2
      ;;
  esac
  printf '%s\n' "$canonical_parent/$leaf"
)

# Fail before building when the fixed archived source/binary catalog already
# contains a symlink or escape. The current Rust collector repeats these checks
# descriptor-relatively and snapshots the exact executable bytes before use.
for archived_path in \
  "crates/npa-api/examples/bench_whnf_application_spine.rs" \
  "crates/npa-api/examples/check_whnf_application_spine_package.rs" \
  "crates/npa-cli/examples/measure_process.rs" \
  "target/release/examples/bench_whnf_application_spine" \
  "target/release/examples/check_whnf_application_spine_package" \
  "target/release/examples/measure_process"
do
  resolve_archived_regular_file "$archived_path" >/dev/null
done

NPA_BENCH_SOURCE_IDENTITY="$source_identity" \
cargo build --locked --offline --release -p npa-api \
  --example bench_whnf_application_spine \
  --example check_whnf_application_spine_package
NPA_BENCH_SOURCE_IDENTITY="$source_identity" \
cargo build --locked --offline --release -p npa-cli --example measure_process

target/release/examples/bench_whnf_application_spine \
  --fixture-manifest "$fixture_manifest" \
  --baseline "$deterministic_baseline" \
  --validate-bootstrap-profile "$elapsed_profile" \
  --archived-artifact "$archived_artifact" \
  --measure-process target/release/examples/measure_process \
  --package-harness target/release/examples/check_whnf_application_spine_package

[[ ! -e "$baseline_output" && ! -L "$baseline_output" ]] || {
  echo "refusing to overwrite existing baseline: $baseline_output" >&2
  exit 2
}
baseline_parent=$(dirname "$baseline_output")
[[ -d "$baseline_parent" && ! -L "$baseline_parent" ]] || {
  echo "baseline parent must be an existing non-symlink directory: $baseline_parent" >&2
  exit 2
}
baseline_parent_canonical=$(cd "$baseline_parent" && pwd -P)
[[ "$baseline_parent_canonical" == "$repository_root/npa-core/$baseline_parent" ]] || {
  echo "baseline parent escaped the canonical checkout: $baseline_parent_canonical" >&2
  exit 2
}
baseline_output_absolute="$baseline_parent_canonical/${baseline_output##*/}"
target/release/examples/bench_whnf_application_spine \
  --fixture-manifest "$fixture_manifest" \
  --baseline "$deterministic_baseline" \
  --collect-archived-recursive-baseline \
  --archived-artifact "$archived_artifact" \
  --review-reason "$review_reason" \
  --output "$baseline_output_absolute"

echo "wrote reviewed recursive baseline: $baseline_output_absolute" >&2
echo "elapsed profile was checked as an explicit reviewer input and was not modified: $elapsed_profile" >&2
