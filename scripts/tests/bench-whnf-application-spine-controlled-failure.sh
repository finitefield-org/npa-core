#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
temporary_root=$(mktemp -d "${TMPDIR:-/tmp}/npa-whnf-controlled-failure.XXXXXX")
temporary_root=$(cd "$temporary_root" && pwd -P)
trap '/bin/rm -rf -- "$temporary_root"' EXIT

cd "$repository_root"
cargo build --locked --offline -p npa-api --example bench_whnf_application_spine
runner="$repository_root/target/debug/examples/bench_whnf_application_spine"
manifest="$repository_root/testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
baseline="$repository_root/testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
printf '{}\n' >"$temporary_root/malformed.json"

expect_controlled_failure() {
  local label=$1
  shift
  local stdout="$temporary_root/$label.stdout"
  local stderr="$temporary_root/$label.stderr"
  set +e
  "$runner" "$@" >"$stdout" 2>"$stderr"
  local status=$?
  set -e
  if [[ $status -ne 2 ]]; then
    echo "$label exited $status instead of 2" >&2
    exit 1
  fi
  [[ ! -s $stdout ]]
  [[ $(wc -l <"$stderr" | tr -d ' ') = 1 ]]
  grep -q '^kernel WHNF benchmark: ' "$stderr"
  if grep -Eiq 'panicked|stack backtrace|thread .+ panic' "$stderr"; then
    echo "$label leaked a panic diagnostic" >&2
    exit 1
  fi
}

expect_controlled_failure missing-manifest \
  --fixture-manifest "$temporary_root/missing.json" --baseline "$baseline" --list
expect_controlled_failure malformed-manifest \
  --fixture-manifest "$temporary_root/malformed.json" --baseline "$baseline" --list
expect_controlled_failure malformed-baseline \
  --fixture-manifest "$manifest" --baseline "$temporary_root/malformed.json" --list
expect_controlled_failure unknown-scenario \
  --fixture-manifest "$manifest" --baseline "$baseline" --child \
  --scenario-id unknown-scenario
expect_controlled_failure unknown-option --unknown

echo "WHNF controlled-failure exit contract test passed"
