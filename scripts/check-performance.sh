#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "[1/3] Build performance harness (locked, offline)"
cargo build --locked --offline -p npa-api --example bench_package_verifier

echo "[2/3] Verify deterministic observability contracts"
cargo test --locked --offline -p npa-api performance_measurement
cargo test --locked --offline -p npa-api performance_gate
cargo test --locked --offline -p npa-api tactic_batch_deterministic_counter_gate_covers_required_candidate_counts
cargo test --locked --offline -p npa-kernel optional_work_meter

echo "[3/3] Run compact checked-artifact fixture"
source_identity="$(/usr/bin/git rev-parse HEAD)"
if [[ -n "$(/usr/bin/git status --porcelain --untracked-files=normal)" ]]; then
  source_identity="${source_identity}-dirty"
fi
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

if [[ "$performance_output" != *'"schema":"npa.performance.run.v0.1"'* ]] ||
  [[ "$performance_output" != *'"status":"passed"'* ]] ||
  [[ "$performance_output" != *'"schema":"npa.performance.measurements.v0.2"'* ]] ||
  [[ "$performance_output" != *'"cargo_profile":"dev","features":[]'* ]] ||
  [[ "$performance_output" == *'"rustc_vv":"unavailable"'* ]] ||
  [[ "$performance_output" != *'"label":"package.modules_decoded","unit":"count","value":2'* ]] ||
  [[ "$performance_output" != *'"label":"package.modules_checked","unit":"count","value":2'* ]] ||
  [[ "$performance_output" != *'"label":"package.live_results","unit":"count","value":2'* ]]; then
  echo "performance fixture output did not match deterministic baseline" >&2
  echo "$performance_output" >&2
  exit 1
fi

echo "$performance_output"
echo "performance report: $performance_path"
