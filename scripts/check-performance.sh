#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "[1/4] Build performance harnesses (locked, offline)"
cargo build --locked --offline -p npa-api --example bench_package_verifier
cargo build --locked --offline -p npa-api --example bench_true_batching

echo "[2/4] Verify deterministic observability contracts"
cargo test --locked --offline -p npa-api performance_measurement
cargo test --locked --offline -p npa-api performance_gate
cargo test --locked --offline -p npa-api tactic_batch_deterministic_counter_gate_covers_required_candidate_counts
cargo test --locked --offline -p npa-cert prepared_candidate_chain_counters_cover_required_candidate_counts
cargo test --locked --offline -p npa-kernel optional_work_meter

echo "[3/4] Run compact checked-artifact fixture"
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

echo "[4/4] Run proof-authoring true-batching fixtures"
true_batching_output="$(target/debug/examples/bench_true_batching \
  --source-identity "$source_identity" \
  --warmup 1 \
  --samples 3)"
true_batching_path="$performance_dir/true-batching.json"
printf '%s\n' "$true_batching_output" > "$true_batching_path"

if [[ "$true_batching_output" != *'"schema":"npa.true-batching.elapsed.v0.1"'* ]] ||
  [[ "$true_batching_output" != *'"elapsed_gate":"advisory","status":"passed"'* ]] ||
  [[ "$true_batching_output" != *'"path":"certificate-producer","fixture":"accepted-chain","candidate_count":256'* ]] ||
  [[ "$true_batching_output" != *'"prepared_chains":1,"name_index_rebuilds":1,"environment_clones":256,"copied_prefix_elements":0'* ]]; then
  echo "true-batching fixture output did not match deterministic work contract" >&2
  echo "$true_batching_output" >&2
  exit 1
fi

echo "$true_batching_output"
echo "true-batching report: $true_batching_path"
