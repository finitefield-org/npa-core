#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "[1/6] Build performance harnesses (locked, offline)"
cargo build --locked --offline -p npa-api --example bench_package_verifier
cargo build --locked --offline -p npa-api --example bench_true_batching

echo "[2/6] Verify deterministic observability contracts"
cargo test --locked --offline -p npa-api performance_measurement
cargo test --locked --offline -p npa-api performance_gate
cargo test --locked --offline -p npa-api tactic_batch_deterministic_counter_gate_covers_required_candidate_counts
cargo test --locked --offline -p npa-cert prepared_candidate_chain_counters_cover_required_candidate_counts
cargo test --locked --offline -p npa-kernel optional_work_meter

echo "[3/6] Run compact checked-artifact fixture"
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
  [[ "$performance_output" != *'"schema":"npa.performance.measurements.v0.3"'* ]] ||
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

echo "[4/6] Run proof-authoring true-batching fixtures"
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

echo "[5/6] Prebuild release npa-cli outside the measured interval"
cargo build --locked --offline --release -p npa-cli --bin npa --example measure_process

echo "[6/6] Run kernel-fuel authoring rollout scenario"
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
  find "$kernel_fuel_package" -type f -print0 |
    sort -z |
    xargs -0 sha256sum
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
