#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
source scripts/check-performance.sh

temporary_root="$(mktemp -d "${TMPDIR:-/tmp}/npa-snap-vmsp-controller.XXXXXX")"
case "$temporary_root" in "${TMPDIR:-/tmp}"/npa-snap-vmsp-controller.*) ;; *) exit 1 ;; esac
temporary_root="$(cd "$temporary_root" && pwd -P)"
trap 'rmdir "$temporary_root"' EXIT

source_identity="$(current_source_identity)"
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline \
  -p npa-cli --example measure_process --example bench_package_artifact_snapshot
NPA_BENCH_SOURCE_IDENTITY="$source_identity" cargo build --locked --offline \
  -p npa-api --example bench_shared_payload

manager="$PWD/target/debug/examples/measure_process"
snapshot="$PWD/target/debug/examples/bench_package_artifact_snapshot"
shared="$PWD/target/debug/examples/bench_shared_payload"

[[ -x "$manager" && -x "$snapshot" && -x "$shared" ]]

# The controller writes and flushes one raw lowercase SHA-256 digest at the
# final pre-publication boundary. The shell accepts that value only when the
# controller later exits successfully. Exercise the same helper used by both
# production wrappers so a tagged report/seal hash cannot create a sealed
# destination that the wrapper then reports as failed.
raw_matrix_digest="$(printf '%s' 'sealed matrix bytes' | sha256_stream)"
require_snap_vmsp_controller_matrix_digest snapshot "$raw_matrix_digest"
require_snap_vmsp_controller_matrix_digest shared-payload "$raw_matrix_digest"
if require_snap_vmsp_controller_matrix_digest snapshot \
  "sha256:$raw_matrix_digest" 2>/dev/null
then
  echo "tagged controller digest crossed the raw operational stdout contract" >&2
  exit 1
fi

# The four legacy per-sample/direct-final surfaces are retired. Every spelling
# must fail with the generic controlled usage error before opening or creating
# caller-selected output state.
for retired in \
  --create-snap-vmsp-final \
  --measure-snap-vmsp-child \
  --write-snap-vmsp-member \
  --manage-snap-vmsp-staging
do
  candidate="$temporary_root/${retired#--}"
  diagnostic="$temporary_root/diagnostic"
  if "$manager" "$retired" --output "$candidate" 2>"$diagnostic"; then
    echo "retired SNAP/VMSP surface remained callable: $retired" >&2
    exit 1
  fi
  status=$?
  [[ "$status" -eq 2 ]]
  [[ ! -e "$candidate" ]]
  grep -Fxq \
    'measure-process: usage: measure_process --output PATH --stderr PATH -- COMMAND [ARG ...]' \
    "$diagnostic"
  rm "$diagnostic"
done

# These are the actual release-example binaries, executed through inherited
# descriptor paths with the audit fd/hash protocol used by the controller.
cargo test --locked --offline -p npa-cli --example measure_process \
  tests::real_snap_and_vmsp_benchmarks_support_detached_descriptor_exec -- --exact
cargo test --locked --offline -p npa-cli --example measure_process \
  tests::tiny_controller_round_trip_creates_final_only_after_quiescence_and_seals -- --exact
cargo test --locked --offline -p npa-cli --example measure_process \
  tests::escaped_setsid_pipe_holder_fails_closed_before_final_creation -- --exact
cargo test --locked --offline -p npa-api \
  json::tests::bounded_parser_rejects_near_limit_structure_under_low_address_space \
  --lib -- --exact

echo "SNAP/VMSP sealed-controller hermetic tests passed"
