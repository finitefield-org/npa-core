#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
CORE_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)

exec env CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}" \
  cargo run --locked --offline -q \
  --manifest-path "$CORE_ROOT/Cargo.toml" \
  -p npa-cli \
  --bin npa-release-manifest-validator -- \
  "$@"
