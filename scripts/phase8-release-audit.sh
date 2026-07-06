#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Fixed Phase 8 release-audit fixture gate. This is narrower than the Phase 9
# workspace regression gate and focuses on source-free checker/audit contracts.
echo "[1/4] Source-free reference checker binary"
cargo test -p npa-checker-ref

echo "[2/4] Independent checker audit substrate"
cargo test -p npa-api independent_checker

echo "[3/4] Standard-library release audit fixture"
cargo test -p npa-api --lib std_library::tests::audits_mvp_release_artifacts_for_independent_checker

echo "[4/4] AI fast path boundary"
cargo test -p npa-api ai_search
