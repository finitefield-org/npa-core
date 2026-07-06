#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Fixed post-Phase-9-Human completion gate: AI automation remains on
# deterministic Machine Surface fixtures, while Human advanced-feature
# regressions run in workspace tests. The gate intentionally does not add
# production LLM/RAG/online graph store/external SMT services to the PR or AI
# candidate hot path.
echo "[1/4] Phase 9 M9 regression fixtures"
cargo test -p npa-api --lib advanced_ai_m9

echo "[2/4] Formatting check"
cargo fmt --all -- --check

echo "[3/4] Clippy workspace gate"
cargo clippy --workspace --all-targets -- -D warnings

echo "[4/4] Workspace tests"
cargo test --workspace
