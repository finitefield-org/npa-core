#!/bin/sh
set -eu

repo_root=$(/usr/bin/git rev-parse --show-toplevel)
output="$repo_root/npa-core/testdata/certificate-structural-limits-maxima.tsv"
temporary=$(mktemp "${TMPDIR:-/tmp}/npa-structural-limits.XXXXXX")
trap 'rm -f "$temporary"' EXIT HUP INT TERM

cd "$repo_root"
# Manifest fixtures are closure dependencies, not current-corpus audit roots.
/usr/bin/git ls-files -z '*.npcert' \
  ':(exclude)npa-core/testdata/certificate-structural-history/*.npcert' |
  cargo run --quiet --manifest-path npa-core/Cargo.toml -p npa-cert \
    --example audit_structural_limits -- --stdin0-with-dependencies \
    npa-core/testdata/certificate-structural-history/dependencies.tsv >"$temporary"

mv "$temporary" "$output"
trap - EXIT HUP INT TERM
