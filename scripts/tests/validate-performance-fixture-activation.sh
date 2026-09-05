#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
validator="$repository_root/npa-core/scripts/validate-performance-fixture-activation.sh"
temporary_root=$(mktemp -d "${TMPDIR:-/tmp}/npa-fixture-activation-test.XXXXXX")
trap 'rm -rf -- "$temporary_root"' EXIT

expect_failure() {
  if "$@" 2>/dev/null; then
    echo "validator accepted an invalid activation fixture: $*" >&2
    exit 1
  fi
}

run_validator() (
  cd "$temporary_root/repo"
  npa-core/scripts/validate-performance-fixture-activation.sh "$@"
)

mkdir -p "$temporary_root/repo/npa-core/testdata/performance/fixtures"
cp "$validator" "$temporary_root/repo/validator.sh"
cat >"$temporary_root/repo/task.md" <<'EOF'
### SNAP-PERF-FORMAT-001 — fixture activation
- audited_schema: `npa.performance.fixtures.v0.1`
- prior_variants: `warmed-checked-artifact-verifier`
- union_state: `co-landed`
- selected_schema: `npa.performance.fixtures.v0.2`
- selected_manifest_path: `npa-core/testdata/performance/fixtures/manifest.v0.2.json`
- selected_type_suffix: `V02`
- selected_schema_constant: `PERFORMANCE_FIXTURES_SCHEMA_V0_2`
- selected_selection_type: `PerformanceFixtureSelectionV02`
- selected_version_variant: `VersionedPerformanceFixtureSelection::V02`
- selected_parser: `validate_performance_fixture_selection_v02`
- defining_task_or_commit: `SNAP-PERF-FORMAT-001`
### NEXT — boundary
EOF
cat >"$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" <<'EOF'
{"schema":"npa.performance.fixtures.v0.2","scenarios":[{"kind":"package-artifact-snapshot"}]}
EOF
cat >"$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.1.json" <<'EOF'
{"schema":"npa.performance.fixtures.v0.1","scenarios":[{"kind":"package-artifact-snapshot"},{"kind":"package-artifact-snapshot"}]}
EOF

mkdir -p "$temporary_root/repo/npa-core/scripts"
cp "$validator" "$temporary_root/repo/npa-core/scripts/validate-performance-fixture-activation.sh"
run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

sed -e 's/audited_schema: `npa\.performance\.fixtures\.v0\.1`/audited_schema: `npa.performance.fixtures.v0.2`/' \
  -e 's/union_state: `co-landed`/union_state: `reused`/' \
  "$temporary_root/repo/task.md" >"$temporary_root/repo/reused.md"
run_validator --task-doc reused.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

awk '{ print; if ($0 ~ /^- selected_schema:/) print "- selected_schema: `duplicate`" }' \
  "$temporary_root/repo/task.md" >"$temporary_root/repo/bad.md"
expect_failure run_validator --task-doc bad.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

awk '{ print; if ($0 ~ /^- prior_variants:/) print "- unexpected_activation_key: `value`" }' \
  "$temporary_root/repo/task.md" >"$temporary_root/repo/extra-key.md"
expect_failure run_validator --task-doc extra-key.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

sed 's#manifest.v0.2.json#../outside.json#' \
  "$temporary_root/repo/task.md" >"$temporary_root/repo/path-escape.md"
expect_failure run_validator --task-doc path-escape.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

sed -e 's/v0\.2/v0.3/g' -e 's/V0_2/V0_3/g' -e 's/V02/V03/g' -e 's/v02/v03/g' \
  "$temporary_root/repo/task.md" >"$temporary_root/repo/wrong-successor.md"
sed 's/v0\.2/v0.3/g' \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" \
  >"$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.3.json"
expect_failure run_validator --task-doc wrong-successor.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1

cp "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" \
  "$temporary_root/repo/external-manifest.json"
mv "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.saved"
ln -s "$temporary_root/repo/external-manifest.json" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json"
expect_failure run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1
rm -f "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json"
mv "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.saved" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json"

sed 's/npa\.performance\.fixtures\.v0\.2/npa.performance.fixtures.v0.3/' \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" \
  >"$temporary_root/repo/wrong-schema.json"
mv "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.saved"
mv "$temporary_root/repo/wrong-schema.json" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json"
expect_failure run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1
mv "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.saved" \
  "$temporary_root/repo/npa-core/testdata/performance/fixtures/manifest.v0.2.json"

expect_failure run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 0
expect_failure run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 2
expect_failure run_validator --task-doc task.md --activation-task SNAP-PERF-FORMAT-001 --kind package-artifact-snapshot --expected-count 1 extra

echo "performance fixture activation tests passed"
