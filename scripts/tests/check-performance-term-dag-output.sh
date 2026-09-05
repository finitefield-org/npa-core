#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
temporary_parent=${TMPDIR:-/tmp}
temporary_parent=${temporary_parent%/}
temporary_root=$(mktemp -d "$temporary_parent/npa-tdag-output-test.XXXXXX")
temporary_root=$(cd "$temporary_root" && pwd -P)
trap '/bin/rm -rf -- "$temporary_root"' EXIT
mkdir "$temporary_root/bin" "$temporary_root/tmp" "$temporary_root/work" \
  "$temporary_root/work/scripts" "$temporary_root/output"
mkdir -p "$temporary_root/work/testdata/performance/fixtures" \
  "$temporary_root/work/testdata/performance/baselines" \
  "$temporary_root/work/testdata/performance/certificate-term-dag-materialization"

cp "$repository_root/scripts/check-performance.sh" "$temporary_root/work/scripts/check-performance.sh"
chmod +x "$temporary_root/work/scripts/check-performance.sh"
cat >"$temporary_root/bin/cargo" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
chmod +x "$temporary_root/bin/cargo"

for scenario in shared-doubling nonsharing-chain repeated-declaration-roots sparse-import import-diamond term-materialization-near-limit wide-term-materialization-package; do
  mkdir "$temporary_root/work/testdata/performance/certificate-term-dag-materialization/$scenario"
  printf '{"scenario":"%s"}\n' "$scenario" >"$temporary_root/work/testdata/performance/certificate-term-dag-materialization/$scenario/fixture.json"
done
printf '{}\n' >"$temporary_root/work/testdata/performance/fixtures/certificate-term-dag-materialization.v0.1.json"
printf '{}\n' >"$temporary_root/work/testdata/performance/baselines/certificate-term-dag-materialization.measurements.v0.1.json"

mkdir -p "$temporary_root/work/target/debug/examples" "$temporary_root/work/target/release/examples"
cat >"$temporary_root/work/target/debug/examples/generate_certificate_term_dag_materialization_fixtures" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == --output && $# -eq 2 ]]; then
  cp -R testdata/performance/certificate-term-dag-materialization/. "$2/"
elif [[ ${1:-} == --clean-output && $# -eq 2 ]]; then
  root=$2
  for scenario in shared-doubling nonsharing-chain repeated-declaration-roots sparse-import import-diamond term-materialization-near-limit wide-term-materialization-package; do
    rm "$root/$scenario/fixture.json"
    rmdir "$root/$scenario"
  done
  : >.tdag-generator-cleaned
  rmdir "$root"
else
  exit 2
fi
EOF
chmod +x "$temporary_root/work/target/debug/examples/generate_certificate_term_dag_materialization_fixtures"

cat >"$temporary_root/work/target/release/examples/bench_certificate_term_dag_materialization" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
mode=""
output=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --validate-all|--controller|--validate-report) mode=$1; shift ;;
    --output) output=$2; shift 2 ;;
    --manifest|--baseline|--measure-process) shift 2 ;;
    *) exit 2 ;;
  esac
done
case "$mode" in
  --validate-all) exit 0 ;;
  --controller)
    [[ -n "$output" && ! -e "$output" && ! -L "$output" ]]
    printf '{"schema":"npa.certificate-term-dag-materialization.run.v0.2","rows":[]}\n' >"$output"
    ;;
  --validate-report)
    : >.tdag-validator-called
    if [[ ${NPA_TEST_REJECT_TDAG_VALIDATION:-0} == 1 ]]; then
      exit 9
    fi
    grep -q '"schema":"npa.certificate-term-dag-materialization.run.v0.2"' "$output"
    ;;
  *) exit 2 ;;
esac
EOF
chmod +x "$temporary_root/work/target/release/examples/bench_certificate_term_dag_materialization"
printf '#!/bin/sh\nexit 0\n' >"$temporary_root/work/target/release/examples/measure_process"
chmod +x "$temporary_root/work/target/release/examples/measure_process"

(
  cd "$temporary_root/work"
  /usr/bin/git init -q
  /usr/bin/git config user.name "NPA Hermetic Test"
  /usr/bin/git config user.email "npa-hermetic@example.invalid"
  /usr/bin/git add .
  /usr/bin/git commit -q -m fixture
)

run_lane() {
  local output=$1
  shift
  (
    cd "$temporary_root/work"
    TMPDIR="$temporary_root/tmp" PATH="$temporary_root/bin:/usr/bin:/bin" "$@" \
      scripts/check-performance.sh --term-dag-materialization --output "$output"
  )
}

run_lane "$temporary_root/output/report.json" env
[[ -f "$temporary_root/output/report.json" ]]
[[ -f "$temporary_root/work/.tdag-validator-called" ]]
[[ -f "$temporary_root/work/.tdag-generator-cleaned" ]]
if find "$temporary_root/tmp" -mindepth 1 -maxdepth 1 -name 'npa-tdag-fixtures.*' -print -quit | grep -q .; then
  echo "TDAG lane leaked its private generated fixture root" >&2
  exit 1
fi

if run_lane "$temporary_root/output/rejected.json" env NPA_TEST_REJECT_TDAG_VALIDATION=1 >/dev/null 2>&1; then
  echo "TDAG lane ignored strict validator failure" >&2
  exit 1
fi
[[ -f "$temporary_root/output/rejected.json" ]]

if run_lane "$temporary_root/output/report.json" env >/dev/null 2>&1; then
  echo "TDAG lane replaced an existing output" >&2
  exit 1
fi
if run_lane "$temporary_root/output/../output/noncanonical.json" env >/dev/null 2>&1; then
  echo "TDAG lane accepted a noncanonical output path" >&2
  exit 1
fi
ln -s "$temporary_root/output" "$temporary_root/output-link"
if run_lane "$temporary_root/output-link/symlink.json" env >/dev/null 2>&1; then
  echo "TDAG lane accepted a symlink output parent" >&2
  exit 1
fi

echo "check-performance TDAG persistent output test passed"
