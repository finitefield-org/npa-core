#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
temporary_parent=${TMPDIR:-/tmp}
temporary_parent=${temporary_parent%/}
temporary_root=$(mktemp -d "$temporary_parent/npa-whnf-output-test.XXXXXX")
temporary_root=$(cd "$temporary_root" && pwd -P)
trap '/bin/rm -rf -- "$temporary_root"' EXIT
mkdir "$temporary_root/bin" "$temporary_root/work" "$temporary_root/work/scripts" "$temporary_root/output"
mkdir -p "$temporary_root/work/testdata/performance/fixtures" \
  "$temporary_root/work/testdata/performance/baselines"

cp "$repository_root/scripts/check-performance.sh" "$temporary_root/work/scripts/check-performance.sh"
chmod +x "$temporary_root/work/scripts/check-performance.sh"
cat >"$temporary_root/bin/cargo" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
cat >"$temporary_root/bin/git" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == rev-parse ]]; then
  printf '0123456789abcdef0123456789abcdef01234567\n'
elif [[ ${1:-} == status ]]; then
  exit 0
else
  exit 2
fi
EOF
chmod +x "$temporary_root/bin/cargo" "$temporary_root/bin/git"
mkdir -p "$temporary_root/work/target/release/examples"
cat >"$temporary_root/work/target/release/examples/bench_whnf_application_spine" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
output=""
validate=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --output) output=$2; shift 2 ;;
    --validate-report) validate=$2; shift 2 ;;
    *) shift ;;
  esac
done
if [[ -n "$validate" ]]; then
  : >.whnf-validator-called
  if [[ ${NPA_TEST_REJECT_VALIDATION:-0} == 1 ]]; then
    exit 9
  fi
  grep -q '"schema":"npa.kernel-whnf-application-spine.run.v0.2"' "$validate"
  grep -q '"phase":"candidate"' "$validate"
  exit 0
fi
[[ -n "$output" && ! -e "$output" ]]
printf '{"schema":"npa.kernel-whnf-application-spine.run.v0.2","phase":"candidate","rows":[{}]}\n' >"$output"
EOF
chmod +x "$temporary_root/work/target/release/examples/bench_whnf_application_spine"
for binary in check_whnf_application_spine_package measure_process; do
  printf '#!/bin/sh\nexit 0\n' >"$temporary_root/work/target/release/examples/$binary"
  chmod +x "$temporary_root/work/target/release/examples/$binary"
done
printf '{}\n' >"$temporary_root/work/profile.json"
printf '{}\n' >"$temporary_root/work/testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
printf '{}\n' >"$temporary_root/work/testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
(
  cd "$temporary_root/work"
  /usr/bin/git init -q
  /usr/bin/git config user.name "NPA Hermetic Test"
  /usr/bin/git config user.email "npa-hermetic@example.invalid"
  /usr/bin/git add .
  /usr/bin/git commit -q -m fixture
)

(
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-performance.sh \
    --elapsed-profile profile.json --output "$temporary_root/output/report.json"
)
[[ -f "$temporary_root/output/report.json" ]]
[[ -f "$temporary_root/work/.whnf-validator-called" ]]

if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" NPA_TEST_REJECT_VALIDATION=1 \
    scripts/check-performance.sh --elapsed-profile profile.json \
      --output "$temporary_root/output/rejected-report.json"
) >/dev/null 2>&1; then
  echo "WHNF elapsed lane ignored strict validator failure" >&2
  exit 1
fi

if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-performance.sh \
    --elapsed-profile profile.json --output "$temporary_root/output/report.json"
) >/dev/null 2>&1; then
  echo "WHNF elapsed lane replaced an existing report" >&2
  exit 1
fi

if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-performance.sh \
    --elapsed-profile profile.json
) >/dev/null 2>&1; then
  echo "WHNF elapsed lane accepted a missing --output" >&2
  exit 1
fi

echo "check-performance WHNF persistent output test passed"
