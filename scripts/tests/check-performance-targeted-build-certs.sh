#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
source scripts/check-performance.sh

IFS=$'\t' read -r test_root test_parent test_identity \
  < <(make_private_temp_dir "${TMPDIR:-/tmp}" "npa-targeted-controlled-test")
cleanup() {
  if [[ -n ${test_root:-} && -d $test_root ]]; then
    if [[ -e ${fake:-} || -L ${fake:-} ]]; then
      [[ -f $fake && ! -L $fake ]] || {
        echo "refusing to remove a replaced targeted-build test executable: $fake" >&2
        return 1
      }
      rm -- "$fake"
    fi
    guarded_remove_private_temp_dir \
      "$test_root" "$test_parent" "npa-targeted-controlled-test" "$test_identity"
  fi
}
trap cleanup EXIT
fake="$test_root/targeted-build-certs"
printf '%s\n' \
  '#!/usr/bin/env bash' \
  'set -euo pipefail' \
  'echo "targeted build-certs benchmark failed: usage: targeted_build_certs_bench --scenario all --verify | --validate-report PATH" >&2' \
  'exit 2' >"$fake"
chmod 700 "$fake"

bash scripts/check-performance.sh \
  --test-targeted-build-certs-controlled-error "$fake"

printf '%s\n' \
  '#!/usr/bin/env bash' \
  'echo "thread panicked" >&2' \
  'exit 2' >"$fake"
chmod 700 "$fake"
if bash scripts/check-performance.sh \
  --test-targeted-build-certs-controlled-error "$fake" >/dev/null 2>&1; then
  echo "controlled-error validator accepted a panic diagnostic" >&2
  exit 1
fi

echo "targeted build-certs controlled-error routing passed"
