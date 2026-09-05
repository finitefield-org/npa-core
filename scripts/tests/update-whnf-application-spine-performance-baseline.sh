#!/usr/bin/env bash
set -euo pipefail

source_root=$(cd "$(dirname "$0")/../.." && pwd)
temporary_parent=$(cd "${TMPDIR:-/tmp}" && pwd -P)
temporary_root=$(mktemp -d "$temporary_parent/npa-whnf-updater-test.XXXXXX")
case "$temporary_root" in
  "$temporary_parent"/npa-whnf-updater-test.*) ;;
  *) echo "unexpected temporary root: $temporary_root" >&2; exit 1 ;;
esac
cleanup() {
  case "$temporary_root" in
    "$temporary_parent"/npa-whnf-updater-test.*)
      [[ -d "$temporary_root" ]] && rm -rf -- "$temporary_root"
      ;;
    *) return 1 ;;
  esac
}
trap cleanup EXIT
private_tmp="$temporary_root/tmp"
mkdir "$private_tmp"
private_tmp=$(cd "$private_tmp" && pwd -P)

repository="$temporary_root/repository"
core="$repository/npa-core"
archive="$temporary_root/archive"
test_bin="$temporary_root/bin"
mkdir -p \
  "$test_bin" \
  "$core/scripts" \
  "$core/target/release/examples" \
  "$core/testdata/performance/fixtures" \
  "$core/testdata/performance/baselines/elapsed" \
  "$archive/crates/npa-api/examples" \
  "$archive/crates/npa-cli/examples" \
  "$archive/target/release/examples"
cp "$source_root/scripts/update-whnf-application-spine-performance-baseline.sh" \
  "$core/scripts/update-whnf-application-spine-performance-baseline.sh"
chmod +x "$core/scripts/update-whnf-application-spine-performance-baseline.sh"

cat >"$test_bin/rustc" <<'EOF'
#!/usr/bin/env bash
printf 'rustc 1.0.0 (hermetic)\nhost: x86_64-unknown-linux-gnu\n'
EOF
cat >"$test_bin/cargo" <<'EOF'
#!/usr/bin/env bash
[[ ${NPA_BENCH_SOURCE_IDENTITY:-} =~ ^[0-9a-f]{40}$ ]] || exit 96
exit 0
EOF
chmod +x "$test_bin/rustc" "$test_bin/cargo"

cat >"$core/target/release/examples/bench_whnf_application_spine" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >>"${NPA_WHNF_TEST_LOG:?}"
case " $* " in
  *" --phase recursive "*)
    echo "post-switch test double received recursive execution" >&2
    exit 91
    ;;
  *" --validate-bootstrap-profile "*)
    exit 0
    ;;
  *" --collect-archived-recursive-baseline "*)
    output=""
    while [[ $# -gt 0 ]]; do
      case "$1" in
        --output) output=$2; shift 2 ;;
        *) shift ;;
      esac
    done
    printf '{"raw_recursive_report":true}\n' >"$output"
    ;;
  *)
    echo "unexpected post-switch invocation" >&2
    exit 92
    ;;
esac
EOF
chmod +x "$core/target/release/examples/bench_whnf_application_spine"
for role in check_whnf_application_spine_package measure_process; do
  cat >"$core/target/release/examples/$role" <<'EOF'
#!/usr/bin/env bash
exit 94
EOF
  chmod +x "$core/target/release/examples/$role"
done

cat >"$archive/target/release/examples/bench_whnf_application_spine" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf 'archived %s\n' "$*" >>"${NPA_WHNF_TEST_LOG:?}"
phase=""
output=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --phase) phase=$2; shift 2 ;;
    --output) output=$2; shift 2 ;;
    *) shift ;;
  esac
done
[[ "$phase" == "recursive" ]]
printf '{"raw_recursive_report":true}\n' >"$output"
EOF
chmod +x "$archive/target/release/examples/bench_whnf_application_spine"
for role in check_whnf_application_spine_package measure_process; do
  cat >"$archive/target/release/examples/$role" <<'EOF'
#!/usr/bin/env bash
exit 93
EOF
  chmod +x "$archive/target/release/examples/$role"
done
printf 'archived micro source\n' >"$archive/crates/npa-api/examples/bench_whnf_application_spine.rs"
printf 'archived package source\n' >"$archive/crates/npa-api/examples/check_whnf_application_spine_package.rs"
printf 'archived measure source\n' >"$archive/crates/npa-cli/examples/measure_process.rs"

printf '{}\n' >"$core/testdata/performance/fixtures/kernel-whnf-application-spine.v0.1.json"
printf '{}\n' >"$core/testdata/performance/baselines/kernel-whnf-application-spine.measurements.v0.2.json"
cat >"$core/profile.json" <<'EOF'
{"schema":"npa.kernel-whnf-application-spine.elapsed-profile.v0.1","profile_id":"kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1","target":"x86_64-unknown-linux-gnu","cargo_profile":"release","baseline_path":"testdata/performance/baselines/elapsed/kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1.baseline.v0.1.json","review_reason":"reviewed hermetic fixture"}
EOF
printf '{"archive_root":"%s"}\n' "$archive" >"$core/artifact.json"

(
  cd "$repository"
  /usr/bin/git init -q
  /usr/bin/git config user.name "NPA hermetic test"
  /usr/bin/git config user.email "npa-hermetic@example.invalid"
  /usr/bin/git add npa-core
  /usr/bin/git commit -qm "fixture"
)

log="$temporary_root/invocations.log"
archive_link="$temporary_root/archive-link"
ln -s "$archive" "$archive_link"
printf '{"archive_root":"%s"}\n' "$archive_link" >"$temporary_root/root-symlink-artifact.json"
if root_error=$(
  cd "$core"
  PATH="$test_bin:$PATH" TMPDIR="$private_tmp" NPA_WHNF_TEST_LOG="$log" scripts/update-whnf-application-spine-performance-baseline.sh \
    --elapsed-profile profile.json \
    --reason "reject root symlink" \
    --archived-artifact "$temporary_root/root-symlink-artifact.json" 2>&1
); then
  echo "archive-root symlink unexpectedly accepted" >&2
  exit 1
fi
grep -q 'archived artifact root must not be a symbolic link' <<<"$root_error"

archived_micro="$archive/target/release/examples/bench_whnf_application_spine"
outside_micro="$temporary_root/outside-archived-micro"
mv "$archived_micro" "$outside_micro"
ln -s "$outside_micro" "$archived_micro"
if binary_error=$(
  cd "$core"
  PATH="$test_bin:$PATH" TMPDIR="$private_tmp" NPA_WHNF_TEST_LOG="$log" scripts/update-whnf-application-spine-performance-baseline.sh \
    --elapsed-profile profile.json \
    --reason "reject binary symlink" \
    --archived-artifact artifact.json 2>&1
); then
  echo "archived binary symlink unexpectedly accepted" >&2
  exit 1
fi
grep -q 'archived artifact path must not contain symbolic links' <<<"$binary_error"
rm -f "$archived_micro"
mv "$outside_micro" "$archived_micro"

(
  cd "$core"
  PATH="$test_bin:$PATH" TMPDIR="$private_tmp" NPA_WHNF_TEST_LOG="$log" scripts/update-whnf-application-spine-performance-baseline.sh \
    --elapsed-profile profile.json \
    --reason "reviewed hermetic fixture" \
    --archived-artifact artifact.json
)

baseline="$core/testdata/performance/baselines/elapsed/kernel-whnf-application-spine.reviewed-linux-x86_64-release-v1.baseline.v0.1.json"
[[ $(cat "$baseline") == '{"raw_recursive_report":true}' ]]
[[ $(grep -c -- '--validate-bootstrap-profile' "$log") -eq 1 ]]
[[ $(grep -c -- '--collect-archived-recursive-baseline' "$log") -eq 1 ]]
! grep -q -- '--phase recursive' "$log"

printf 'dirty\n' >>"$core/profile.json"
if (
  cd "$core"
  PATH="$test_bin:$PATH" TMPDIR="$private_tmp" NPA_WHNF_TEST_LOG="$log" scripts/update-whnf-application-spine-performance-baseline.sh \
    --elapsed-profile profile.json \
    --reason "must fail dirty" \
    --archived-artifact artifact.json
) >/dev/null 2>&1; then
  echo "dirty checkout unexpectedly accepted" >&2
  exit 1
fi

echo "WHNF archived-baseline updater hermetic test passed"
