#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
temporary_root=$(mktemp -d "${TMPDIR:-/tmp}/npa-cvr-script-test.XXXXXX")
temporary_root=$(cd "$temporary_root" && pwd -P)
trap '/bin/rm -rf -- "$temporary_root"' EXIT
mkdir -p "$temporary_root/bin" "$temporary_root/work/scripts" "$temporary_root/work/target/release/examples" "$temporary_root/output" "$temporary_root/tmp"
export TMPDIR="$temporary_root/tmp"
cp "$repository_root/scripts/check-certificate-validation-reuse-performance.sh" "$temporary_root/work/scripts/"

cat >"$temporary_root/bin/cargo" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
case " $* " in
  *" NPA_CVR_BENCH_MODE=controller "*) exit 97 ;;
esac
mode=${NPA_CVR_BENCH_MODE:-}
case "$mode" in
  controller)
    [[ -n ${NPA_CVR_BENCH_RUN_JSON:-} && ! -e $NPA_CVR_BENCH_RUN_JSON ]]
    [[ ${NPA_CVR_BENCH_WORK_DIR:-} = /* && -d $NPA_CVR_BENCH_WORK_DIR ]]
    [[ -z $(find "$NPA_CVR_BENCH_WORK_DIR" -mindepth 1 -print -quit) ]]
    [[ $(stat -f '%Lp' "$NPA_CVR_BENCH_WORK_DIR") = 700 ]]
    [[ ${NPA_BENCH_SOURCE_IDENTITY:-} =~ ^[0-9a-f]{40}(-dirty)?$ ]]
    printf '{"schema":"npa.certificate-validation-pass-reuse.run.v0.2","rows":[],"summaries":[]}' >"$NPA_CVR_BENCH_RUN_JSON"
    case ${NPA_TEST_CVR_WORK_DIR_MUTATION:-} in
      "") rmdir "$NPA_CVR_BENCH_WORK_DIR" ;;
      nested) mkdir "$NPA_CVR_BENCH_WORK_DIR/unexpected" ;;
      regular) printf 'unexpected\n' >"$NPA_CVR_BENCH_WORK_DIR/unexpected.txt" ;;
      replace)
        rmdir "$NPA_CVR_BENCH_WORK_DIR"
        ln -s "${NPA_CVR_BENCH_RUN_JSON%/*}" "$NPA_CVR_BENCH_WORK_DIR"
        ;;
      replace-dir)
        rmdir "$NPA_CVR_BENCH_WORK_DIR"
        mkdir -m 700 "$NPA_CVR_BENCH_WORK_DIR"
        ;;
      *) exit 99 ;;
    esac
    ;;
  validator)
    [[ -f ${NPA_CVR_BENCH_RUN_JSON:-} ]]
    [[ -z ${NPA_CVR_BENCH_WORK_DIR:-} ]]
    [[ ${NPA_BENCH_SOURCE_IDENTITY:-} =~ ^[0-9a-f]{40}(-dirty)?$ ]]
    grep -q '"schema":"npa.certificate-validation-pass-reuse.run.v0.2"' "$NPA_CVR_BENCH_RUN_JSON"
    ;;
  "") ;;
  *) exit 98 ;;
esac
EOF
chmod +x "$temporary_root/bin/cargo" "$temporary_root/work/scripts/check-certificate-validation-reuse-performance.sh"
printf '#!/bin/sh\nexit 0\n' >"$temporary_root/work/target/release/examples/measure_process"
chmod +x "$temporary_root/work/target/release/examples/measure_process"
(
  cd "$temporary_root/work"
  /usr/bin/git init -q
  /usr/bin/git add .
  /usr/bin/git -c user.name=CVR -c user.email=cvr@example.invalid commit -qm fixture
)

report="$temporary_root/output/report.json"
report=$(cd "$temporary_root/output" && pwd -P)/report.json
(
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh --output "$report"
)
[[ -f "$report" ]]
[[ $(find "$temporary_root/output" -mindepth 1 -maxdepth 1 -type f | wc -l | tr -d ' ') = 1 ]]
[[ -z $(find "$temporary_root/output" -mindepth 1 -maxdepth 1 ! -name report.json -print -quit) ]]

if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh --output "$report"
) >/dev/null 2>&1; then
  echo "CVR script replaced an existing report" >&2
  exit 1
fi

for invalid in "" "relative.json"; do
  args=()
  if [[ -n $invalid ]]; then args=(--output "$invalid"); fi
  if (
    cd "$temporary_root/work"
    PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh "${args[@]}"
  ) >/dev/null 2>&1; then
    echo "CVR script accepted invalid output arguments" >&2
    exit 1
  fi
done

mkdir "$temporary_root/output/real-parent"
ln -s "$temporary_root/output/real-parent" "$temporary_root/output/linked-parent"
for invalid_output in \
  "$temporary_root/output/linked-parent/symlink-parent.json" \
  "$temporary_root/output/real-parent/../dot-component.json" \
  "$temporary_root/output/-unsafe.json"
do
  if (
    cd "$temporary_root/work"
    PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh \
      --output "$invalid_output"
  ) >/dev/null 2>&1; then
    echo "CVR script accepted noncanonical or unsafe output: $invalid_output" >&2
    exit 1
  fi
done
ln -s missing "$temporary_root/output/dangling.json"
if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh \
    --output "$temporary_root/output/dangling.json"
) >/dev/null 2>&1; then
  echo "CVR script accepted a dangling output target" >&2
  exit 1
fi

ln -s "$temporary_root" "$temporary_root/tmp-link"
printf 'not a directory\n' >"$temporary_root/tmp-file"
for invalid_tmpdir in "relative" "$temporary_root/../$(basename "$temporary_root")" "$temporary_root/tmp-link" "$temporary_root/tmp-file"; do
  if (
    cd "$temporary_root/work"
    TMPDIR="$invalid_tmpdir" PATH="$temporary_root/bin:/usr/bin:/bin" \
      scripts/check-certificate-validation-reuse-performance.sh \
      --output "$temporary_root/output/tmpdir-rejected.json"
  ) >/dev/null 2>&1; then
    echo "CVR script accepted unsafe TMPDIR: $invalid_tmpdir" >&2
    exit 1
  fi
done

for mutation in nested regular replace replace-dir; do
  if (
    cd "$temporary_root/work"
    NPA_TEST_CVR_WORK_DIR_MUTATION="$mutation" \
      PATH="$temporary_root/bin:/usr/bin:/bin" \
      scripts/check-certificate-validation-reuse-performance.sh \
      --output "$temporary_root/output/cleanup-$mutation.json"
  ) >/dev/null 2>&1; then
    echo "CVR script accepted unsafe temporary cleanup mutation: $mutation" >&2
    exit 1
  fi
done

mv "$temporary_root/work/target/release/examples/measure_process" "$temporary_root/real-measure-process"
ln -s "$temporary_root/real-measure-process" "$temporary_root/work/target/release/examples/measure_process"
if (
  cd "$temporary_root/work"
  PATH="$temporary_root/bin:/usr/bin:/bin" scripts/check-certificate-validation-reuse-performance.sh \
    --output "$temporary_root/output/second.json"
) >/dev/null 2>&1; then
  echo "CVR script accepted a symlinked measure_process executable" >&2
  exit 1
fi

echo "CVR persistent output and validator routing test passed"
