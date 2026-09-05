#!/bin/sh
set -eu

repository_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
temporary_dir=
temporary_dir_identity=

path_identity() {
    stat -f '%d:%i' "$1" 2>/dev/null || stat -c '%d:%i' "$1"
}

expected_temporary_entry() {
    candidate_name=$1
    for candidate_scenario in \
        cvr-valid-1k \
        cvr-valid-1m \
        cvr-valid-near-byte-limit \
        cvr-valid-wide-levels \
        cvr-valid-deep-term-dag \
        cvr-valid-wide-term-dag \
        cvr-malformed-early-level-reference \
        cvr-malformed-middle-term-order \
        cvr-malformed-late-certificate-hash
    do
        for candidate_sample in 0 1 2 3 4 5 6 7 8; do
            for candidate_suffix in json stdout stderr; do
                if [ "$candidate_name" = "$candidate_scenario-$candidate_sample.$candidate_suffix" ]; then
                    return 0
                fi
            done
        done
    done
    return 1
}

cleanup_temporary_dir() {
    cleanup_status=$?
    trap - EXIT HUP INT TERM
    if [ -n "$temporary_dir" ]; then
        cleanup_failed=false
        if [ ! -e "$temporary_dir" ] && [ ! -L "$temporary_dir" ]; then
            # Success path: the Rust controller removed the exact 243-file
            # catalog and its root through retained root/parent descriptors.
            :
        elif [ -L "$temporary_dir" ] || [ ! -d "$temporary_dir" ]; then
            echo "refusing to clean replaced CVR temporary directory: $temporary_dir" >&2
            cleanup_failed=true
        elif [ "$(CDPATH= cd -- "$temporary_dir" && pwd -P)" != "$temporary_dir" ]; then
            echo "refusing to clean noncanonical CVR temporary directory: $temporary_dir" >&2
            cleanup_failed=true
        elif [ "$(path_identity "$temporary_dir")" != "$temporary_dir_identity" ]; then
            echo "refusing to clean replaced CVR temporary directory identity: $temporary_dir" >&2
            cleanup_failed=true
        else
            echo "refusing CVR temporary directory left behind after controller cleanup: $temporary_dir" >&2
            cleanup_failed=true
        fi
        if [ "$cleanup_failed" = true ] && [ "$cleanup_status" -eq 0 ]; then
            cleanup_status=1
        fi
    fi
    exit "$cleanup_status"
}

trap cleanup_temporary_dir EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

usage() {
    echo "usage: $0 --output PATH" >&2
    exit 2
}

if [ "$#" -ne 2 ] || [ "$1" != "--output" ]; then
    usage
fi
case "$2" in
    /*) run_json=$2 ;;
    *) echo "--output must be an absolute path" >&2; exit 2 ;;
esac
if [ -e "$run_json" ] || [ -L "$run_json" ]; then
    echo "refusing to replace existing output: $run_json" >&2
    exit 1
fi
output_parent=${run_json%/*}
if [ -z "$output_parent" ] || [ -L "$output_parent" ] || [ ! -d "$output_parent" ]; then
    echo "output parent must already exist: $output_parent" >&2
    exit 1
fi
canonical_output_parent=$(CDPATH= cd -- "$output_parent" && pwd -P)
output_basename=${run_json##*/}
case "$output_basename" in
    ''|*[!A-Za-z0-9._-]*|[!A-Za-z0-9]*)
        echo "invalid output basename" >&2
        exit 1
        ;;
esac
canonical_run_json="$canonical_output_parent/$output_basename"
if [ "$canonical_run_json" != "$run_json" ]; then
    echo "--output must already be canonical and contain no symbolic-link or dot components" >&2
    exit 1
fi
run_json=$canonical_run_json

temporary_parent=${TMPDIR:-/tmp}
case "$temporary_parent" in
    /*) ;;
    *) echo "TMPDIR must be absolute" >&2; exit 1 ;;
esac
case "/$temporary_parent/" in
    */../*|*/./*) echo "TMPDIR must not contain dot components" >&2; exit 1 ;;
esac
if [ -L "$temporary_parent" ] || [ ! -d "$temporary_parent" ]; then
    echo "TMPDIR must name a real directory" >&2
    exit 1
fi
requested_temporary_parent=$temporary_parent
temporary_parent=$(CDPATH= cd -- "$temporary_parent" && pwd -P)
if [ "$temporary_parent" != "$requested_temporary_parent" ]; then
    echo "TMPDIR must already be canonical and contain no symbolic-link components" >&2
    exit 1
fi
if [ -L "$temporary_parent" ] || [ ! -d "$temporary_parent" ]; then
    echo "canonical TMPDIR must name a real directory" >&2
    exit 1
fi
temporary_dir=$(mktemp -d "$temporary_parent/npa-cvr-benchmark.XXXXXX")
if [ -L "$temporary_dir" ] || [ ! -d "$temporary_dir" ]; then
    echo "mktemp did not create a real CVR directory" >&2
    exit 1
fi
canonical_temporary_dir=$(CDPATH= cd -- "$temporary_dir" && pwd -P)
if [ "$canonical_temporary_dir" != "$temporary_dir" ] \
    || [ "${temporary_dir%/*}" != "$temporary_parent" ]; then
    echo "mktemp created an unexpected CVR directory" >&2
    exit 1
fi
temporary_dir=$canonical_temporary_dir
temporary_dir_identity=$(path_identity "$temporary_dir")
if [ -z "$temporary_dir_identity" ]; then
    echo "could not bind CVR temporary directory identity" >&2
    exit 1
fi
if [ "$(stat -f '%Lp' "$temporary_dir" 2>/dev/null || stat -c '%a' "$temporary_dir")" != 700 ]; then
    echo "CVR temporary directory must have mode 0700" >&2
    exit 1
fi

source_oid=$(/usr/bin/git -C "$repository_dir" rev-parse HEAD)
case "$source_oid" in
    *[!0-9a-f]*)
        echo "Git HEAD is not a lowercase 40-digit OID" >&2
        exit 1
        ;;
esac
if [ "${#source_oid}" -ne 40 ]; then
    echo "Git HEAD is not a lowercase 40-digit OID" >&2
    exit 1
fi
source_identity=$source_oid
if [ -n "$(/usr/bin/git -C "$repository_dir" status --porcelain --untracked-files=normal)" ]; then
    source_identity="${source_oid}-dirty"
fi

cd "$repository_dir"
NPA_BENCH_SOURCE_IDENTITY="$source_identity" \
cargo build --locked --offline --release -p npa-cli --example measure_process
measure_process="$repository_dir/target/release/examples/measure_process"
if [ ! -x "$measure_process" ] || [ ! -f "$measure_process" ] || [ -L "$measure_process" ]; then
    echo "missing executable measure_process: $measure_process" >&2
    exit 1
fi
canonical_measure_process=$(CDPATH= cd -- "${measure_process%/*}" && pwd -P)/${measure_process##*/}
if [ "$canonical_measure_process" != "$measure_process" ]; then
    echo "measure_process must have a canonical non-symlink path" >&2
    exit 1
fi

NPA_CVR_BENCH_MODE=controller \
NPA_CVR_BENCH_WORK_DIR="$temporary_dir" \
NPA_MEASURE_PROCESS="$measure_process" \
NPA_CVR_BENCH_RUN_JSON="$run_json" \
NPA_BENCH_SOURCE_IDENTITY="$source_identity" \
cargo test --locked --offline --release -p npa-cert --lib \
    verify::validation_reuse_benchmark_tests::validation_reuse_release_benchmark \
    -- --exact --ignored

if [ ! -f "$run_json" ]; then
    echo "benchmark did not produce $run_json" >&2
    exit 1
fi

NPA_CVR_BENCH_MODE=validator \
NPA_MEASURE_PROCESS="$measure_process" \
NPA_CVR_BENCH_RUN_JSON="$run_json" \
NPA_BENCH_SOURCE_IDENTITY="$source_identity" \
cargo test --locked --offline --release -p npa-cert --lib \
    verify::validation_reuse_benchmark_tests::validation_reuse_release_benchmark \
    -- --exact --ignored

echo "wrote $run_json"
