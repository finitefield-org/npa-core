#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
EXT_ROOT="$ROOT/checkers/npa-checker-ext"

CURRENT_VERSION=$(awk '
  /^name = "npa-cli"$/ { in_package = 1; next }
  in_package && /^version = "/ {
    value = $0
    sub(/^version = "/, "", value)
    sub(/"$/, "", value)
    print value
    exit
  }
' "$ROOT/crates/npa-cli/Cargo.toml")
if [ "$CURRENT_VERSION" != 0.7.0 ]; then
  echo "toolchain v0.7 compatibility requires npa-cli 0.7.0, found $CURRENT_VERSION" >&2
  exit 1
fi
MODE=full

case $# in
  0) ;;
  1)
    if [ "$1" != "--functional-only" ]; then
      echo "usage: $0 [--functional-only]" >&2
      exit 2
    fi
    MODE=functional
    ;;
  *)
    echo "usage: $0 [--functional-only]" >&2
    exit 2
    ;;
esac

for tool in awk basename cargo cmp cp find mkdir mktemp ocamlc rg rm rustc sed sha256sum sort xargs /usr/bin/git
do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "toolchain v0.7 compatibility requires $tool" >&2
    exit 1
  fi
done
if [ "$MODE" = full ]; then
  for tool in date gzip strace tar
  do
    if ! command -v "$tool" >/dev/null 2>&1; then
      echo "full toolchain v0.7 compatibility requires $tool" >&2
      exit 1
    fi
  done
fi

GIT_ROOT=$(/usr/bin/git -C "$ROOT" rev-parse --show-toplevel)
if [ "$MODE" = full ] && [ -n "$(/usr/bin/git -C "$GIT_ROOT" status --porcelain=v1 --untracked-files=all)" ]; then
  echo "full toolchain v0.7 compatibility requires a clean candidate checkout" >&2
  exit 1
fi

KNOWN_GAPS="$EXT_ROOT/test/known-gaps.tsv"
if [ "$(awk 'NR > 1 && NF > 0 { count++ } END { print count + 0 }' "$KNOWN_GAPS")" -ne 0 ]; then
  echo "known-gap manifest is not empty" >&2
  exit 1
fi

RUN_PARENT="$ROOT/target/npa-checker-ext-v0.7"
mkdir -p "$RUN_PARENT"
RUN_DIR=$(mktemp -d "$RUN_PARENT/run.XXXXXX")
trap 'rm -rf "$RUN_DIR"' EXIT HUP INT TERM
export CARGO_BUILD_JOBS=1
export LC_ALL=C.UTF-8
export LANG=C.UTF-8
export TZ=UTC

evidence() {
  cargo run --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
    --bin npa-checker-ext-toolchain-evidence -- "$@"
}

phase() {
  printf 'toolchain-v0.7: %s\n' "$1"
}

snapshot_proofs() {
  find "$ROOT/testdata/package" -type f -exec sha256sum {} + | sort
}
snapshot_proofs > "$RUN_DIR/proofs.before"

phase "real OCaml checker build and source-free differential"
"$EXT_ROOT/scripts/test.sh"
"$EXT_ROOT/scripts/build.sh"
CHECKER="$EXT_ROOT/_build/npa-checker-ext"
"$CHECKER" --version > "$RUN_DIR/checker-version.txt"
if [ "$MODE" = full ]; then
  "$EXT_ROOT/scripts/differential.sh"
fi

phase "locked offline host 0.7 metadata, build, API, and adapter gates"
cargo metadata --locked --offline --format-version 1 --no-deps \
  --manifest-path "$ROOT/Cargo.toml" > "$RUN_DIR/cargo-metadata.json"
evidence check-metadata --metadata "$RUN_DIR/cargo-metadata.json" >/dev/null

cargo build --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli --bin npa
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --example verify_ext_v0_7_facade
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --example inspect_ext_v0_7_policy
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test package_api_v1
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test package_cli_args
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test package_artifact_ledger
NPA_CHECKER_EXT_BINARY_PATH="$CHECKER" \
  cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
    --test package_verify_certs \
    package_verify_external_real_ocaml_checker_closes_source_free_import_dag \
    -- --ignored --exact
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test checker_ext_toolchain_evidence
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --lib checker_ext_toolchain_evidence::tests
test -d "$ROOT/testdata/release-manifest"
cargo test --locked --offline --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test release_manifest_validator

phase "deterministic fixture and v0.7 policy preflight"
FIXTURE_RECORD="$RUN_DIR/fixture.json"
evidence prepare-fixture \
  --run-dir "$RUN_DIR/work" \
  --fixture "$ROOT/testdata/package/npa-mathlib-downstream" \
  --core-root "$ROOT" > "$FIXTURE_RECORD"
SOURCE="$RUN_DIR/work/source"
PACKAGE="$SOURCE/proofs"
evidence prepare-inputs \
  --root "$PACKAGE" \
  --checker "$CHECKER" \
  --version-file "$RUN_DIR/checker-version.txt" > "$RUN_DIR/prepared-inputs.json"

cd "$SOURCE"
cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli \
  --example inspect_ext_v0_7_policy -- \
  --root proofs \
  --runner-policy ci/runner.release.json \
  --checker-registry ci/checker-binaries.json > "$RUN_DIR/preflight.json"
POLICY_HASH=$(evidence json-field --path "$RUN_DIR/preflight.json" --field runner_policy_sha256)

if [ "$MODE" = full ]; then
  evidence collect-build \
    --core-root "$ROOT" \
    --source-root "$SOURCE" \
    --fixture-record "$FIXTURE_RECORD" \
    --metadata "$RUN_DIR/cargo-metadata.json" \
    --preflight "$RUN_DIR/preflight.json" \
    --checker "$CHECKER" \
    --require-clean > "$RUN_DIR/build-identity.json"
fi

evidence inventory --root "$PACKAGE" \
  --extra "$ROOT/Cargo.lock" \
  --extra "$ROOT/target/debug/npa" \
  --extra "$CHECKER" > "$RUN_DIR/inventory-before.json"

TRACE_EXPR='%file,%network,%process,write,writev,pwrite64,pwritev,pwritev2,ftruncate'
clear_outputs() {
  label=$1
  rm -rf \
    "$PACKAGE/generated/checker-imports" \
    "$PACKAGE/generated/checker-results"
  printf '%s %s\n' "$label" 'generated/checker-imports generated/checker-results' \
    >> "$RUN_DIR/permitted-clears.log"
}

phase "v1 facade run"
if [ "$MODE" = full ]; then
  strace -ff -yy -qq -s 4096 -e "trace=$TRACE_EXPR" -o "$RUN_DIR/trace-facade" \
    cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli \
      --example verify_ext_v0_7_facade -- \
      --root proofs \
      --runner-policy ci/runner.release.json \
      --runner-policy-hash "$POLICY_HASH" \
      --checker-registry ci/checker-binaries.json \
      > "$RUN_DIR/facade.json"
else
  cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli \
    --example verify_ext_v0_7_facade -- \
    --root proofs \
    --runner-policy ci/runner.release.json \
    --runner-policy-hash "$POLICY_HASH" \
    --checker-registry ci/checker-binaries.json \
    > "$RUN_DIR/facade.json"
fi
evidence capture-run \
  --root "$PACKAGE" \
  --command-result "$RUN_DIR/facade.json" \
  --evidence-dir "$RUN_DIR/work/evidence/facade" \
  --fixture-record "$FIXTURE_RECORD" \
  --preflight "$RUN_DIR/preflight.json" > "$RUN_DIR/capture-facade.json"
if [ "$MODE" = full ]; then
  evidence check-trace \
    --trace-prefix "$RUN_DIR/trace-facade" \
    --source-root "$SOURCE" \
    --package-root "$PACKAGE" \
    --fixture-record "$FIXTURE_RECORD" > "$RUN_DIR/trace-facade.json"
fi

clear_outputs after-facade
phase "first direct locked/offline run"
if [ "$MODE" = full ]; then
  strace -ff -yy -qq -s 4096 -e "trace=$TRACE_EXPR" -o "$RUN_DIR/trace-direct-1" \
    cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
      package verify-certs \
      --root proofs \
      --package-lock checked \
      --checker external \
      --audit-cache off \
      --verifier-memo off \
      --jobs 1 \
      --runner-policy ci/runner.release.json \
      --runner-policy-hash "$POLICY_HASH" \
      --checker-registry ci/checker-binaries.json \
      --json > "$RUN_DIR/direct-1.json"
else
  cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
    package verify-certs \
    --root proofs \
    --package-lock checked \
    --checker external \
    --audit-cache off \
    --verifier-memo off \
    --jobs 1 \
    --runner-policy ci/runner.release.json \
    --runner-policy-hash "$POLICY_HASH" \
    --checker-registry ci/checker-binaries.json \
    --json > "$RUN_DIR/direct-1.json"
fi
evidence capture-run \
  --root "$PACKAGE" \
  --command-result "$RUN_DIR/direct-1.json" \
  --evidence-dir "$RUN_DIR/work/evidence/direct-1" \
  --fixture-record "$FIXTURE_RECORD" \
  --preflight "$RUN_DIR/preflight.json" > "$RUN_DIR/capture-direct-1.json"
if [ "$MODE" = full ]; then
  evidence check-trace \
    --trace-prefix "$RUN_DIR/trace-direct-1" \
    --source-root "$SOURCE" \
    --package-root "$PACKAGE" \
    --fixture-record "$FIXTURE_RECORD" > "$RUN_DIR/trace-direct-1.json"
fi

clear_outputs after-direct-1
phase "selected final direct locked/offline run"
if [ "$MODE" = full ]; then
  strace -ff -yy -qq -s 4096 -e "trace=$TRACE_EXPR" -o "$RUN_DIR/trace-direct-final" \
    cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
      package verify-certs \
      --root proofs \
      --package-lock checked \
      --checker external \
      --audit-cache off \
      --verifier-memo off \
      --jobs 1 \
      --runner-policy ci/runner.release.json \
      --runner-policy-hash "$POLICY_HASH" \
      --checker-registry ci/checker-binaries.json \
      --json > "$RUN_DIR/direct-final.json"
else
  cargo run --locked --offline -q --manifest-path npa-core/Cargo.toml -p npa-cli -- \
    package verify-certs \
    --root proofs \
    --package-lock checked \
    --checker external \
    --audit-cache off \
    --verifier-memo off \
    --jobs 1 \
    --runner-policy ci/runner.release.json \
    --runner-policy-hash "$POLICY_HASH" \
    --checker-registry ci/checker-binaries.json \
    --json > "$RUN_DIR/direct-final.json"
fi
evidence capture-run \
  --root "$PACKAGE" \
  --command-result "$RUN_DIR/direct-final.json" \
  --evidence-dir "$RUN_DIR/work/evidence/direct-final" \
  --fixture-record "$FIXTURE_RECORD" \
  --preflight "$RUN_DIR/preflight.json" > "$RUN_DIR/capture-direct-final.json"
if [ "$MODE" = full ]; then
  evidence check-trace \
    --trace-prefix "$RUN_DIR/trace-direct-final" \
    --source-root "$SOURCE" \
    --package-root "$PACKAGE" \
    --fixture-record "$FIXTURE_RECORD" > "$RUN_DIR/trace-direct-final.json"
fi

phase "repeatability, source-free, mutation, and protected-byte closure"
evidence compare-runs \
  --run "$RUN_DIR/work/evidence/facade" \
  --run "$RUN_DIR/work/evidence/direct-1" \
  --run "$RUN_DIR/work/evidence/direct-final" > "$RUN_DIR/comparison.json"
"$EXT_ROOT/scripts/source-free-trace.sh"
evidence inventory --root "$PACKAGE" \
  --extra "$ROOT/Cargo.lock" \
  --extra "$ROOT/target/debug/npa" \
  --extra "$CHECKER" > "$RUN_DIR/inventory-after.json"
cmp "$RUN_DIR/inventory-before.json" "$RUN_DIR/inventory-after.json"
if [ "$(/usr/bin/git -C "$SOURCE" rev-parse HEAD)" != "$(evidence json-field --path "$FIXTURE_RECORD" --field source_commit)" ]; then
  echo "temporary source HEAD changed" >&2
  exit 1
fi
if [ -n "$(/usr/bin/git -C "$SOURCE" status --porcelain=v1 --untracked-files=all)" ]; then
  echo "temporary source repository is not clean" >&2
  exit 1
fi

if [ "$MODE" = full ]; then
  phase "selected final-run archive, checksum, and v0.2 manifest"
  GENERATED_AT_UTC=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  evidence build-release \
    --source-root "$SOURCE" \
    --core-root "$ROOT" \
    --package-root "$PACKAGE" \
    --assets-root "$RUN_DIR/work/assets" \
    --fixture-record "$FIXTURE_RECORD" \
    --preflight "$RUN_DIR/preflight.json" \
    --build-record "$RUN_DIR/build-identity.json" \
    --final-evidence "$RUN_DIR/work/evidence/direct-final" \
    --generated-at-utc "$GENERATED_AT_UTC" > "$RUN_DIR/release-assets.json"
  ARCHIVE=$(evidence json-field --path "$RUN_DIR/release-assets.json" --field archive)
  CHECKSUM=$(evidence json-field --path "$RUN_DIR/release-assets.json" --field checksum)
  MANIFEST=$(evidence json-field --path "$RUN_DIR/release-assets.json" --field manifest)
  VALIDATION_ROOT="$RUN_DIR/validation"
  mkdir "$VALIDATION_ROOT"
  tar -xzf "$ARCHIVE" -C "$VALIDATION_ROOT"
  cp "$ARCHIVE" "$VALIDATION_ROOT/$(basename "$ARCHIVE")"
  (cd "$VALIDATION_ROOT" && sha256sum -c "$CHECKSUM")
  "$ROOT/scripts/validate-generated-artifact-release-manifest.sh" \
    --require-v0.2 "$MANIFEST" > "$RUN_DIR/release-validation.json"
fi

snapshot_proofs > "$RUN_DIR/proofs.after"
cmp "$RUN_DIR/proofs.before" "$RUN_DIR/proofs.after"
/usr/bin/git -C "$GIT_ROOT" diff --check
if [ "$MODE" = full ]; then
  FINAL_STATUS=$(/usr/bin/git -C "$GIT_ROOT" status --porcelain=v1 --untracked-files=all)
  if [ -n "$FINAL_STATUS" ]; then
    echo "full toolchain v0.7 compatibility changed the candidate checkout" >&2
    printf '%s\n' "$FINAL_STATUS" >&2
    exit 1
  fi
fi
if rg -l --hidden --glob '!.git/**' '^version https://git-lfs.github.com/spec/v1$' "$GIT_ROOT" > "$RUN_DIR/lfs-pointers.txt"; then
  echo "Git LFS pointer content is forbidden" >&2
  sed -n '1,20p' "$RUN_DIR/lfs-pointers.txt" >&2
  exit 1
fi
if find "$GIT_ROOT" -name .gitattributes -not -path '*/.git/*' -print0 |
  xargs -0 rg -n '(filter|diff|merge)=lfs' > "$RUN_DIR/lfs-rules.txt"; then
  echo "Git LFS filter rules are forbidden" >&2
  sed -n '1,20p' "$RUN_DIR/lfs-rules.txt" >&2
  exit 1
fi

if [ "$MODE" = functional ]; then
  echo "toolchain v0.7 functional compatibility passed; release evidence not evaluated"
else
  echo "toolchain v0.7.0 compatibility and release evidence passed"
fi
