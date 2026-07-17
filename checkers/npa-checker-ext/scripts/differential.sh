#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
EXT_ROOT="$ROOT/checkers/npa-checker-ext"
POLICY="$EXT_ROOT/test/fixtures/axiom-policy.toml"
EMPTY_IMPORTS="$EXT_ROOT/test/fixtures/import_store"
MANIFEST="$EXT_ROOT/test/conformance-manifest.tsv"
KNOWN_GAPS="$EXT_ROOT/test/known-gaps.tsv"

if [ "$(awk 'NR > 1 && NF > 0 { count++ } END { print count + 0 }' "$KNOWN_GAPS")" -ne 0 ]; then
  echo "known-gap manifest is not empty" >&2
  exit 1
fi

"$EXT_ROOT/scripts/build.sh"
cargo build --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-checker-ref
cargo build --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-checker-ref \
  --example verify_ext_reference
cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-checker-ref \
  --example verify_ext_reference
cargo build --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cert \
  --example verify_ext_fast
cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cert \
  --example verify_ext_fast
cargo build --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-api \
  --example validate_checker_raw

TMP_DIR=$(mktemp -d "${TMPDIR:-/tmp}/npa-checker-ext-differential.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT HUP INT TERM

GENERATED_FIXTURES="$TMP_DIR/generated"
cargo run --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cert \
  --example generate_ext_conformance -- "$GENERATED_FIXTURES"
for fixture in \
  indexed-v0.2.npcert \
  mutual-v0.2.npcert \
  nested-v0.2.npcert \
  nested-all-v0.2.npcert \
  imported-indexed-iota-v0.2.npcert \
  imported-mutual-iota-v0.2.npcert \
  forbidden-axiom-v0.2.npcert \
  unchecked-provider-bad-v0.2.npcert \
  unchecked-consumer-unpinned-v0.2.npcert \
  unchecked-consumer-pinned-v0.2.npcert
do
  cmp "$GENERATED_FIXTURES/$fixture" \
    "$EXT_ROOT/test/fixtures/conformance/$fixture"
done

json_string_field() {
  file=$1
  field=$2
  tr '\n' ' ' < "$file" |
    sed -n "s/.*\"$field\"[[:space:]]*:[[:space:]]*\"\([^\"]*\)\".*/\1/p"
}

compare_field() {
  label=$1
  field=$2
  reference=$3
  external=$4
  reference_value=$(json_string_field "$reference" "$field")
  external_value=$(json_string_field "$external" "$field")
  if [ "$reference_value" != "$external_value" ]; then
    echo "$label: $field differs: reference=$reference_value external=$external_value" >&2
    sed -n '1,80p' "$reference" >&2
    sed -n '1,80p' "$external" >&2
    return 1
  fi
}

manifest_field() {
  case_name=$1
  column=$2
  awk -F '\t' -v case_name="$case_name" -v column="$column" \
    '$2 == case_name { print $column; exit }' "$MANIFEST"
}

compare_manifest_field() {
  label=$1
  field=$2
  column=$3
  actual_file=$4
  expected=$(manifest_field "$label" "$column")
  if [ "$expected" = "-" ]; then
    expected=""
  fi
  actual=$(json_string_field "$actual_file" "$field")
  if [ "$expected" != "$actual" ]; then
    echo "$label: stale manifest $field: expected=$expected actual=$actual" >&2
    return 1
  fi
}

policy_hash() {
  if [ -f "$1" ]; then
    printf 'sha256:%s\n' "$(sha256sum "$1" | awk '{ print $1 }')"
  else
    printf 'sha256:%064d\n' 0
  fi
}

run_case_with_policy() {
  label=$1
  certificate=$2
  import_dir=$3
  policy=$4
  expected_policy_hash=$(policy_hash "$policy")
  reference_json="$TMP_DIR/$label.reference.json"
  fast_json="$TMP_DIR/$label.fast.json"
  external_json="$TMP_DIR/$label.external.json"

  fast_status=0
  "$ROOT/target/debug/examples/verify_ext_fast" \
    "$certificate" "$import_dir" "$policy" > "$fast_json" || fast_status=$?
  if [ "$fast_status" -gt 1 ]; then
    echo "$label: fast kernel invocation failed" >&2
    return 1
  fi

  reference_status=0
  "$ROOT/target/debug/examples/verify_ext_reference" \
    "$certificate" "$import_dir" "$policy" \
    > "$reference_json" || reference_status=$?
  if [ "$reference_status" -gt 1 ]; then
    echo "$label: reference checker invocation failed" >&2
    return 1
  fi

  external_status=0
  "$EXT_ROOT/_build/npa-checker-ext" \
    --cert "$certificate" --import-dir "$import_dir" --policy "$policy" \
    --policy-hash "$expected_policy_hash" \
    --output json > "$external_json" || external_status=$?
  if [ "$external_status" -gt 1 ]; then
    echo "$label: external checker invocation failed" >&2
    return 1
  fi

  for field in status module certificate_hash export_hash axiom_report_hash kind reason_code section
  do
    compare_field "$label" "$field" "$reference_json" "$external_json"
  done
  compare_field "$label" status "$reference_json" "$fast_json"
  if [ "$(json_string_field "$fast_json" status)" = "checked" ]; then
    for field in module certificate_hash export_hash axiom_report_hash
    do
      compare_field "$label" "$field" "$reference_json" "$fast_json"
    done
  fi
  compare_manifest_field "$label" status 5 "$external_json"
  compare_manifest_field "$label" module 6 "$external_json"
  compare_manifest_field "$label" certificate_hash 7 "$external_json"
  compare_manifest_field "$label" export_hash 8 "$external_json"
  compare_manifest_field "$label" axiom_report_hash 9 "$external_json"
  compare_manifest_field "$label" kind 10 "$external_json"
  compare_manifest_field "$label" reason_code 11 "$external_json"
  echo "$label: matched"
}

run_case() {
  run_case_with_policy "$1" "$2" "$3" "$POLICY"
}

assert_rust_source_path_rejected() {
  label=$1
  certificate=$2
  import_dir=$3
  policy=$4
  for driver in verify_ext_fast verify_ext_reference
  do
    output="$TMP_DIR/$label.$driver.json"
    status=0
    "$ROOT/target/debug/examples/$driver" \
      "$certificate" "$import_dir" "$policy" > "$output" || status=$?
    if [ "$status" -ne 1 ] || [ "$(json_string_field "$output" status)" != "failed" ]; then
      echo "$label: $driver accepted a forbidden source path" >&2
      return 1
    fi
  done
  echo "$label: rejected"
}

run_case legacy-positive \
  "$ROOT/testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert" \
  "$ROOT/testdata/package/npa-mathlib/vendor"
run_case previous-positive \
  "$ROOT/testdata/package/npa-mathlib-downstream/vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert" \
  "$ROOT/testdata/package/npa-mathlib-downstream/vendor"
run_case current-positive \
  "$ROOT/testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert" \
  "$ROOT/testdata/package/npa-mathlib-downstream/vendor"
EMPTY_LEAF="$TMP_DIR/empty-leaf.npcert"
: > "$EMPTY_LEAF"
run_case decoder-empty-leaf "$EMPTY_LEAF" "$EMPTY_IMPORTS"
MALFORMED_LEAF="$TMP_DIR/malformed-leaf.npcert"
printf '\001X' > "$MALFORMED_LEAF"
run_case decoder-malformed-leaf "$MALFORMED_LEAF" "$EMPTY_IMPORTS"
run_case decoder-noncanonical-leaf-preserves-identity \
  "$GENERATED_FIXTURES/noncanonical-unused-name-v0.2.npcert" \
  "$EMPTY_IMPORTS"
SOURCE_NAMED_LEAF="$TMP_DIR/source-named-leaf.npa"
cp "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" "$SOURCE_NAMED_LEAF"
assert_rust_source_path_rejected source-named-leaf "$SOURCE_NAMED_LEAF" \
  "$EMPTY_IMPORTS" "$POLICY"
NON_CERTIFICATE_LEAF="$TMP_DIR/non-certificate-leaf.bin"
cp "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" "$NON_CERTIFICATE_LEAF"
assert_rust_source_path_rejected non-certificate-leaf "$NON_CERTIFICATE_LEAF" \
  "$EMPTY_IMPORTS" "$POLICY"
SOURCE_NAMED_POLICY="$TMP_DIR/source-named-policy.npa"
cp "$POLICY" "$SOURCE_NAMED_POLICY"
assert_rust_source_path_rejected source-named-policy \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$SOURCE_NAMED_POLICY"
run_case decoder-missing-leaf "$TMP_DIR/missing-leaf.npcert" "$EMPTY_IMPORTS"
run_case dependency-hash-material-mismatch \
  "$GENERATED_FIXTURES/dependency-hash-mismatch-v0.2.npcert" \
  "$EMPTY_IMPORTS"
EQ_IMPORTS="$TMP_DIR/eq-imports"
mkdir -p "$EQ_IMPORTS/Std/Logic/Eq"
cp \
  "$ROOT/testdata/package/proofs/vendor/npa-std/Std/Logic/Eq/certificate.npcert" \
  "$EQ_IMPORTS/Std/Logic/Eq/certificate.npcert"
run_case checked-eq-interoperability \
  "$ROOT/testdata/package/proofs/Proofs/Ai/EqReasoning/certificate.npcert" \
  "$EQ_IMPORTS"
policy_status=0
"$EXT_ROOT/_build/npa-checker-ext" \
  --cert "$ROOT/testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert" \
  --import-dir "$ROOT/testdata/package/npa-mathlib-downstream/vendor" \
  --policy "$POLICY" --policy-hash "$(policy_hash "$POLICY")" --output json \
  > "$TMP_DIR/current-positive.external-repeat.json"
cmp "$TMP_DIR/current-positive.external.json" \
  "$TMP_DIR/current-positive.external-repeat.json"
run_case indexed-positive \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case mutual-positive \
  "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case nested-positive \
  "$EXT_ROOT/test/fixtures/conformance/nested-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case nested-all-positive \
  "$EXT_ROOT/test/fixtures/conformance/nested-all-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case imported-indexed-iota \
  "$EXT_ROOT/test/fixtures/conformance/imported-indexed-iota-v0.2.npcert" \
  "$EXT_ROOT/test/fixtures/conformance"
run_case imported-mutual-iota \
  "$EXT_ROOT/test/fixtures/conformance/imported-mutual-iota-v0.2.npcert" \
  "$EXT_ROOT/test/fixtures/conformance"
run_case semantic-provider-rejection \
  "$EXT_ROOT/test/fixtures/conformance/unchecked-provider-bad-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case high-trust-invalid-import \
  "$EXT_ROOT/test/fixtures/conformance/unchecked-consumer-pinned-v0.2.npcert" \
  "$EXT_ROOT/test/fixtures/conformance"
run_case high-trust-missing-pin \
  "$EXT_ROOT/test/fixtures/conformance/unchecked-consumer-unpinned-v0.2.npcert" \
  "$EXT_ROOT/test/fixtures/conformance"
DUPLICATE_IMPORTS="$TMP_DIR/duplicate-imports"
mkdir -p "$DUPLICATE_IMPORTS/one" "$DUPLICATE_IMPORTS/two"
cp "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  "$DUPLICATE_IMPORTS/one/certificate.npcert"
cp "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  "$DUPLICATE_IMPORTS/two/certificate.npcert"
run_case high-trust-duplicate-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$DUPLICATE_IMPORTS"
MALFORMED_CANDIDATE_IMPORTS="$TMP_DIR/malformed-candidate-imports"
mkdir -p "$MALFORMED_CANDIDATE_IMPORTS"
printf '\001X' > "$MALFORMED_CANDIDATE_IMPORTS/unrelated.npcert"
run_case high-trust-malformed-unrelated-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$MALFORMED_CANDIDATE_IMPORTS"
NONCANONICAL_CANDIDATE_IMPORTS="$TMP_DIR/noncanonical-candidate-imports"
mkdir -p "$NONCANONICAL_CANDIDATE_IMPORTS"
printf '\216\000' > "$NONCANONICAL_CANDIDATE_IMPORTS/unrelated.npcert"
dd if="$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  bs=1 skip=1 2>/dev/null >> \
  "$NONCANONICAL_CANDIDATE_IMPORTS/unrelated.npcert"
run_case high-trust-noncanonical-unrelated-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$NONCANONICAL_CANDIDATE_IMPORTS"
CORE_SPEC_MISMATCH_IMPORTS="$TMP_DIR/core-spec-mismatch-imports"
mkdir -p "$CORE_SPEC_MISMATCH_IMPORTS"
cp "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  "$CORE_SPEC_MISMATCH_IMPORTS/unrelated.npcert"
printf 'X' | dd of="$CORE_SPEC_MISMATCH_IMPORTS/unrelated.npcert" \
  bs=1 seek=16 conv=notrunc 2>/dev/null
run_case high-trust-core-spec-mismatch-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$CORE_SPEC_MISMATCH_IMPORTS"
INVALID_CANDIDATE_HASH_IMPORTS="$TMP_DIR/invalid-candidate-hash-imports"
mkdir -p "$INVALID_CANDIDATE_HASH_IMPORTS"
cp "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
  "$INVALID_CANDIDATE_HASH_IMPORTS/unrelated.npcert"
invalid_candidate_size=$(wc -c < \
  "$INVALID_CANDIDATE_HASH_IMPORTS/unrelated.npcert")
printf '\000' | dd of="$INVALID_CANDIDATE_HASH_IMPORTS/unrelated.npcert" \
  bs=1 seek=$((invalid_candidate_size - 1)) conv=notrunc 2>/dev/null
run_case high-trust-invalid-unrelated-candidate-hash \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$INVALID_CANDIDATE_HASH_IMPORTS"
SOURCE_SUBTREE_IMPORTS="$TMP_DIR/source-subtree-imports"
mkdir -p "$SOURCE_SUBTREE_IMPORTS/hidden.npa" \
  "$SOURCE_SUBTREE_IMPORTS/replay.json"
printf '\001X' > "$SOURCE_SUBTREE_IMPORTS/hidden.npa/unrelated.npcert"
printf '\001X' > "$SOURCE_SUBTREE_IMPORTS/replay.json/unrelated.npcert"
run_case high-trust-source-subtree-excluded \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$SOURCE_SUBTREE_IMPORTS"
REPLAY_PREFIX_IMPORTS="$TMP_DIR/replay-prefix-imports"
mkdir -p "$REPLAY_PREFIX_IMPORTS/replay.json.backup"
printf '\001X' > "$REPLAY_PREFIX_IMPORTS/replay.json.backup/unrelated.npcert"
run_case high-trust-replay-prefix-is-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$REPLAY_PREFIX_IMPORTS"
HIDDEN_CERTIFICATE_IMPORTS="$TMP_DIR/hidden-certificate-imports"
mkdir -p "$HIDDEN_CERTIFICATE_IMPORTS"
printf '\001X' > "$HIDDEN_CERTIFICATE_IMPORTS/.npcert"
run_case high-trust-hidden-certificate-is-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$HIDDEN_CERTIFICATE_IMPORTS"
UNRELATED_REGULAR_IMPORTS="$TMP_DIR/unrelated-regular-imports"
mkdir -p "$UNRELATED_REGULAR_IMPORTS"
printf 'must not be opened by any checker\n' > "$UNRELATED_REGULAR_IMPORTS/unrelated.txt"
run_case high-trust-unrelated-regular-excluded \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$UNRELATED_REGULAR_IMPORTS"
SYMLINK_IMPORT_TARGET="$TMP_DIR/symlink-import-target"
SYMLINK_IMPORTS="$TMP_DIR/symlink-imports"
mkdir -p "$SYMLINK_IMPORT_TARGET"
ln -s "$SYMLINK_IMPORT_TARGET" "$SYMLINK_IMPORTS"
run_case high-trust-symlink-import-root \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$SYMLINK_IMPORTS"
SYMLINK_ANCESTOR_REAL="$TMP_DIR/symlink-ancestor-real"
SYMLINK_ANCESTOR_ALIAS="$TMP_DIR/symlink-ancestor-alias"
mkdir -p "$SYMLINK_ANCESTOR_REAL/imports"
cp "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$SYMLINK_ANCESTOR_REAL/leaf.npcert"
cp "$POLICY" "$SYMLINK_ANCESTOR_REAL/policy.toml"
ln -s "$SYMLINK_ANCESTOR_REAL" "$SYMLINK_ANCESTOR_ALIAS"
run_case_with_policy high-trust-symlink-certificate-ancestor \
  "$SYMLINK_ANCESTOR_ALIAS/leaf.npcert" \
  "$SYMLINK_ANCESTOR_REAL/imports" "$POLICY"
run_case_with_policy high-trust-symlink-import-ancestor \
  "$SYMLINK_ANCESTOR_REAL/leaf.npcert" \
  "$SYMLINK_ANCESTOR_ALIAS/imports" "$POLICY"
run_case_with_policy high-trust-symlink-policy-ancestor \
  "$SYMLINK_ANCESTOR_REAL/leaf.npcert" \
  "$SYMLINK_ANCESTOR_REAL/imports" "$SYMLINK_ANCESTOR_ALIAS/policy.toml"
OVERSIZED_CANDIDATE_IMPORTS="$TMP_DIR/oversized-candidate-imports"
mkdir -p "$OVERSIZED_CANDIDATE_IMPORTS"
truncate -s 67108865 "$OVERSIZED_CANDIDATE_IMPORTS/unrelated.npcert"
run_case high-trust-oversized-unrelated-candidate \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$OVERSIZED_CANDIDATE_IMPORTS"
OVERSIZED_LEAF="$TMP_DIR/oversized-leaf.npcert"
truncate -s 67108865 "$OVERSIZED_LEAF"
run_case high-trust-oversized-leaf "$OVERSIZED_LEAF" "$EMPTY_IMPORTS"
CANDIDATE_LIMIT_IMPORTS="$TMP_DIR/candidate-limit-imports"
mkdir -p "$CANDIDATE_LIMIT_IMPORTS"
printf '\001X' > "$CANDIDATE_LIMIT_IMPORTS/00000.npcert"
candidate_index=1
while [ "$candidate_index" -le 4096 ]
do
  cp "$EXT_ROOT/test/fixtures/conformance/mutual-v0.2.npcert" \
    "$CANDIDATE_LIMIT_IMPORTS/$candidate_index.npcert"
  candidate_index=$((candidate_index + 1))
done
run_case high-trust-candidate-limit \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$CANDIDATE_LIMIT_IMPORTS"
run_case policy-forbidden-axiom \
  "$EXT_ROOT/test/fixtures/conformance/forbidden-axiom-v0.2.npcert" \
  "$EMPTY_IMPORTS"
run_case legacy-small-universe-attack \
  "$ROOT/testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert" \
  "$EMPTY_IMPORTS"
run_case current-mutual-small-universe-attack \
  "$ROOT/testdata/certificates/security/mutual-inductive-constructor-universe-bound-v0.2.npcert" \
  "$EMPTY_IMPORTS"

printf '%s\n' \
  'format = "npa.independent-checker.axiom_policy.v1"' \
  'allowed_axioms = []' \
  'deny_custom_axioms = false' > "$TMP_DIR/invalid-policy.toml"
run_case_with_policy policy-denial-override-rejected \
  "$EXT_ROOT/test/fixtures/conformance/forbidden-axiom-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/invalid-policy.toml"
run_case_with_policy policy-missing-file \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/missing-policy.toml"
printf '%s\n' \
  'format = "npa.independent-checker.axiom_policy.v1"' \
  'allowed_axioms = ["B", "AA"]' > "$TMP_DIR/canonical-order-policy.toml"
run_case_with_policy policy-canonical-name-order \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/canonical-order-policy.toml"
printf 'format\302\240=\302\240"npa.independent-checker.axiom_policy.v1"\nallowed_axioms\302\240=\302\240[]\n' \
  > "$TMP_DIR/unicode-whitespace-policy.toml"
run_case_with_policy policy-unicode-whitespace \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/unicode-whitespace-policy.toml"
printf '%s\n' \
  "format = 'npa.independent-checker.axiom_policy.v1'" \
  'allowed_axioms = []' > "$TMP_DIR/single-quoted-policy.toml"
run_case_with_policy policy-single-quoted-string-rejected \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/single-quoted-policy.toml"
printf '%s\n' \
  'format = "npa.independent-checker.axiom_policy.v1"' \
  'allowed_axioms = ["AA", "B"]' > "$TMP_DIR/order-violation-policy.toml"
run_case_with_policy policy-name-order-violation \
  "$EXT_ROOT/test/fixtures/conformance/indexed-v0.2.npcert" \
  "$EMPTY_IMPORTS" "$TMP_DIR/order-violation-policy.toml"

"$ROOT/target/debug/examples/validate_checker_raw" \
  "$TMP_DIR"/*.reference.json "$TMP_DIR"/*.external*.json

NPA_CHECKER_EXT_BINARY_PATH="$EXT_ROOT/_build/npa-checker-ext" \
  cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
    --test package_verify_certs \
    package_verify_external_real_ocaml_checker_closes_source_free_import_dag \
    -- --ignored --exact

"$EXT_ROOT/scripts/source-free-trace.sh"
