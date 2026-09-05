#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
EXT_ROOT="$ROOT/checkers/npa-checker-ext"
POLICY="$EXT_ROOT/test/fixtures/axiom-policy.toml"
EMPTY_IMPORTS="$EXT_ROOT/test/fixtures/import_store"
MATRIX="$ROOT/testdata/certificate-v0.4/fixture-matrix.tsv"
KNOWN_GAPS="$EXT_ROOT/test/known-gaps.tsv"

if [ "$(awk 'NR > 1 && NF > 0 { count++ } END { print count + 0 }' "$KNOWN_GAPS")" -ne 0 ]; then
  echo "known-gap manifest is not empty" >&2
  exit 1
fi
if [ "$(awk 'NR > 1 && NF > 0 { count++ } END { print count + 0 }' "$MATRIX")" -ne 72 ]; then
  echo "v0.4 fixture matrix does not contain exactly 72 cases" >&2
  exit 1
fi

"$EXT_ROOT/scripts/test.sh"
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
cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-api \
  ods12_
cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --example verify_ext_v0_8_facade
cargo test --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cli \
  --test package_verify_certs \
  package_verify_external_requires_explicit_policy_and_registry -- --exact

TMP_DIR=$(mktemp -d "$ROOT/target/npa-checker-ext-differential.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT HUP INT TERM

GENERATED_FIXTURES="$TMP_DIR/generated"
cargo run --locked --offline -q --manifest-path "$ROOT/Cargo.toml" -p npa-cert \
  --example generate_ext_conformance -- "$GENERATED_FIXTURES"

FIXTURES='
dependency-hash-mismatch-v0.4.npcert
forbidden-axiom-v0.4.npcert
imported-indexed-iota-v0.4.npcert
imported-mutual-iota-v0.4.npcert
indexed-v0.4.npcert
invalid-target-v0.4.npcert
mutual-v0.4.npcert
nested-all-v0.4.npcert
nested-v0.4.npcert
noncanonical-unused-name-v0.4.npcert
opaque-alias-chain-v0.4.npcert
opaque-direct-v0.4.npcert
stale-implementation-hash-v0.4.npcert
unchecked-consumer-pinned-v0.4.npcert
unchecked-consumer-unpinned-v0.4.npcert
unchecked-provider-bad-v0.4.npcert
'
fixture_count=0
for fixture in $FIXTURES
do
  cmp "$GENERATED_FIXTURES/$fixture" \
    "$EXT_ROOT/test/fixtures/conformance/$fixture"
  fixture_count=$((fixture_count + 1))
done
if [ "$fixture_count" -ne 16 ] || \
   [ "$(find "$GENERATED_FIXTURES" -type f -name '*.npcert' | wc -l | tr -d ' ')" -ne 16 ]; then
  echo "v0.4 conformance fixture set is not exactly the reviewed 16 files" >&2
  exit 1
fi

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

assert_field() {
  label=$1
  file=$2
  field=$3
  expected=$4
  actual=$(json_string_field "$file" "$field")
  if [ "$actual" != "$expected" ]; then
    echo "$label: expected $field=$expected, got $actual" >&2
    sed -n '1,80p' "$file" >&2
    return 1
  fi
}

policy_hash() {
  printf 'sha256:%s\n' "$(sha256sum "$1" | awk '{ print $1 }')"
}

run_case() {
  label=$1
  expected_status=$2
  expected_kind=$3
  expected_reason=$4
  certificate=$5
  import_dir=$6
  expected_policy_hash=$(policy_hash "$POLICY")
  reference_json="$TMP_DIR/$label.reference.json"
  fast_json="$TMP_DIR/$label.fast.json"
  external_json="$TMP_DIR/$label.external.json"

  fast_status=0
  "$ROOT/target/debug/examples/verify_ext_fast" \
    "$certificate" "$import_dir" "$POLICY" > "$fast_json" || fast_status=$?
  reference_status=0
  "$ROOT/target/debug/examples/verify_ext_reference" \
    "$certificate" "$import_dir" "$POLICY" > "$reference_json" || reference_status=$?
  external_status=0
  "$EXT_ROOT/_build/npa-checker-ext" \
    --cert "$certificate" --import-dir "$import_dir" --policy "$POLICY" \
    --policy-hash "$expected_policy_hash" --output json \
    > "$external_json" || external_status=$?

  if [ "$fast_status" -gt 1 ] || [ "$reference_status" -gt 1 ] || \
     [ "$external_status" -gt 1 ]; then
    echo "$label: checker invocation failed" >&2
    return 1
  fi
  if [ "$expected_status" = checked ]; then
    expected_exit=0
  else
    expected_exit=1
  fi
  if [ "$fast_status" -ne "$expected_exit" ] || \
     [ "$reference_status" -ne "$expected_exit" ] || \
     [ "$external_status" -ne "$expected_exit" ]; then
    echo "$label: unexpected checker exit status" >&2
    return 1
  fi

  assert_field "$label" "$fast_json" status "$expected_status"
  assert_field "$label" "$reference_json" status "$expected_status"
  assert_field "$label" "$external_json" status "$expected_status"
  assert_field "$label" "$external_json" checker_version 0.4.0
  assert_field "$label" "$external_json" certificate_format NPA-CERT-0.4.0
  assert_field "$label" "$external_json" core_spec NPA-Core-0.4.0

  for field in certificate_format core_spec status
  do
    compare_field "$label" "$field" "$reference_json" "$external_json"
  done

  if [ "$expected_kind" != - ]; then
    assert_field "$label" "$external_json" kind "$expected_kind"
  fi
  if [ "$expected_reason" != - ]; then
    assert_field "$label" "$external_json" reason_code "$expected_reason"
  fi
  if [ "$expected_status" = checked ]; then
    assert_field "$label" "$external_json" input_certificate_format NPA-CERT-0.4.0
    assert_field "$label" "$external_json" input_core_spec NPA-Core-0.4.0
    for field in input_certificate_format input_core_spec
    do
      compare_field "$label" "$field" "$reference_json" "$external_json"
    done
    for field in module certificate_hash export_hash axiom_report_hash
    do
      compare_field "$label" "$field" "$reference_json" "$external_json"
      compare_field "$label" "$field" "$reference_json" "$fast_json"
    done
  fi
  echo "$label: matched"
}

CONFORMANCE="$EXT_ROOT/test/fixtures/conformance"
INDEXED_IMPORTS="$TMP_DIR/indexed-imports"
MUTUAL_IMPORTS="$TMP_DIR/mutual-imports"
BAD_IMPORTS="$TMP_DIR/bad-imports"
mkdir "$INDEXED_IMPORTS" "$MUTUAL_IMPORTS" "$BAD_IMPORTS"
cp "$CONFORMANCE/indexed-v0.4.npcert" "$INDEXED_IMPORTS/provider.npcert"
cp "$CONFORMANCE/mutual-v0.4.npcert" "$MUTUAL_IMPORTS/provider.npcert"
cp "$CONFORMANCE/unchecked-provider-bad-v0.4.npcert" "$BAD_IMPORTS/provider.npcert"

write_import_header_variant() {
  output_dir=$1
  format=$2
  core_spec=$3
  mkdir "$output_dir"
  output="$output_dir/provider.npcert"
  cp "$CONFORMANCE/mutual-v0.4.npcert" "$output"
  if [ "$(dd if="$output" bs=1 skip=1 count=14 2>/dev/null)" != "NPA-CERT-0.4.0" ] || \
     [ "$(dd if="$output" bs=1 skip=16 count=14 2>/dev/null)" != "NPA-Core-0.4.0" ]; then
    echo "unexpected v0.4 provider header layout" >&2
    exit 1
  fi
  printf '%s' "$format" | dd of="$output" bs=1 seek=1 conv=notrunc 2>/dev/null
  printf '%s' "$core_spec" | dd of="$output" bs=1 seek=16 conv=notrunc 2>/dev/null
}

OLD_PAIR_IMPORTS="$TMP_DIR/old-pair-imports"
MIXED_OLD_FORMAT_IMPORTS="$TMP_DIR/mixed-old-format-imports"
MIXED_OLD_CORE_IMPORTS="$TMP_DIR/mixed-old-core-imports"
write_import_header_variant "$OLD_PAIR_IMPORTS" NPA-CERT-0.3.0 NPA-Core-0.3.0
write_import_header_variant "$MIXED_OLD_FORMAT_IMPORTS" NPA-CERT-0.3.0 NPA-Core-0.4.0
write_import_header_variant "$MIXED_OLD_CORE_IMPORTS" NPA-CERT-0.4.0 NPA-Core-0.3.0

run_case opaque-direct checked - - \
  "$CONFORMANCE/opaque-direct-v0.4.npcert" "$EMPTY_IMPORTS"
run_case opaque-alias-chain checked - - \
  "$CONFORMANCE/opaque-alias-chain-v0.4.npcert" "$EMPTY_IMPORTS"
run_case indexed checked - - "$CONFORMANCE/indexed-v0.4.npcert" "$EMPTY_IMPORTS"
run_case mutual checked - - "$CONFORMANCE/mutual-v0.4.npcert" "$EMPTY_IMPORTS"
run_case nested checked - - "$CONFORMANCE/nested-v0.4.npcert" "$EMPTY_IMPORTS"
run_case nested-all checked - - "$CONFORMANCE/nested-all-v0.4.npcert" "$EMPTY_IMPORTS"
run_case imported-indexed-iota checked - - \
  "$CONFORMANCE/imported-indexed-iota-v0.4.npcert" "$INDEXED_IMPORTS"
run_case imported-mutual-iota checked - - \
  "$CONFORMANCE/imported-mutual-iota-v0.4.npcert" "$MUTUAL_IMPORTS"

run_case invalid-target failed dependency_hash_mismatch target_not_opaque \
  "$CONFORMANCE/invalid-target-v0.4.npcert" "$EMPTY_IMPORTS"
run_case stale-implementation-hash failed dependency_hash_mismatch certificate_hash_mismatch \
  "$CONFORMANCE/stale-implementation-hash-v0.4.npcert" "$EMPTY_IMPORTS"
run_case dependency-hash-mismatch failed dependency_hash_mismatch decl_certificate_hash_mismatch \
  "$CONFORMANCE/dependency-hash-mismatch-v0.4.npcert" "$EMPTY_IMPORTS"
run_case noncanonical-unused-name failed noncanonical_encoding unused_table_entry \
  "$CONFORMANCE/noncanonical-unused-name-v0.4.npcert" "$EMPTY_IMPORTS"
run_case forbidden-axiom failed forbidden_axiom forbidden_axiom \
  "$CONFORMANCE/forbidden-axiom-v0.4.npcert" "$EMPTY_IMPORTS"
run_case semantically-invalid-provider failed type_mismatch type_mismatch \
  "$CONFORMANCE/unchecked-provider-bad-v0.4.npcert" "$EMPTY_IMPORTS"
run_case semantically-invalid-pinned-import failed type_mismatch type_mismatch \
  "$CONFORMANCE/unchecked-consumer-pinned-v0.4.npcert" "$BAD_IMPORTS"
run_case missing-import-certificate-pin failed import_not_found missing_import_certificate_hash \
  "$CONFORMANCE/unchecked-consumer-unpinned-v0.4.npcert" "$BAD_IMPORTS"
run_case import_old_pair failed certificate_decode_error format_mismatch \
  "$CONFORMANCE/imported-mutual-iota-v0.4.npcert" "$OLD_PAIR_IMPORTS"
run_case import_mixed_old_format failed certificate_decode_error format_mismatch \
  "$CONFORMANCE/imported-mutual-iota-v0.4.npcert" "$MIXED_OLD_FORMAT_IMPORTS"
run_case import_mixed_old_core failed certificate_decode_error core_spec_mismatch \
  "$CONFORMANCE/imported-mutual-iota-v0.4.npcert" "$MIXED_OLD_CORE_IMPORTS"

EMPTY_LEAF="$TMP_DIR/empty-leaf.npcert"
: > "$EMPTY_LEAF"
run_case empty-leaf failed certificate_decode_error unexpected_eof \
  "$EMPTY_LEAF" "$EMPTY_IMPORTS"
MALFORMED_LEAF="$TMP_DIR/malformed-leaf.npcert"
printf '\001X' > "$MALFORMED_LEAF"
run_case malformed-leaf failed certificate_decode_error unexpected_eof \
  "$MALFORMED_LEAF" "$EMPTY_IMPORTS"

write_string() {
  output=$1
  value=$2
  length=$(printf '%s' "$value" | wc -c | tr -d ' ')
  if [ "$length" -ge 128 ]; then
    echo "header matrix string exceeds single-byte test encoder" >&2
    exit 1
  fi
  escape=$(printf '\\%03o' "$length")
  printf '%b%s' "$escape" "$value" >> "$output"
}

write_header_prefix() {
  output=$1
  format=$2
  core_spec=$3
  : > "$output"
  write_string "$output" "$format"
  write_string "$output" "$core_spec"
  printf '\001\001X' >> "$output"
}

tab=$(printf '\t')
while IFS="$tab" read -r case_id case_class template format core_spec mutation producer_result rust_result ocaml_result boundary
do
  if [ "$case_class" = header ] && [ "$ocaml_result" != checked ]; then
    header_fixture="$TMP_DIR/$case_id.npcert"
    write_header_prefix "$header_fixture" "$format" "$core_spec"
    run_case "$case_id" failed certificate_decode_error "$ocaml_result" \
      "$header_fixture" "$EMPTY_IMPORTS"
  fi
done < "$MATRIX"

write_term_prefix() {
  output=$1
  printf '\016NPA-CERT-0.4.0\016NPA-Core-0.4.0\001\001X\000\000\001\000' > "$output"
}

run_retired_tag_case() {
  label=$1
  payload=$2
  fixture="$TMP_DIR/$label.npcert"
  write_term_prefix "$fixture"
  printf '%b' "$payload" >> "$fixture"
  run_case "$label" failed certificate_decode_error unknown_tag \
    "$fixture" "$EMPTY_IMPORTS"
}

run_retired_tag_case retired-06-reachable '\001\006\000\000\000'
run_retired_tag_case retired-06-unused '\002\000\000\006\000\000\000'
run_retired_tag_case retired-06-tag-only '\001\006'
run_retired_tag_case retired-06-one-child '\001\006\000'
run_retired_tag_case retired-06-two-children '\001\006\000\000'
run_retired_tag_case retired-06-oversized-tail '\001\006\377\377\377\377\377\377\377\377\377\001'

OVERSIZED_LEAF="$TMP_DIR/oversized-leaf.npcert"
truncate -s 67108865 "$OVERSIZED_LEAF"
run_case oversized-leaf failed certificate_decode_error resource_limit \
  "$OVERSIZED_LEAF" "$EMPTY_IMPORTS"

SOURCE_NAMED_LEAF="$TMP_DIR/source-named-leaf.npa"
cp "$CONFORMANCE/indexed-v0.4.npcert" "$SOURCE_NAMED_LEAF"
for driver in verify_ext_fast verify_ext_reference
do
  source_json="$TMP_DIR/source-named-leaf.$driver.json"
  source_status=0
  "$ROOT/target/debug/examples/$driver" \
    "$SOURCE_NAMED_LEAF" "$EMPTY_IMPORTS" "$POLICY" \
    > "$source_json" || source_status=$?
  if [ "$source_status" -ne 1 ] || \
     [ "$(json_string_field "$source_json" status)" != failed ]; then
    echo "$driver accepted a forbidden source path" >&2
    exit 1
  fi
done

"$ROOT/target/debug/examples/validate_checker_raw" \
  "$TMP_DIR"/*.reference.json "$TMP_DIR"/*.external.json

"$EXT_ROOT/scripts/source-free-trace.sh"
