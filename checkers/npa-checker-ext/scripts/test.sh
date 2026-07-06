#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BUILD_DIR="$ROOT/_build"
OCAMLC=$("$ROOT/scripts/ocamlc.sh")

sh "$ROOT/scripts/build.sh"

"$OCAMLC" -I "$BUILD_DIR" -c -o "$BUILD_DIR/test_runner.cmo" "$ROOT/test/test_runner.ml"
"$OCAMLC" -I "$BUILD_DIR" \
  -o "$BUILD_DIR/test_runner" \
  "$BUILD_DIR/ext_sha256.cmo" \
  "$BUILD_DIR/ext_hash.cmo" \
  "$BUILD_DIR/ext_bytes.cmo" \
  "$BUILD_DIR/ext_result.cmo" \
  "$BUILD_DIR/ext_feature.cmo" \
  "$BUILD_DIR/ext_name.cmo" \
  "$BUILD_DIR/ext_import.cmo" \
  "$BUILD_DIR/ext_level.cmo" \
  "$BUILD_DIR/ext_term.cmo" \
  "$BUILD_DIR/ext_cert.cmo" \
  "$BUILD_DIR/ext_canonical.cmo" \
  "$BUILD_DIR/ext_import_store.cmo" \
  "$BUILD_DIR/ext_env.cmo" \
  "$BUILD_DIR/ext_axiom.cmo" \
  "$BUILD_DIR/ext_reduce.cmo" \
  "$BUILD_DIR/ext_inductive.cmo" \
  "$BUILD_DIR/ext_typecheck.cmo" \
  "$BUILD_DIR/ext_cli.cmo" \
  "$BUILD_DIR/test_runner.cmo"

NPA_CHECKER_EXT_ROOT="$ROOT" "$BUILD_DIR/test_runner" "$@"
