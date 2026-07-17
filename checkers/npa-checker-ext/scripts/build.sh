#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BUILD_DIR="$ROOT/_build"
OCAMLC=$("$ROOT/scripts/ocamlc.sh")

mkdir -p "$BUILD_DIR"

"$OCAMLC" -c -o "$BUILD_DIR/ext_unix_stubs.o" \
  "$ROOT/src/ext_unix_stubs.c"

compile_module() {
  src="$1"
  base=$(basename "$src" .ml)
  interface="$ROOT/src/$base.mli"
  if [ -f "$interface" ]; then
    "$OCAMLC" -I "$BUILD_DIR" -c -o "$BUILD_DIR/$base.cmi" "$interface"
  fi
  "$OCAMLC" -I "$BUILD_DIR" -c -o "$BUILD_DIR/$base.cmo" "$ROOT/$src"
}

for src in \
  src/ext_sha256.ml \
  src/ext_hash.ml \
  src/ext_bytes.ml \
  src/ext_result.ml \
  src/ext_feature.ml \
  src/ext_name.ml \
  src/ext_unix.ml \
  src/ext_import.ml \
  src/ext_level.ml \
  src/ext_term.ml \
  src/ext_cert.ml \
  src/ext_universe.ml \
  src/ext_canonical.ml \
  src/ext_import_store.ml \
  src/ext_env.ml \
  src/ext_axiom.ml \
  src/ext_inductive.ml \
  src/ext_typecheck.ml \
  src/ext_checker.ml \
  src/ext_session.ml \
  src/ext_cli.ml \
  src/main.ml
do
  compile_module "$src"
done

"$OCAMLC" -custom -I "$BUILD_DIR" \
  -o "$BUILD_DIR/npa-checker-ext" \
  unix.cma \
  "$BUILD_DIR/ext_unix_stubs.o" \
  "$BUILD_DIR/ext_sha256.cmo" \
  "$BUILD_DIR/ext_hash.cmo" \
  "$BUILD_DIR/ext_bytes.cmo" \
  "$BUILD_DIR/ext_result.cmo" \
  "$BUILD_DIR/ext_feature.cmo" \
  "$BUILD_DIR/ext_name.cmo" \
  "$BUILD_DIR/ext_unix.cmo" \
  "$BUILD_DIR/ext_import.cmo" \
  "$BUILD_DIR/ext_level.cmo" \
  "$BUILD_DIR/ext_term.cmo" \
  "$BUILD_DIR/ext_cert.cmo" \
  "$BUILD_DIR/ext_universe.cmo" \
  "$BUILD_DIR/ext_canonical.cmo" \
  "$BUILD_DIR/ext_import_store.cmo" \
  "$BUILD_DIR/ext_env.cmo" \
  "$BUILD_DIR/ext_axiom.cmo" \
  "$BUILD_DIR/ext_inductive.cmo" \
  "$BUILD_DIR/ext_typecheck.cmo" \
  "$BUILD_DIR/ext_checker.cmo" \
  "$BUILD_DIR/ext_session.cmo" \
  "$BUILD_DIR/ext_cli.cmo" \
  "$BUILD_DIR/main.cmo"
