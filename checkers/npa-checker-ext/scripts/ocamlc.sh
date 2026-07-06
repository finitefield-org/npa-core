#!/bin/sh
set -eu

if [ -n "${OCAMLC:-}" ]; then
  printf '%s\n' "$OCAMLC"
  exit 0
fi

if command -v ocamlc >/dev/null 2>&1; then
  command -v ocamlc
  exit 0
fi

if command -v brew >/dev/null 2>&1; then
  prefix=$(brew --prefix ocaml 2>/dev/null || true)
  if [ -n "$prefix" ] && [ -x "$prefix/bin/ocamlc" ]; then
    printf '%s\n' "$prefix/bin/ocamlc"
    exit 0
  fi
fi

printf '%s\n' "ocamlc not found; set OCAMLC or install OCaml" >&2
exit 127
