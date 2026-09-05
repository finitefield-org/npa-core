#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
source "$repository_root/scripts/check-performance.sh"

temporary_root=$(mktemp -d "${TMPDIR:-/tmp}/npa-performance-sha256.XXXXXX")
temporary_root=$(cd "$temporary_root" && pwd -P)
trap '/bin/rm -rf -- "$temporary_root"' EXIT
mkdir "$temporary_root/bin"
ln -s /usr/bin/awk "$temporary_root/bin/awk"

write_digest_stub() {
  local path=$1
  local digest=$2
  printf '#!/bin/sh\nprintf "%%s  -\\n" "%s"\n' "$digest" >"$path"
  chmod +x "$path"
}

preferred=1111111111111111111111111111111111111111111111111111111111111111
fallback=2222222222222222222222222222222222222222222222222222222222222222
write_digest_stub "$temporary_root/bin/shasum" "$preferred"
write_digest_stub "$temporary_root/bin/sha256sum" "$fallback"

original_path=$PATH
PATH=$temporary_root/bin
[[ "$(printf payload | sha256_stream)" == "$preferred" ]]
[[ "$(sha256_file "$repository_root/Cargo.lock")" == "$preferred" ]]

/bin/rm "$temporary_root/bin/shasum"
[[ "$(printf payload | sha256_stream)" == "$fallback" ]]
[[ "$(sha256_file "$repository_root/Cargo.lock")" == "$fallback" ]]

/bin/rm "$temporary_root/bin/sha256sum"
if printf payload | sha256_stream >/dev/null 2>&1; then
  echo "sha256_stream accepted an environment without either supported tool" >&2
  exit 1
fi

PATH=$original_path

tree_root=$temporary_root/tree
mkdir "$tree_root"
printf 'a' >"$tree_root/z file"
printf 'b' >"$tree_root/line
break"
printf 'c' >"$tree_root/alpha"
snapshot_tree_sha256 "$tree_root" >"$temporary_root/first.snapshot"
snapshot_tree_sha256 "$tree_root" >"$temporary_root/second.snapshot"
cmp -s "$temporary_root/first.snapshot" "$temporary_root/second.snapshot"
[[ $(LC_ALL=C tr -cd '\000' <"$temporary_root/first.snapshot" | wc -c | tr -d ' ') == 11 ]]

mkdir "$tree_root/empty-directory"
snapshot_tree_sha256 "$tree_root" >"$temporary_root/with-directory.snapshot"
! cmp -s "$temporary_root/first.snapshot" "$temporary_root/with-directory.snapshot"
rmdir "$tree_root/empty-directory"

ln -s alpha "$tree_root/extra-link"
if snapshot_tree_sha256 "$tree_root" >"$temporary_root/link.snapshot" 2>/dev/null; then
  echo "tree snapshot accepted a symbolic-link entry" >&2
  exit 1
fi
unlink "$tree_root/extra-link"

ln -s "$tree_root" "$temporary_root/tree-link"
if snapshot_tree_sha256 "$temporary_root/tree-link" >"$temporary_root/root-link.snapshot" 2>/dev/null; then
  echo "tree snapshot accepted a symbolic-link root" >&2
  exit 1
fi
unlink "$temporary_root/tree-link"

mkfifo "$tree_root/special"
if snapshot_tree_sha256 "$tree_root" >"$temporary_root/special.snapshot" 2>/dev/null; then
  echo "tree snapshot accepted a special-file entry" >&2
  exit 1
fi
rm -f -- "$tree_root/special"

echo "check-performance SHA-256 portability helpers passed"
