#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
source scripts/check-performance.sh

test_root="$(mktemp -d "${TMPDIR:-/tmp}/npa-private-temp-test.XXXXXX")"
trap 'rm -rf -- "$test_root"' EXIT

IFS=$'\t' read -r private_path private_parent private_identity \
  < <(make_private_temp_dir "$test_root" ".npa-private")
[[ -d "$private_path" && ! -L "$private_path" ]]
[[ "$private_parent" == "$(cd "$test_root" && pwd -P)" ]]
[[ "$private_identity" == *:700 ]]
guarded_remove_private_temp_dir \
  "$private_path" "$private_parent" ".npa-private" "$private_identity"
[[ ! -e "$private_path" ]]

IFS=$'\t' read -r catalog_path catalog_parent catalog_identity \
  < <(make_private_temp_dir "$test_root" ".npa-private")
catalog_first="$catalog_path/first.json"
catalog_second="$catalog_path/second.json"
printf '{}\n' >"$catalog_first"
printf '{}\n' >"$catalog_second"
cleanup_private_temp_catalog \
  "$catalog_path" "$catalog_parent" ".npa-private" "$catalog_identity" \
  "$catalog_first" "$catalog_second"
[[ ! -e "$catalog_path" ]]

IFS=$'\t' read -r unknown_path unknown_parent unknown_identity \
  < <(make_private_temp_dir "$test_root" ".npa-private")
known_file="$unknown_path/known.json"
unknown_file="$unknown_path/unknown.json"
printf '{}\n' >"$known_file"
printf '{}\n' >"$unknown_file"
if cleanup_private_temp_catalog \
  "$unknown_path" "$unknown_parent" ".npa-private" "$unknown_identity" \
  "$known_file"; then
  echo "private temp catalog cleanup accepted an unknown entry" >&2
  exit 1
fi
[[ -d "$unknown_path" && -f "$unknown_file" && ! -e "$known_file" ]]

IFS=$'\t' read -r replaced_path replaced_parent replaced_identity \
  < <(make_private_temp_dir "$test_root" ".npa-private")
relocated="${replaced_path}.original"
mv "$replaced_path" "$relocated"
mkdir "$replaced_path"
chmod 700 "$replaced_path"
if guarded_remove_private_temp_dir \
  "$replaced_path" "$replaced_parent" ".npa-private" "$replaced_identity"; then
  echo "private temp cleanup accepted a replacement directory" >&2
  exit 1
fi
[[ -d "$replaced_path" && -d "$relocated" ]]

real_parent="$test_root/real-parent"
link_parent="$test_root/link-parent"
mkdir "$real_parent"
ln -s "$real_parent" "$link_parent"
if make_private_temp_dir "$link_parent" ".npa-private" >/dev/null 2>&1; then
  echo "private temp allocation accepted a symlink parent" >&2
  exit 1
fi

echo "check-performance private temporary-directory guards passed"
