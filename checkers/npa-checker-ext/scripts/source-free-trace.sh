#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
EXT_ROOT="$ROOT/checkers/npa-checker-ext"

if ! command -v strace >/dev/null 2>&1; then
  echo "source-free trace skipped: strace unavailable"
  exit 0
fi

TMP_DIR=$(mktemp -d "${TMPDIR:-/tmp}/npa-checker-ext-trace.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT HUP INT TERM

CHECKER="$EXT_ROOT/_build/npa-checker-ext"
CERTIFICATE="$ROOT/testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert"
cp -R "$ROOT/testdata/package/npa-mathlib-downstream/vendor" "$TMP_DIR/vendor"
IMPORT_DIR="$TMP_DIR/vendor"
UNRELATED_FILE="$IMPORT_DIR/unrelated.txt"
printf 'must not be opened by the checker\n' > "$UNRELATED_FILE"
POLICY="$EXT_ROOT/test/fixtures/axiom-policy.toml"
POLICY_HASH="sha256:$(sha256sum "$POLICY" | awk '{ print $1 }')"

allowed_file_path() {
  path=$1
  for target in "$CHECKER" "$CERTIFICATE" "$POLICY" "$IMPORT_DIR"
  do
    case "$target" in
      "$path"/*)
        if [ -d "$path" ]; then
          return 0
        fi
        ;;
    esac
  done
  case "$path" in
    /)
      return 0
      ;;
    "$CHECKER"|"$CERTIFICATE"|"$POLICY"|/etc/ld.so.cache|/etc/ld.so.preload|/proc/self/exe|/usr/bin/ocamlrun|/usr/lib/ocaml/ld.conf)
      return 0
      ;;
    "$IMPORT_DIR"|"$IMPORT_DIR"/*)
      case "$path" in
        *.npcert) return 0 ;;
      esac
      if [ -d "$path" ]; then
        return 0
      fi
      return 1
      ;;
    /lib/*/libc.so.*|/lib/*/libm.so.*|/lib/*/ld-linux*.so*|/usr/lib/*/libc.so.*|/usr/lib/*/libm.so.*|/usr/lib/*/ld-linux*.so*|/usr/lib/ocaml/stublibs/*.so|/usr/local/lib/ocaml/*/stublibs/*.so)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

successful_read_open() {
  syscall_name=$1
  syscall=$2
  case "$syscall_name" in
    open|openat|openat2) ;;
    *) return 1 ;;
  esac
  case "$syscall" in
    *O_WRONLY*|*O_RDWR*|*O_PATH*) return 1 ;;
  esac
  case "$syscall" in
    *' = '[0-9]*) return 0 ;;
    *) return 1 ;;
  esac
}

if allowed_file_path /etc/passwd; then
  echo "source-free trace allowlist admits an unrelated host file" >&2
  exit 1
fi
if allowed_file_path "$IMPORT_DIR/proof.npa"; then
  echo "source-free trace allowlist admits source under the import directory" >&2
  exit 1
fi
if successful_read_open stat \
  "stat(\"$CERTIFICATE\", {st_mode=S_IFREG}) = 0"; then
  echo "source-free trace treats metadata probes as certificate reads" >&2
  exit 1
fi
if successful_read_open openat \
  "openat(AT_FDCWD, \"$CERTIFICATE\", O_RDONLY) = -1 ENOENT"; then
  echo "source-free trace treats failed opens as certificate reads" >&2
  exit 1
fi
if successful_read_open openat \
  "openat(AT_FDCWD, \"$CERTIFICATE\", O_PATH) = 3"; then
  echo "source-free trace treats O_PATH handles as certificate reads" >&2
  exit 1
fi

strace -f -qq -yy \
  -e trace=%file,%network,io_uring_setup,io_uring_enter,io_uring_register,pidfd_getfd,sendfile,splice,vmsplice,tee \
  -o "$TMP_DIR/trace.log" \
  "$CHECKER" \
  --cert "$CERTIFICATE" \
  --import-dir "$IMPORT_DIR" \
  --policy "$POLICY" \
  --policy-hash "$POLICY_HASH" \
  --output json > "$TMP_DIR/result.json"

grep -q '"status": "checked"' "$TMP_DIR/result.json"

saw_certificate=false
saw_policy=false
saw_import_certificate=false
while IFS= read -r syscall
do
  trimmed=${syscall#"${syscall%%[![:space:]]*}"}
  call=${trimmed#* }
  call=${call#"${call%%[![:space:]]*}"}
  syscall_name=${call%%(*}
  case "$syscall_name" in
    execve|access|faccessat|faccessat2|open|openat|openat2|readlink|readlinkat|stat|lstat|newfstatat|statx)
      path=${syscall#*\"}
      path=${path%%\"*}
      case "$syscall_name" in
        openat|openat2|faccessat|faccessat2|readlinkat|newfstatat|statx)
          case "$path" in
            /*) ;;
            *)
              dir_argument=${call#*(}
              dir_argument=${dir_argument%%,*}
              case "$dir_argument" in
                *'<'*'>'*)
                  directory_path=${dir_argument#*<}
                  directory_path=${directory_path%%>*}
                  if [ -z "$path" ]; then
                    path=$directory_path
                  elif [ "$directory_path" = / ]; then
                    path="/$path"
                  else
                    path="$directory_path/$path"
                  fi
                  ;;
              esac
              ;;
          esac
          ;;
      esac
      case "$syscall_name" in
        execve)
          if [ "$path" != "$CHECKER" ]; then
            echo "source-free trace observed an unexpected executable: $path" >&2
            exit 1
          fi
          ;;
        open|openat|openat2)
          case "$syscall" in
            *O_WRONLY*|*O_RDWR*|*O_CREAT*|*O_TRUNC*|*O_APPEND*|*O_TMPFILE*)
              echo "source-free trace observed a writable open: $path" >&2
              exit 1
              ;;
          esac
          ;;
      esac
      metadata_only=false
      if [ "$path" = "$UNRELATED_FILE" ]; then
        case "$syscall_name" in
          stat|lstat|newfstatat|statx) metadata_only=true ;;
        esac
      fi
      if [ "$metadata_only" != true ] && ! allowed_file_path "$path"; then
        echo "source-free trace observed a non-allowlisted file syscall: $syscall_name $path" >&2
        exit 1
      fi
      if [ "$metadata_only" = true ] && successful_read_open "$syscall_name" "$syscall"; then
        echo "source-free trace opened unrelated import input: $path" >&2
        exit 1
      fi
      if successful_read_open "$syscall_name" "$syscall"; then
        if [ "$path" = "$CERTIFICATE" ]; then
          saw_certificate=true
        fi
        if [ "$path" = "$POLICY" ]; then
          saw_policy=true
        fi
        case "$path" in
          "$IMPORT_DIR"/*.npcert) saw_import_certificate=true ;;
        esac
      fi
      ;;
    *)
      echo "source-free trace observed a forbidden syscall: $syscall_name" >&2
      exit 1
      ;;
  esac
done < "$TMP_DIR/trace.log"

if [ "$saw_certificate" != true ] || [ "$saw_policy" != true ] || \
  [ "$saw_import_certificate" != true ]; then
  echo "source-free trace did not observe every required source-free input" >&2
  exit 1
fi

echo "source-free trace: matched"
