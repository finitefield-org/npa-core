#define _GNU_SOURCE

#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/unixsupport.h>

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static int npa_open_anchor(bool absolute) {
  return open(absolute ? "/" : ".", O_RDONLY | O_CLOEXEC | O_DIRECTORY);
}

enum npa_open_kind {
  NPA_OPEN_DIRECTORY,
  NPA_OPEN_REGULAR,
};

static bool npa_accepts_kind(mode_t mode, enum npa_open_kind kind) {
  switch (kind) {
  case NPA_OPEN_DIRECTORY:
    return S_ISDIR(mode);
  case NPA_OPEN_REGULAR:
    return S_ISREG(mode);
  }
  return false;
}

static int npa_openat_nofollow_raw(int parent, const char *name,
                                   enum npa_open_kind kind) {
  struct stat metadata;
  if (fstatat(parent, name, &metadata, AT_SYMLINK_NOFOLLOW) != 0) {
    return -1;
  }
  if (S_ISLNK(metadata.st_mode)) {
    errno = ELOOP;
    return -1;
  }
  if (!npa_accepts_kind(metadata.st_mode, kind)) {
    errno = kind == NPA_OPEN_DIRECTORY ? ENOTDIR : EINVAL;
    return -1;
  }
  int flags = O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK;
  if (kind == NPA_OPEN_DIRECTORY) {
    flags |= O_DIRECTORY;
  }
  int opened = openat(parent, name, flags);
  if (opened < 0) {
    return -1;
  }
  if (fstat(opened, &metadata) != 0) {
    int saved = errno;
    close(opened);
    errno = saved;
    return -1;
  }
  if (!npa_accepts_kind(metadata.st_mode, kind)) {
    close(opened);
    errno = EINVAL;
    return -1;
  }
  return opened;
}

static bool npa_string_has_nul(value input) {
  mlsize_t length = caml_string_length(input);
  return memchr(String_val(input), '\0', length) != NULL;
}

CAMLprim value npa_ext_open_path_nofollow(value path_value,
                                          value directory_value) {
  CAMLparam2(path_value, directory_value);
  if (npa_string_has_nul(path_value)) {
    unix_error(EINVAL, "open", path_value);
  }
  const char *path = String_val(path_value);
  if (*path == '\0') {
    unix_error(ENOENT, "open", path_value);
  }
  char *copy = strdup(path);
  if (copy == NULL) {
    unix_error(ENOMEM, "open", path_value);
  }
  size_t capacity = strlen(path) + 1;
  char **components = calloc(capacity, sizeof(char *));
  if (components == NULL) {
    free(copy);
    unix_error(ENOMEM, "open", path_value);
  }
  size_t count = 0;
  char *save = NULL;
  for (char *part = strtok_r(copy, "/", &save); part != NULL;
       part = strtok_r(NULL, "/", &save)) {
    if (strcmp(part, ".") != 0) {
      components[count++] = part;
    }
  }

  int current = npa_open_anchor(path[0] == '/');
  if (current < 0) {
    int saved = errno;
    free(components);
    free(copy);
    errno = saved;
    uerror("open", path_value);
  }
  for (size_t index = 0; index < count; index++) {
    enum npa_open_kind kind = index + 1 < count || Bool_val(directory_value)
                                  ? NPA_OPEN_DIRECTORY
                                  : NPA_OPEN_REGULAR;
    int next = npa_openat_nofollow_raw(current, components[index], kind);
    if (next < 0) {
      int saved = errno;
      close(current);
      free(components);
      free(copy);
      errno = saved;
      uerror("open", path_value);
    }
    close(current);
    current = next;
  }
  free(components);
  free(copy);
  CAMLreturn(Val_int(current));
}

CAMLprim value npa_ext_path_kind_at_nofollow(value parent_value,
                                             value name_value) {
  CAMLparam2(parent_value, name_value);
  if (npa_string_has_nul(name_value) || caml_string_length(name_value) == 0 ||
      memchr(String_val(name_value), '/', caml_string_length(name_value)) !=
          NULL) {
    unix_error(EINVAL, "fstatat", name_value);
  }
  struct stat metadata;
  if (fstatat(Int_val(parent_value), String_val(name_value), &metadata,
              AT_SYMLINK_NOFOLLOW) != 0) {
    uerror("fstatat", name_value);
  }
  if (S_ISLNK(metadata.st_mode)) {
    CAMLreturn(Val_int(0));
  }
  if (S_ISDIR(metadata.st_mode)) {
    CAMLreturn(Val_int(1));
  }
  if (S_ISREG(metadata.st_mode)) {
    CAMLreturn(Val_int(2));
  }
  CAMLreturn(Val_int(3));
}

CAMLprim value npa_ext_openat_nofollow(value parent_value, value name_value,
                                       value directory_value) {
  CAMLparam3(parent_value, name_value, directory_value);
  if (npa_string_has_nul(name_value) || caml_string_length(name_value) == 0 ||
      memchr(String_val(name_value), '/', caml_string_length(name_value)) !=
          NULL) {
    unix_error(EINVAL, "openat", name_value);
  }
  enum npa_open_kind kind =
      Bool_val(directory_value) ? NPA_OPEN_DIRECTORY : NPA_OPEN_REGULAR;
  int fd = npa_openat_nofollow_raw(Int_val(parent_value),
                                   String_val(name_value), kind);
  if (fd < 0) {
    uerror("openat", name_value);
  }
  CAMLreturn(Val_int(fd));
}

static void npa_free_names(char **names, size_t count) {
  if (names == NULL) {
    return;
  }
  for (size_t index = 0; index < count; index++) {
    free(names[index]);
  }
  free(names);
}

CAMLprim value npa_ext_read_dir_names_bounded(value directory_value,
                                              value limit_value) {
  CAMLparam2(directory_value, limit_value);
  CAMLlocal3(list, cell, name_value);
  intnat raw_limit = Long_val(limit_value);
  if (raw_limit < 0) {
    unix_error(EOVERFLOW, "readdir", Nothing);
  }
  size_t limit = (size_t)raw_limit;
  int duplicate = fcntl(Int_val(directory_value), F_DUPFD_CLOEXEC, 0);
  if (duplicate < 0) {
    uerror("readdir", Nothing);
  }
  DIR *directory = fdopendir(duplicate);
  if (directory == NULL) {
    int saved = errno;
    close(duplicate);
    errno = saved;
    uerror("readdir", Nothing);
  }

  char **names = calloc(limit + 1, sizeof(char *));
  if (names == NULL) {
    closedir(directory);
    unix_error(ENOMEM, "readdir", Nothing);
  }
  size_t count = 0;
  errno = 0;
  for (;;) {
    struct dirent *entry = readdir(directory);
    if (entry == NULL) {
      break;
    }
    if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
      continue;
    }
    if (count >= limit) {
      closedir(directory);
      npa_free_names(names, count);
      unix_error(EOVERFLOW, "readdir", Nothing);
    }
    names[count] = strdup(entry->d_name);
    if (names[count] == NULL) {
      closedir(directory);
      npa_free_names(names, count);
      unix_error(ENOMEM, "readdir", Nothing);
    }
    count++;
    errno = 0;
  }
  int read_error = errno;
  closedir(directory);
  if (read_error != 0) {
    npa_free_names(names, count);
    unix_error(read_error, "readdir", Nothing);
  }

  list = Val_emptylist;
  for (size_t index = count; index > 0; index--) {
    name_value = caml_copy_string(names[index - 1]);
    cell = caml_alloc(2, 0);
    Store_field(cell, 0, name_value);
    Store_field(cell, 1, list);
    list = cell;
  }
  npa_free_names(names, count);
  CAMLreturn(list);
}
