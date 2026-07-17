external open_path_nofollow : string -> bool -> Unix.file_descr
  = "npa_ext_open_path_nofollow"

external openat_nofollow : Unix.file_descr -> string -> bool -> Unix.file_descr
  = "npa_ext_openat_nofollow"

type path_kind =
  | Symlink
  | Directory
  | Regular
  | Other

external path_kind_at_nofollow_raw : Unix.file_descr -> string -> int
  = "npa_ext_path_kind_at_nofollow"

let path_kind_at_nofollow descriptor name =
  match path_kind_at_nofollow_raw descriptor name with
  | 0 -> Symlink
  | 1 -> Directory
  | 2 -> Regular
  | _ -> Other

external read_dir_names_bounded : Unix.file_descr -> int -> string list
  = "npa_ext_read_dir_names_bounded"
