type hash = string

type global_ref =
  | Imported of {
      import_index : int;
      name : Ext_name.t;
      decl_interface_hash : hash;
    }
  | Local of { decl_index : int }
  | LocalGenerated of {
      decl_index : int;
      name : Ext_name.t;
    }
  | Builtin of {
      name : Ext_name.t;
      decl_interface_hash : hash;
    }

type t =
  | Sort of Ext_level.t
  | BVar of int
  | Const of global_ref * Ext_level.t list
  | App of t * t
  | Lam of t * t
  | Pi of t * t
  | Let of t * t * t

type located = {
  term : t;
  offset : Ext_bytes.offset;
}

let sort_zero = Sort Ext_level.zero

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let read_u32 section reader =
  let start = Ext_bytes.offset reader in
  match Ext_bytes.read_uvar section reader with
  | Error err -> Error err
  | Ok (value, next) ->
      if value > 0xffff_ffffL then Ext_bytes.error section start Ext_bytes.Length_overflow
      else Ok (Int64.to_int value, next)

let name_at section names id offset =
  if id < 0 || id >= Array.length names then
    Ext_bytes.error section offset Ext_bytes.Dangling_reference
  else Ok names.(id)

let level_at levels id offset =
  if id < 0 || id >= Array.length levels then
    Ext_bytes.error Ext_bytes.Term_table offset Ext_bytes.Dangling_reference
  else Ok levels.(id).Ext_level.level

let previous_term values index id offset =
  if id < 0 || id >= index then
    Ext_bytes.error Ext_bytes.Term_table offset Ext_bytes.Dangling_reference
  else
    match values.(id) with
    | None -> Ext_bytes.error Ext_bytes.Term_table offset Ext_bytes.Dangling_reference
    | Some located -> Ok located.term

let read_hash section reader = Ext_bytes.take section 32 reader

let read_name_id section names offset reader =
  bind (Ext_bytes.read_usize section reader) (fun (id, next) ->
      bind (name_at section names id offset) (fun name -> Ok (name, next)))

let read_level_id levels offset reader =
  bind (Ext_bytes.read_usize Ext_bytes.Term_table reader) (fun (id, next) ->
      bind (level_at levels id offset) (fun level -> Ok (level, next)))

let read_previous_term_id values index offset reader =
  bind (Ext_bytes.read_usize Ext_bytes.Term_table reader) (fun (id, next) ->
      bind (previous_term values index id offset) (fun term -> Ok (term, next)))

let read_level_vec levels offset reader =
  bind (Ext_bytes.read_usize Ext_bytes.Term_table reader) (fun (count, after_count) ->
      let rec loop remaining current decoded =
        if remaining = 0 then Ok (List.rev decoded, current)
        else
          bind (read_level_id levels offset current) (fun (level, next) ->
              loop (remaining - 1) next (level :: decoded))
      in
      loop count after_count [])

let read_global_ref section names offset reader =
  let tag_offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte section reader with
  | Error err -> Error err
  | Ok (tag, after_tag) -> (
      match tag with
      | 0x00 ->
          bind (Ext_bytes.read_usize section after_tag)
            (fun (import_index, after_import) ->
              bind (read_name_id section names offset after_import) (fun (name, after_name) ->
                  bind (read_hash section after_name) (fun (decl_interface_hash, next) ->
                      Ok (Imported { import_index; name; decl_interface_hash }, next))))
      | 0x01 ->
          bind (Ext_bytes.read_usize section after_tag)
            (fun (decl_index, next) -> Ok (Local { decl_index }, next))
      | 0x02 ->
          bind (Ext_bytes.read_usize section after_tag)
            (fun (decl_index, after_decl) ->
              bind (read_name_id section names offset after_decl) (fun (name, next) ->
                  Ok (LocalGenerated { decl_index; name }, next)))
      | 0x03 ->
          bind (read_name_id section names offset after_tag) (fun (name, after_name) ->
              bind (read_hash section after_name) (fun (decl_interface_hash, next) ->
                  Ok (Builtin { name; decl_interface_hash }, next)))
      | tag -> Ext_bytes.error section tag_offset (Ext_bytes.Unknown_tag tag))

let has_previous_term values index term =
  let rec loop cursor =
    if cursor >= index then false
    else
      match values.(cursor) with
      | Some previous when previous.term = term -> true
      | _ -> loop (cursor + 1)
  in
  loop 0

let read_table names levels reader =
  match Ext_bytes.read_usize Ext_bytes.Term_table reader with
  | Error err -> Error err
  | Ok (term_count, after_count) ->
      if term_count > Ext_bytes.remaining after_count then
        Ext_bytes.error Ext_bytes.Term_table (Ext_bytes.offset after_count) Ext_bytes.Unexpected_eof
      else
        let name_values = Array.of_list names in
        let level_values = Array.of_list levels in
        let values = Array.make term_count None in
        let rec loop index current decoded =
          if index = term_count then Ok (List.rev decoded, current)
          else
            let entry_offset = Ext_bytes.offset current in
            match Ext_bytes.read_byte Ext_bytes.Term_table current with
            | Error err -> Error err
            | Ok (tag, after_tag) ->
                let decoded_term =
                  match tag with
                  | 0x00 ->
                      bind (read_level_id level_values entry_offset after_tag)
                        (fun (level, next) -> Ok (Sort level, next))
                  | 0x01 ->
                      bind (read_u32 Ext_bytes.Term_table after_tag)
                        (fun (index, next) -> Ok (BVar index, next))
                  | 0x02 ->
                      bind (read_global_ref Ext_bytes.Term_table name_values entry_offset after_tag)
                        (fun (global_ref, after_ref) ->
                          bind
                            (read_level_vec level_values entry_offset after_ref)
                            (fun (levels, next) -> Ok (Const (global_ref, levels), next)))
                  | 0x03 ->
                      bind
                        (read_previous_term_id values index entry_offset after_tag)
                        (fun (fn, after_fn) ->
                          bind
                            (read_previous_term_id values index entry_offset after_fn)
                            (fun (arg, next) -> Ok (App (fn, arg), next)))
                  | 0x04 ->
                      bind
                        (read_previous_term_id values index entry_offset after_tag)
                        (fun (ty, after_ty) ->
                          bind
                            (read_previous_term_id values index entry_offset after_ty)
                            (fun (body, next) -> Ok (Lam (ty, body), next)))
                  | 0x05 ->
                      bind
                        (read_previous_term_id values index entry_offset after_tag)
                        (fun (ty, after_ty) ->
                          bind
                            (read_previous_term_id values index entry_offset after_ty)
                            (fun (body, next) -> Ok (Pi (ty, body), next)))
                  | 0x06 ->
                      bind
                        (read_previous_term_id values index entry_offset after_tag)
                        (fun (ty, after_ty) ->
                          bind
                            (read_previous_term_id values index entry_offset after_ty)
                            (fun (value, after_value) ->
                              bind
                                (read_previous_term_id values index entry_offset after_value)
                                (fun (body, next) -> Ok (Let (ty, value, body), next))))
                  | tag ->
                      Ext_bytes.error Ext_bytes.Term_table entry_offset (Ext_bytes.Unknown_tag tag)
                in
                (match decoded_term with
                | Error err -> Error err
                | Ok (term, next) ->
                    if has_previous_term values index term then
                      Ext_bytes.error Ext_bytes.Term_table entry_offset
                        Ext_bytes.Non_normalized_term
                    else
                      let located = { term; offset = entry_offset } in
                      values.(index) <- Some located;
                      loop (index + 1) next (located :: decoded))
        in
        loop 0 after_count []
