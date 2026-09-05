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

type located = {
  term : t;
  offset : Ext_bytes.offset;
  depth : int;
  order_height : int;
  expanded : int;
  order_payload : string;
  structural_hash : string;
}

type rebuild_kind = Rebuild_app | Rebuild_lam | Rebuild_pi
type rebuild_frame = Visit of t | Rebuild of t * rebuild_kind

module Term_identity_map = Hashtbl.Make (struct
  type nonrec t = t

  let equal lhs rhs = lhs == rhs
  let hash = Hashtbl.hash
end)

let sort_zero = Sort Ext_level.zero

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let map_global_refs map_global_ref malformed root =
  let mapped = Term_identity_map.create 128 in
  let rec loop pending results =
    match pending with
    | [] -> (
        match results with
        | [ result ] -> Ok result
        | _ -> malformed ())
    | Visit term :: rest -> (
        match Term_identity_map.find_opt mapped term with
        | Some result -> loop rest (result :: results)
        | None -> (
            match term with
            | Sort _ | BVar _ ->
                Term_identity_map.replace mapped term term;
                loop rest (term :: results)
            | Const (global_ref, levels) ->
                bind (map_global_ref global_ref) (fun mapped_ref ->
                    let result = Const (mapped_ref, levels) in
                    Term_identity_map.replace mapped term result;
                    loop rest (result :: results))
            | App (fn, arg) ->
                loop
                  (Visit fn :: Visit arg :: Rebuild (term, Rebuild_app) :: rest)
                  results
            | Lam (ty, body) ->
                loop
                  (Visit ty :: Visit body :: Rebuild (term, Rebuild_lam) :: rest)
                  results
            | Pi (ty, body) ->
                loop
                  (Visit ty :: Visit body :: Rebuild (term, Rebuild_pi) :: rest)
                  results))
    | Rebuild (source, kind) :: rest -> (
        match (kind, results) with
        | Rebuild_app, arg :: fn :: tail ->
            let result = App (fn, arg) in
            Term_identity_map.replace mapped source result;
            loop rest (result :: tail)
        | Rebuild_lam, body :: ty :: tail ->
            let result = Lam (ty, body) in
            Term_identity_map.replace mapped source result;
            loop rest (result :: tail)
        | Rebuild_pi, body :: ty :: tail ->
            let result = Pi (ty, body) in
            Term_identity_map.replace mapped source result;
            loop rest (result :: tail)
        | _ -> malformed ())
  in
  loop [ Visit root ] []

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
  else Ok levels.(id)

let previous_term values index id offset =
  if id < 0 || id >= index then
    Ext_bytes.error Ext_bytes.Term_table offset Ext_bytes.Dangling_reference
  else
    match values.(id) with
    | None -> Ext_bytes.error Ext_bytes.Term_table offset Ext_bytes.Dangling_reference
    | Some located -> Ok located

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
  bind (Ext_bytes.read_count Ext_bytes.Term_table reader) (fun (count, after_count) ->
      let rec loop remaining current decoded =
        if remaining = 0 then Ok (List.rev decoded, current)
        else
          bind (read_level_id levels offset current) (fun (level, next) ->
              loop (remaining - 1) next (level :: decoded))
      in
      loop count after_count [])

let byte value = String.make 1 (Char.chr value)

let encode_usize value = Ext_bytes.encode_uvar (Int64.of_int value)

let encode_name_key name =
  let components = Ext_name.components name in
  encode_usize (List.length components)
  ^ String.concat ""
      (List.map
         (fun component -> encode_usize (String.length component) ^ component)
         components)

let global_ref_payload = function
  | Imported { import_index; name; decl_interface_hash } ->
      byte 0x00 ^ encode_usize import_index ^ encode_name_key name
      ^ decl_interface_hash
  | Local { decl_index } -> byte 0x01 ^ encode_usize decl_index
  | LocalGenerated { decl_index; name } ->
      byte 0x02 ^ encode_usize decl_index ^ encode_name_key name
  | Builtin { name; decl_interface_hash } ->
      byte 0x03 ^ encode_name_key name ^ decl_interface_hash

let structural_hash payload =
  Bytes.to_string
    (Ext_hash.sha256_raw_string ("NPA-TERM-0.1" ^ payload))

let capped_add lhs rhs =
  let cap = Ext_bytes.max_root_expanded_nodes + 1 in
  if lhs >= cap || rhs >= cap || lhs > cap - rhs then cap else lhs + rhs

let level_vector_cost levels =
  List.fold_left
    (fun (depth, expanded) level ->
      (max depth level.Ext_level.depth, capped_add expanded level.Ext_level.expanded))
    (0, 0) levels

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

let read_table names levels reader =
  match
    Ext_bytes.read_count_with_limit Ext_bytes.Term_table
      Ext_bytes.Term_table_nodes Ext_bytes.max_term_table_nodes reader
  with
  | Error err -> Error err
  | Ok (term_count, after_count) ->
      if term_count > Ext_bytes.remaining after_count then
        Ext_bytes.error Ext_bytes.Term_table (Ext_bytes.offset after_count)
          Ext_bytes.Unexpected_eof
      else
        let name_values = Array.of_list names in
        let level_values = Array.of_list levels in
        let values = Array.make term_count None in
        let seen_encodings = Hashtbl.create (min term_count 1_024) in
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
                      bind
                        (read_level_id level_values entry_offset after_tag)
                        (fun (level, next) ->
                          Ok
                            ( ( Sort level.Ext_level.level,
                                1 + level.Ext_level.depth,
                                0,
                                capped_add 1 level.Ext_level.expanded,
                                byte 0x00 ^ level.Ext_level.structural_hash ),
                              next ))
                  | 0x01 ->
                      bind (read_u32 Ext_bytes.Term_table after_tag)
                        (fun (bvar, next) ->
                          Ok
                            ( ( BVar bvar,
                                1,
                                0,
                                1,
                                byte 0x01 ^ encode_usize bvar ),
                              next ))
                  | 0x02 ->
                      bind
                        (read_global_ref Ext_bytes.Term_table name_values
                           entry_offset after_tag)
                        (fun (global_ref, after_ref) ->
                          bind
                            (read_level_vec level_values entry_offset after_ref)
                            (fun (levels, next) ->
                              let level_depth, level_expanded =
                                level_vector_cost levels
                              in
                              let values =
                                List.map
                                  (fun level -> level.Ext_level.level)
                                  levels
                              in
                              let hashes =
                                String.concat ""
                                  (List.map
                                     (fun level ->
                                       level.Ext_level.structural_hash)
                                     levels)
                              in
                              let global_ref_bytes =
                                String.sub after_tag.Ext_bytes.data
                                  (Ext_bytes.offset after_tag)
                                  (Ext_bytes.offset after_ref
                                  - Ext_bytes.offset after_tag)
                              in
                              Ok
                                ( ( Const (global_ref, values),
                                    1 + level_depth,
                                    0,
                                    capped_add 1 level_expanded,
                                    byte 0x02 ^ global_ref_bytes
                                    ^ encode_usize (List.length levels)
                                    ^ hashes ),
                                  next )))
                  | 0x03 ->
                      bind
                        (read_previous_term_id values index entry_offset
                           after_tag)
                        (fun (fn, after_fn) ->
                          bind
                            (read_previous_term_id values index entry_offset
                               after_fn)
                            (fun (arg, next) ->
                              Ok
                                ( ( App (fn.term, arg.term),
                                    1 + max fn.depth arg.depth,
                                    1 + max fn.order_height arg.order_height,
                                    capped_add 1
                                      (capped_add fn.expanded arg.expanded),
                                    byte 0x03 ^ fn.structural_hash
                                    ^ arg.structural_hash ),
                                  next )))
                  | 0x04 ->
                      bind
                        (read_previous_term_id values index entry_offset
                           after_tag)
                        (fun (ty, after_ty) ->
                          bind
                            (read_previous_term_id values index entry_offset
                               after_ty)
                            (fun (body, next) ->
                              Ok
                                ( ( Lam (ty.term, body.term),
                                    1 + max ty.depth body.depth,
                                    1 + max ty.order_height body.order_height,
                                    capped_add 1
                                      (capped_add ty.expanded body.expanded),
                                    byte 0x04 ^ ty.structural_hash
                                    ^ body.structural_hash ),
                                  next )))
                  | 0x05 ->
                      bind
                        (read_previous_term_id values index entry_offset
                           after_tag)
                        (fun (ty, after_ty) ->
                          bind
                            (read_previous_term_id values index entry_offset
                               after_ty)
                            (fun (body, next) ->
                              Ok
                                ( ( Pi (ty.term, body.term),
                                    1 + max ty.depth body.depth,
                                    1 + max ty.order_height body.order_height,
                                    capped_add 1
                                      (capped_add ty.expanded body.expanded),
                                    byte 0x05 ^ ty.structural_hash
                                    ^ body.structural_hash ),
                                  next )))
                  | tag ->
                      Ext_bytes.error Ext_bytes.Term_table entry_offset
                        (Ext_bytes.Unknown_tag tag)
                in
                (match decoded_term with
                | Error err -> Error err
                | Ok
                    ( (term, depth, order_height, expanded, order_payload),
                      next ) ->
                    let encoding =
                        String.sub current.Ext_bytes.data entry_offset
                          (Ext_bytes.offset next - entry_offset)
                    in
                    if Hashtbl.mem seen_encodings encoding then
                      Ext_bytes.error Ext_bytes.Term_table entry_offset
                        Ext_bytes.Non_normalized_term
                    else
                        let located =
                          {
                            term;
                            offset = entry_offset;
                            depth;
                            order_height;
                            expanded;
                            order_payload;
                            structural_hash = structural_hash order_payload;
                          }
                        in
                        values.(index) <- Some located;
                        Hashtbl.add seen_encodings encoding ();
                        loop (index + 1) next (located :: decoded))
        in
        loop 0 after_count []
