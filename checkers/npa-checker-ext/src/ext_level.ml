type t =
  | Zero
  | Succ of t
  | Max of t * t
  | Imax of t * t
  | Param of Ext_name.t

type located = {
  level : t;
  offset : Ext_bytes.offset;
}

let zero = Zero

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let human_universe_meta_prefix = "__npa_internal_human_universe_meta#"

let starts_with text prefix =
  let text_len = String.length text in
  let prefix_len = String.length prefix in
  text_len >= prefix_len && String.sub text 0 prefix_len = prefix

let contains_question_mark component =
  let rec loop index =
    if index >= String.length component then false
    else if component.[index] = '?' then true
    else loop (index + 1)
  in
  loop 0

let component_contains_universe_meta name =
  List.exists
    (fun component ->
      starts_with component human_universe_meta_prefix || contains_question_mark component)
    (Ext_name.components name)

let name_at names id offset =
  if id < 0 || id >= Array.length names then
    Ext_bytes.error Ext_bytes.Level_table offset Ext_bytes.Dangling_reference
  else
    let name = names.(id) in
    if component_contains_universe_meta name then
      Ext_bytes.error Ext_bytes.Level_table offset Ext_bytes.Unresolved_metavariable
    else Ok name

let previous_level values index id offset =
  if id < 0 || id >= index then
    Ext_bytes.error Ext_bytes.Level_table offset Ext_bytes.Dangling_reference
  else
    match values.(id) with
    | None -> Ext_bytes.error Ext_bytes.Level_table offset Ext_bytes.Dangling_reference
    | Some located -> Ok located.level

let previous_depth depths index id offset =
  if id < 0 || id >= index || depths.(id) = 0 then
    Ext_bytes.error Ext_bytes.Level_table offset Ext_bytes.Dangling_reference
  else Ok depths.(id)

let rec level_as_nat level =
  match level with
  | Zero -> Some 0
  | Succ inner -> (
      match level_as_nat inner with
      | None -> None
      | Some value -> Some (value + 1))
  | Max _ | Imax _ | Param _ -> None

let level_from_nat value =
  let rec loop remaining level =
    if remaining = 0 then level else loop (remaining - 1) (Succ level)
  in
  loop value Zero

let rec compare_level lhs rhs =
  let rank level =
    match level with
    | Zero -> 0
    | Succ _ -> 1
    | Max _ -> 2
    | Imax _ -> 3
    | Param _ -> 4
  in
  match (lhs, rhs) with
  | Zero, Zero -> 0
  | Succ lhs_inner, Succ rhs_inner -> compare_level lhs_inner rhs_inner
  | Max (lhs_a, lhs_b), Max (rhs_a, rhs_b)
  | Imax (lhs_a, lhs_b), Imax (rhs_a, rhs_b) ->
      let first = compare_level lhs_a rhs_a in
      if first <> 0 then first else compare_level lhs_b rhs_b
  | Param lhs_name, Param rhs_name ->
      String.compare (Ext_name.to_string lhs_name) (Ext_name.to_string rhs_name)
  | _ -> compare (rank lhs) (rank rhs)

let rec normalize level =
  match level with
  | Zero | Param _ -> level
  | Succ inner -> Succ (normalize inner)
  | Max (lhs, rhs) ->
      let lhs = normalize lhs in
      let rhs = normalize rhs in
      if lhs = rhs then lhs
      else if lhs = Zero then rhs
      else if rhs = Zero then lhs
      else (
        match (level_as_nat lhs, level_as_nat rhs) with
        | Some lhs_nat, Some rhs_nat -> level_from_nat (max lhs_nat rhs_nat)
        | _ ->
            if compare_level rhs lhs < 0 then Max (rhs, lhs) else Max (lhs, rhs))
  | Imax (lhs, rhs) ->
      let lhs = normalize lhs in
      let rhs = normalize rhs in
      (match rhs with
      | Zero -> Zero
      | Succ inner -> normalize (Max (lhs, Succ inner))
      | _ -> Imax (lhs, rhs))

let read_previous_ref values depths index entry_offset reader =
  bind (Ext_bytes.read_usize Ext_bytes.Level_table reader) (fun (id, next) ->
      bind (previous_level values index id entry_offset) (fun level ->
          bind (previous_depth depths index id entry_offset) (fun depth ->
              Ok ((level, depth), next))))

let read_name_ref names entry_offset reader =
  bind (Ext_bytes.read_usize Ext_bytes.Level_table reader) (fun (id, next) ->
      bind (name_at names id entry_offset) (fun name -> Ok (name, next)))

let read_table names reader =
  match Ext_bytes.read_count Ext_bytes.Level_table reader with
  | Error err -> Error err
  | Ok (level_count, after_count) ->
      if level_count > Ext_bytes.remaining after_count then
        Ext_bytes.error Ext_bytes.Level_table (Ext_bytes.offset after_count)
          Ext_bytes.Unexpected_eof
      else
        let name_values = Array.of_list names in
        let values = Array.make level_count None in
        let depths = Array.make level_count 0 in
        let seen_encodings = Hashtbl.create (min level_count 1_024) in
        let rec loop index current decoded =
          if index = level_count then Ok (List.rev decoded, current)
          else
            let entry_offset = Ext_bytes.offset current in
            match Ext_bytes.read_byte Ext_bytes.Level_table current with
            | Error err -> Error err
            | Ok (tag, after_tag) ->
                let decoded_level =
                  match tag with
                  | 0x00 -> Ok ((Zero, 1), after_tag)
                  | 0x01 ->
                      bind
                        (read_previous_ref values depths index entry_offset
                           after_tag)
                        (fun ((inner, depth), next) ->
                          Ok ((Succ inner, depth + 1), next))
                  | 0x02 ->
                      bind
                        (read_previous_ref values depths index entry_offset
                           after_tag)
                        (fun ((lhs, lhs_depth), after_lhs) ->
                          bind
                            (read_previous_ref values depths index entry_offset
                               after_lhs)
                            (fun ((rhs, rhs_depth), next) ->
                              Ok
                                ( (Max (lhs, rhs),
                                   1 + max lhs_depth rhs_depth),
                                  next )))
                  | 0x03 ->
                      bind
                        (read_previous_ref values depths index entry_offset
                           after_tag)
                        (fun ((lhs, lhs_depth), after_lhs) ->
                          bind
                            (read_previous_ref values depths index entry_offset
                               after_lhs)
                            (fun ((rhs, rhs_depth), next) ->
                              Ok
                                ( (Imax (lhs, rhs),
                                   1 + max lhs_depth rhs_depth),
                                  next )))
                  | 0x04 ->
                      bind (read_name_ref name_values entry_offset after_tag)
                        (fun (name, next) -> Ok ((Param name, 1), next))
                  | tag ->
                      Ext_bytes.error Ext_bytes.Level_table entry_offset
                        (Ext_bytes.Unknown_tag tag)
                in
                (match decoded_level with
                | Error err -> Error err
                | Ok ((level, depth), next) ->
                    if depth > Ext_bytes.max_node_depth then
                      Ext_bytes.error Ext_bytes.Level_table entry_offset
                        Ext_bytes.Resource_limit
                    else if normalize level <> level then
                      Ext_bytes.error Ext_bytes.Level_table entry_offset
                        Ext_bytes.Non_normalized_level
                    else
                      let encoding =
                        String.sub current.Ext_bytes.data entry_offset
                          (Ext_bytes.offset next - entry_offset)
                      in
                      if Hashtbl.mem seen_encodings encoding then
                        Ext_bytes.error Ext_bytes.Level_table entry_offset
                          Ext_bytes.Noncanonical_order
                      else
                      let located = { level; offset = entry_offset } in
                      values.(index) <- Some located;
                      depths.(index) <- depth;
                      Hashtbl.add seen_encodings encoding ();
                      loop (index + 1) next (located :: decoded))
        in
        loop 0 after_count []
