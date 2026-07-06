type policy = {
  deny_sorry : bool;
  deny_custom_axioms : bool;
  allowed_axioms : Ext_name.t list;
}

let default_policy =
  { deny_sorry = true; deny_custom_axioms = true; allowed_axioms = [] }

let policy_format = "npa.independent-checker.axiom_policy.v1"

let legacy_policy_format = "npa.phase8.axiom_policy.v1"

type policy_parse_error = {
  policy_field : string;
  expected_value : string;
  actual_value : string;
}

type policy_string_entry =
  | Policy_string of string
  | Policy_non_string

type policy_assignment = {
  assignment_key : string;
  assignment_value : string;
}

let policy_parse_error field expected_value actual_value =
  Error { policy_field = field; expected_value; actual_value }

let policy_invalid_toml () =
  policy_parse_error "axiom_policy" "valid_toml" "invalid_toml"

let policy_error_kind _ = "policy_input_error"

let policy_error_reason_code _ = "request_axiom_policy_invalid"

let policy_allows policy name =
  List.exists (Ext_name.equal name) policy.allowed_axioms

let starts_with text prefix =
  let text_len = String.length text in
  let prefix_len = String.length prefix in
  text_len >= prefix_len && String.sub text 0 prefix_len = prefix

let has_utf8_bom text =
  String.length text >= 3
  && Char.code text.[0] = 0xef
  && Char.code text.[1] = 0xbb
  && Char.code text.[2] = 0xbf

let schema_path_component value =
  let length = String.length value in
  let rec loop index =
    if index >= length then true
    else
      let code = Char.code value.[index] in
      ((code >= Char.code 'a' && code <= Char.code 'z')
      || (code >= Char.code 'A' && code <= Char.code 'Z')
      || (code >= Char.code '0' && code <= Char.code '9')
      || value.[index] = '_' || value.[index] = '-')
      && loop (index + 1)
  in
  length > 0 && length <= 64 && loop 0

let key_path_valid key =
  key <> "" && List.for_all schema_path_component (String.split_on_char '.' key)

let policy_field_for_key key =
  if key_path_valid key then "axiom_policy." ^ key else "axiom_policy"

let find_char_from text start target =
  let rec loop index =
    if index >= String.length text then None
    else if text.[index] = target then Some index
    else loop (index + 1)
  in
  loop start

let strip_toml_comment line =
  let rec loop index in_string escaped =
    if index >= String.length line then
      if in_string || escaped then policy_invalid_toml () else Ok line
    else
      let ch = line.[index] in
      if in_string then
        if escaped then loop (index + 1) true false
        else
          match ch with
          | '\\' -> loop (index + 1) true true
          | '"' -> loop (index + 1) false false
          | _ -> loop (index + 1) true false
      else
        match ch with
        | '"' -> loop (index + 1) true false
        | '#' -> Ok (String.sub line 0 index)
        | _ -> loop (index + 1) false false
  in
  loop 0 false false

let toml_array_closed value =
  let rec loop index depth in_string escaped =
    if index >= String.length value then
      if in_string || escaped then policy_invalid_toml () else Ok false
    else
      let ch = value.[index] in
      if in_string then
        if escaped then loop (index + 1) depth true false
        else
          match ch with
          | '\\' -> loop (index + 1) depth true true
          | '"' -> loop (index + 1) depth false false
          | _ -> loop (index + 1) depth true false
      else
        match ch with
        | '"' -> loop (index + 1) depth true false
        | '[' -> loop (index + 1) (depth + 1) false false
        | ']' ->
            if depth = 0 then policy_invalid_toml ()
            else if depth = 1 then Ok true
            else loop (index + 1) (depth - 1) false false
        | _ -> loop (index + 1) depth false false
  in
  loop 0 0 false false

let collect_policy_assignments source =
  let lines = String.split_on_char '\n' source in
  let rec loop index assignments =
    if index >= List.length lines then Ok (List.rev assignments)
    else
      let line = List.nth lines index in
      match strip_toml_comment line with
      | Error err -> Error err
      | Ok without_comment ->
          let trimmed = String.trim without_comment in
          if trimmed = "" then loop (index + 1) assignments
          else if starts_with trimmed "[" then (
            match find_char_from trimmed 0 ']' with
            | None -> policy_invalid_toml ()
            | Some close_index ->
                if String.trim (String.sub trimmed (close_index + 1)
                                  (String.length trimmed - close_index - 1))
                   <> ""
                then policy_invalid_toml ()
                else
                  let key = String.trim (String.sub trimmed 1 (close_index - 1)) in
                  if key = "" then policy_invalid_toml ()
                  else
                    loop (index + 1)
                      ({ assignment_key = key; assignment_value = "{table}" }
                      :: assignments))
          else
            match find_char_from trimmed 0 '=' with
            | None -> policy_invalid_toml ()
            | Some eq_index ->
                let key = String.trim (String.sub trimmed 0 eq_index) in
                if key = "" || not (key_path_valid key) then policy_invalid_toml ()
                else
                  let value =
                    String.trim
                      (String.sub trimmed (eq_index + 1)
                         (String.length trimmed - eq_index - 1))
                  in
                  let rec collect_array current_index value =
                    if starts_with (String.trim value) "[" then
                      match toml_array_closed value with
                      | Error err -> Error err
                      | Ok true -> Ok (current_index, value)
                      | Ok false ->
                          let next_index = current_index + 1 in
                          if next_index >= List.length lines then policy_invalid_toml ()
                          else
                            let next_line = List.nth lines next_index in
                            (match strip_toml_comment next_line with
                            | Error err -> Error err
                            | Ok next_without_comment ->
                                collect_array next_index
                                  (value ^ "\n"
                                  ^ String.trim next_without_comment))
                    else Ok (current_index, value)
                  in
                  (match collect_array index value with
                  | Error err -> Error err
                  | Ok (next_index, value) ->
                      loop (next_index + 1)
                        ({ assignment_key = key; assignment_value = value }
                        :: assignments))
  in
  loop 0 []

let toml_skip_ws value index =
  let rec loop index =
    if index >= String.length value then index
    else
      match value.[index] with
      | ' ' | '\t' | '\n' | '\r' -> loop (index + 1)
      | _ -> index
  in
  loop index

let parse_toml_basic_string_at value start =
  if start >= String.length value || value.[start] <> '"' then policy_invalid_toml ()
  else
    let buffer = Buffer.create 16 in
    let rec loop index =
      if index >= String.length value then policy_invalid_toml ()
      else
        match value.[index] with
        | '"' -> Ok (Buffer.contents buffer, index + 1)
        | '\\' ->
            if index + 1 >= String.length value then policy_invalid_toml ()
            else
              let escaped = value.[index + 1] in
              let decoded =
                match escaped with
                | '"' -> Some '"'
                | '\\' -> Some '\\'
                | 'b' -> Some '\b'
                | 't' -> Some '\t'
                | 'n' -> Some '\n'
                | 'f' -> Some '\012'
                | 'r' -> Some '\r'
                | _ -> None
              in
              (match decoded with
              | None -> policy_invalid_toml ()
              | Some ch ->
                  Buffer.add_char buffer ch;
                  loop (index + 2))
        | ch ->
            if Char.code ch < 0x20 then policy_invalid_toml ()
            else (
              Buffer.add_char buffer ch;
              loop (index + 1))
    in
    loop (start + 1)

let parse_toml_string_value value =
  let trimmed = String.trim value in
  if trimmed = "null" then policy_invalid_toml ()
  else if not (starts_with trimmed "\"") then Ok None
  else
    match parse_toml_basic_string_at trimmed 0 with
    | Error err -> Error err
    | Ok (text, next) ->
        if String.trim (String.sub trimmed next (String.length trimmed - next)) = "" then
          Ok (Some text)
        else policy_invalid_toml ()

let parse_toml_bool_value field value =
  let trimmed = String.trim value in
  if trimmed = "null" then policy_invalid_toml ()
  else if trimmed = "true" then Ok true
  else if trimmed = "false" then Ok false
  else policy_parse_error field "bool" "wrong_type"

let parse_toml_string_array_value value =
  let trimmed = String.trim value in
  if trimmed = "null" then policy_invalid_toml ()
  else if not (starts_with trimmed "[") then Ok None
  else
    let rec loop index entries =
      let index = toml_skip_ws trimmed index in
      if index >= String.length trimmed then policy_invalid_toml ()
      else if trimmed.[index] = ']' then
        let next = index + 1 in
        if String.trim (String.sub trimmed next (String.length trimmed - next)) = "" then
          Ok (Some (List.rev entries))
        else policy_invalid_toml ()
      else
        let entry_result =
          if trimmed.[index] = '"' then
            match parse_toml_basic_string_at trimmed index with
            | Error err -> Error err
            | Ok (text, next) -> Ok (Policy_string text, next)
          else
            let rec find_end cursor =
              if cursor >= String.length trimmed then cursor
              else
                match trimmed.[cursor] with
                | ',' | ']' -> cursor
                | _ -> find_end (cursor + 1)
            in
            let end_index = find_end index in
            let raw = String.trim (String.sub trimmed index (end_index - index)) in
            if raw = "null" then policy_invalid_toml ()
            else Ok (Policy_non_string, end_index)
        in
        match entry_result with
        | Error err -> Error err
        | Ok (entry, after_entry) ->
            let next = toml_skip_ws trimmed after_entry in
            if next >= String.length trimmed then policy_invalid_toml ()
            else if trimmed.[next] = ',' then loop (next + 1) (entry :: entries)
            else if trimmed.[next] = ']' then loop next (entry :: entries)
            else policy_invalid_toml ()
    in
    loop 1 []

let name_of_dotted text =
  Ext_name.of_components (String.split_on_char '.' text)

let find_policy_assignment key assignments =
  List.find_opt (fun assignment -> assignment.assignment_key = key) assignments

let validate_policy_duplicates assignments =
  let rec loop seen remaining =
    match remaining with
    | [] -> Ok ()
    | assignment :: rest ->
        if List.mem assignment.assignment_key seen then
          policy_parse_error (policy_field_for_key assignment.assignment_key)
            "unique_object_keys" "duplicate_field"
        else loop (assignment.assignment_key :: seen) rest
  in
  loop [] assignments

let validate_policy_allowed_axioms assignment =
  match parse_toml_string_array_value assignment.assignment_value with
  | Error err -> Error err
  | Ok None ->
      policy_parse_error "axiom_policy.allowed_axioms" "array" "wrong_type"
  | Ok (Some entries) ->
      let rec parse_entries index remaining names =
        match remaining with
        | [] -> Ok (List.rev names)
        | Policy_non_string :: _ ->
            policy_parse_error
              ("axiom_policy.allowed_axioms[" ^ string_of_int index ^ "]")
              "axiom_name" "wrong_type"
        | Policy_string text :: rest -> (
            match name_of_dotted text with
            | None ->
                policy_parse_error
                  ("axiom_policy.allowed_axioms[" ^ string_of_int index ^ "]")
                  "axiom_name" "invalid_name_format"
            | Some name -> parse_entries (index + 1) rest (name :: names))
      in
      (match parse_entries 0 entries [] with
      | Error err -> Error err
      | Ok names ->
          let rec check_order index previous remaining =
            match remaining with
            | [] -> Ok ()
            | name :: rest ->
                let cmp = String.compare (Ext_name.to_string name)
                    (Ext_name.to_string previous)
                in
                if cmp < 0 then
                  policy_parse_error
                    ("axiom_policy.allowed_axioms[" ^ string_of_int index ^ "]")
                    "axiom_name_canonical_order" "order_violation"
                else check_order (index + 1) name rest
          in
          let order_result =
            match names with
            | [] | [ _ ] -> Ok ()
            | first :: rest -> check_order 1 first rest
          in
          (match order_result with
          | Error err -> Error err
          | Ok () ->
              let rec check_duplicates index seen remaining =
                match remaining with
                | [] -> Ok names
                | name :: rest ->
                    if List.exists (Ext_name.equal name) seen then
                      policy_parse_error
                        ("axiom_policy.allowed_axioms[" ^ string_of_int index ^ "]")
                        "unique_axiom_name" "duplicate_axiom_name"
                    else check_duplicates (index + 1) (name :: seen) rest
              in
              check_duplicates 0 [] names))

let parse_policy_toml source =
  if has_utf8_bom source then policy_invalid_toml ()
  else
    match collect_policy_assignments source with
    | Error err -> Error err
    | Ok assignments -> (
        match validate_policy_duplicates assignments with
        | Error err -> Error err
        | Ok () ->
            let parse_format policy =
              match find_policy_assignment "format" assignments with
              | None -> Ok policy
              | Some assignment -> (
                  match parse_toml_string_value assignment.assignment_value with
                  | Error err -> Error err
                  | Ok None ->
                      policy_parse_error "axiom_policy.format" policy_format
                        "wrong_type"
                  | Ok (Some value) ->
                      if value = policy_format || value = legacy_policy_format then
                        Ok policy
                      else
                        policy_parse_error "axiom_policy.format" policy_format
                          "invalid_fixed_value")
            in
            let parse_bool_field key update policy =
              match find_policy_assignment key assignments with
              | None -> Ok policy
              | Some assignment -> (
                  match
                    parse_toml_bool_value (policy_field_for_key key)
                      assignment.assignment_value
                  with
                  | Error err -> Error err
                  | Ok value -> Ok (update policy value))
            in
            let parse_allowed policy =
              match find_policy_assignment "allowed_axioms" assignments with
              | None -> Ok policy
              | Some assignment -> (
                  match validate_policy_allowed_axioms assignment with
                  | Error err -> Error err
                  | Ok allowed_axioms -> Ok { policy with allowed_axioms })
            in
            let parse_unknown policy =
              let known key =
                key = "format" || key = "deny_sorry"
                || key = "deny_custom_axioms" || key = "allowed_axioms"
              in
              let unknown =
                List.filter
                  (fun assignment -> not (known assignment.assignment_key))
                  assignments
              in
              let unknown =
                List.sort
                  (fun left right ->
                    String.compare left.assignment_key right.assignment_key)
                  unknown
              in
              match unknown with
              | [] -> Ok policy
              | assignment :: _ ->
                  policy_parse_error
                    (policy_field_for_key assignment.assignment_key)
                    "absent" "unknown_field"
            in
            let bind_policy result f =
              match result with
              | Error err -> Error err
              | Ok value -> f value
            in
            bind_policy (parse_format default_policy) (fun policy ->
                bind_policy
                  (parse_bool_field "deny_sorry"
                     (fun policy value -> { policy with deny_sorry = value })
                     policy)
                  (fun policy ->
                    bind_policy
                      (parse_bool_field "deny_custom_axioms"
                         (fun policy value ->
                           { policy with deny_custom_axioms = value })
                         policy)
                      (fun policy ->
                        bind_policy (parse_allowed policy) parse_unknown))))

type error = {
  section : Ext_bytes.certificate_section;
  offset : Ext_bytes.offset;
}

let error section offset = Error { section; offset }

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let error_kind _ = "axiom_report_mismatch"

let error_reason_code _ = "axiom_report_mismatch"

let rec list_nth_opt index values =
  match (index, values) with
  | _, _ when index < 0 -> None
  | 0, value :: _ -> Some value
  | _, _ :: rest -> list_nth_opt (index - 1) rest
  | _, [] -> None

let builtin_is_axiom name = Ext_name.to_string name = "Eq.rec"

let global_ref_equal left right = left = right

let dependency_equal left right =
  global_ref_equal left.Ext_cert.dependency_global_ref
    right.Ext_cert.dependency_global_ref
  && left.Ext_cert.dependency_decl_interface_hash
     = right.Ext_cert.dependency_decl_interface_hash

let axiom_equal left right =
  global_ref_equal left.Ext_cert.axiom_global_ref right.Ext_cert.axiom_global_ref
  && Ext_name.equal left.Ext_cert.axiom_name right.Ext_cert.axiom_name
  && left.Ext_cert.axiom_decl_interface_hash
     = right.Ext_cert.axiom_decl_interface_hash

let rec list_equal equal left right =
  match (left, right) with
  | [], [] -> true
  | left_value :: left_rest, right_value :: right_rest ->
      equal left_value right_value && list_equal equal left_rest right_rest
  | _ -> false

let name_id section offset name_table name =
  let rec loop index remaining =
    match remaining with
    | [] -> error section offset
    | entry :: rest ->
        if Ext_name.equal entry.Ext_cert.name name then Ok index
        else loop (index + 1) rest
  in
  loop 0 name_table

let encode_order_uvar value =
  let buffer = Buffer.create 5 in
  let rec loop current =
    let byte = current land 0x7f in
    let next = current lsr 7 in
    if next = 0 then Buffer.add_char buffer (Char.chr byte)
    else (
      Buffer.add_char buffer (Char.chr (byte lor 0x80));
      loop next)
  in
  if value < 0 then invalid_arg "negative uvar order key" else loop value;
  Buffer.contents buffer

let global_ref_order_key section offset name_table global_ref =
  match global_ref with
  | Ext_term.Imported { import_index; name; decl_interface_hash } ->
      bind (name_id section offset name_table name) (fun name_index ->
          Ok
            ("\000" ^ encode_order_uvar import_index
            ^ encode_order_uvar name_index ^ decl_interface_hash))
  | Ext_term.Local { decl_index } ->
      Ok ("\001" ^ encode_order_uvar decl_index)
  | Ext_term.LocalGenerated { decl_index; name } ->
      bind (name_id section offset name_table name) (fun name_index ->
          Ok ("\002" ^ encode_order_uvar decl_index ^ encode_order_uvar name_index))
  | Ext_term.Builtin { name; decl_interface_hash } ->
      bind (name_id section offset name_table name) (fun name_index ->
          Ok ("\003" ^ encode_order_uvar name_index ^ decl_interface_hash))

let axiom_order_key section offset name_table axiom =
  bind
    (global_ref_order_key section offset name_table axiom.Ext_cert.axiom_global_ref)
    (fun global_key ->
      bind (name_id section offset name_table axiom.Ext_cert.axiom_name)
        (fun name_index ->
          Ok
            (global_key ^ encode_order_uvar name_index
            ^ axiom.Ext_cert.axiom_decl_interface_hash)))

let dependency_order_key section offset name_table dependency =
  bind
    (global_ref_order_key section offset name_table
       dependency.Ext_cert.dependency_global_ref)
    (fun global_key ->
      Ok (global_key ^ dependency.Ext_cert.dependency_decl_interface_hash))

let sort_unique_by_key section offset name_table key_fn equal values =
  let rec key_values remaining keyed =
    match remaining with
    | [] -> Ok keyed
    | value :: rest ->
        bind (key_fn section offset name_table value) (fun key ->
            key_values rest ((key, value) :: keyed))
  in
  bind (key_values values []) (fun keyed ->
      let sorted =
        List.sort (fun (left, _) (right, _) -> String.compare left right) keyed
      in
      let rec unique remaining previous values =
        match remaining with
        | [] -> Ok (List.rev values)
        | (_, value) :: rest -> (
            match previous with
            | Some previous_value when equal previous_value value ->
                unique rest previous values
            | _ -> unique rest (Some value) (value :: values))
      in
      unique sorted None [])

let sort_unique_axioms section offset name_table axioms =
  sort_unique_by_key section offset name_table axiom_order_key axiom_equal axioms

let sort_unique_dependencies section offset name_table dependencies =
  sort_unique_by_key section offset name_table dependency_order_key
    dependency_equal dependencies

let rec append_global_refs term refs =
  Ext_canonical.collect_global_refs_from_term term refs

let declaration_terms payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_ty; _ } -> [ decl_ty ]
  | Ext_cert.DefDecl { decl_ty; decl_value; _ } -> [ decl_ty; decl_value ]
  | Ext_cert.TheoremDecl { decl_ty; decl_proof; _ } -> [ decl_ty; decl_proof ]
  | Ext_cert.InductiveDecl { ind_params; ind_indices; ind_constructors; ind_recursor; _ } ->
      let recursor_terms =
        match ind_recursor with
        | None -> []
        | Some recursor -> [ recursor.Ext_cert.recursor_ty ]
      in
      List.map (fun binder -> binder.Ext_cert.binder_ty) ind_params
      @ List.map (fun binder -> binder.Ext_cert.binder_ty) ind_indices
      @ List.map (fun constructor -> constructor.Ext_cert.constructor_ty) ind_constructors
      @ recursor_terms
  | Ext_cert.MutualInductiveBlockDecl { mutual_inductives; _ } ->
      let terms_for_inductive inductive =
        let recursor_terms =
          match inductive.Ext_cert.mutual_recursor with
          | None -> []
          | Some recursor -> [ recursor.Ext_cert.recursor_ty ]
        in
        List.map (fun binder -> binder.Ext_cert.binder_ty) inductive.Ext_cert.mutual_params
        @ List.map
            (fun binder -> binder.Ext_cert.binder_ty)
            inductive.Ext_cert.mutual_indices
        @ List.map
            (fun constructor -> constructor.Ext_cert.constructor_ty)
            inductive.Ext_cert.mutual_constructors
        @ recursor_terms
      in
      List.concat (List.map terms_for_inductive mutual_inductives)

let generated_name_exists declaration name =
  match declaration.Ext_cert.payload with
  | Ext_cert.InductiveDecl { ind_constructors; ind_recursor; _ } ->
      List.exists
        (fun constructor ->
          Ext_name.equal constructor.Ext_cert.constructor_name name)
        ind_constructors
      ||
      (match ind_recursor with
      | None -> false
      | Some recursor -> Ext_name.equal recursor.Ext_cert.recursor_name name)
  | Ext_cert.MutualInductiveBlockDecl { mutual_inductives; _ } ->
      List.exists
        (fun inductive ->
          Ext_name.equal inductive.Ext_cert.mutual_name name
          || List.exists
               (fun constructor ->
                 Ext_name.equal constructor.Ext_cert.constructor_name name)
               inductive.Ext_cert.mutual_constructors
          ||
          match inductive.Ext_cert.mutual_recursor with
          | None -> false
          | Some recursor -> Ext_name.equal recursor.Ext_cert.recursor_name name)
        mutual_inductives
  | _ -> false

let find_import import_index imports =
  list_nth_opt import_index (Ext_import_store.import_environment_imports imports)

let find_public_export name decl_interface_hash exports =
  let rec loop remaining =
    match remaining with
    | [] -> None
    | export :: rest ->
        if
          Ext_name.equal export.Ext_import_store.public_export_name name
          && export.Ext_import_store.public_decl_interface_hash = decl_interface_hash
        then Some export
        else loop rest
  in
  loop exports

let imported_export_for_global_ref section offset imports global_ref =
  match global_ref with
  | Ext_term.Imported { import_index; name; decl_interface_hash } -> (
      match find_import import_index imports with
      | None -> error section offset
      | Some import -> (
          match
            find_public_export name decl_interface_hash
              import.Ext_import_store.resolved_public_environment
                .Ext_import_store.public_exports
          with
          | None -> error section offset
          | Some export -> Ok export))
  | _ -> error section offset

let interface_hash_for_global_ref section offset name_table imports current_decl_index
    (declarations : Ext_cert.declaration list) global_ref =
  match global_ref with
  | Ext_term.Builtin { name; decl_interface_hash } -> (
      match Ext_env.builtin_decl_interface_hash name with
      | Some expected when expected = decl_interface_hash -> Ok decl_interface_hash
      | _ -> error section offset)
  | Ext_term.Imported { decl_interface_hash; _ } ->
      bind
        (imported_export_for_global_ref section offset imports global_ref)
        (fun _ -> Ok decl_interface_hash)
  | Ext_term.Local { decl_index } -> (
      if decl_index >= current_decl_index then error section offset
      else
        match list_nth_opt decl_index declarations with
        | None -> error section offset
        | Some declaration ->
            Ok (declaration.Ext_cert.hashes).Ext_cert.decl_interface_hash)
  | Ext_term.LocalGenerated { decl_index; name } -> (
      if decl_index >= current_decl_index then error section offset
      else
        match list_nth_opt decl_index declarations with
        | Some declaration when generated_name_exists declaration name ->
            Ok (declaration.Ext_cert.hashes).Ext_cert.decl_interface_hash
        | _ -> error section offset)

let allow_self_reference payload =
  match payload with
  | Ext_cert.InductiveDecl _ | Ext_cert.MutualInductiveBlockDecl _ -> true
  | _ -> false

let expected_dependencies_for_decl section offset name_table imports decl_index
    declarations declaration =
  let refs =
    List.fold_left
      (fun refs term -> append_global_refs term refs)
      [] (declaration_terms declaration.Ext_cert.payload)
  in
  let refs =
    List.filter
      (function
        | Ext_term.Local { decl_index = referenced_decl_index }
        | Ext_term.LocalGenerated { decl_index = referenced_decl_index; _ }
          when allow_self_reference declaration.Ext_cert.payload
               && referenced_decl_index = decl_index ->
            false
        | _ -> true)
      refs
  in
  let rec loop remaining dependencies =
    match remaining with
    | [] -> sort_unique_dependencies section offset name_table dependencies
    | global_ref :: rest ->
        bind
          (interface_hash_for_global_ref section offset name_table imports decl_index
             declarations global_ref)
          (fun decl_interface_hash ->
            loop rest
              ({
                 Ext_cert.dependency_global_ref = global_ref;
                 dependency_decl_interface_hash = decl_interface_hash;
               }
              :: dependencies))
  in
  loop refs []

let local_axiom_ref_for_decl decl_index axioms =
  let rec loop remaining =
    match remaining with
    | [] -> None
    | axiom :: rest -> (
        match axiom.Ext_cert.axiom_global_ref with
        | Ext_term.Local { decl_index = axiom_decl_index }
          when axiom_decl_index = decl_index ->
            Some axiom
        | _ -> loop rest)
  in
  loop axioms

let import_index_exporting_axiom imports name decl_interface_hash =
  let rec loop index remaining =
    match remaining with
    | [] -> None
    | import :: rest ->
        if
          List.exists
            (fun export ->
              export.Ext_import_store.public_export_kind = Ext_cert.Export_axiom
              && Ext_name.equal export.Ext_import_store.public_export_name name
              && export.Ext_import_store.public_decl_interface_hash
                 = decl_interface_hash)
            import.Ext_import_store.resolved_public_environment
              .Ext_import_store.public_exports
        then Some index
        else loop (index + 1) rest
  in
  loop 0 (Ext_import_store.import_environment_imports imports)

let remap_imported_axiom_dependency section offset name_table imports axiom =
  bind (name_id section offset name_table axiom.Ext_cert.axiom_name) (fun _ ->
      match
        import_index_exporting_axiom imports axiom.Ext_cert.axiom_name
          axiom.Ext_cert.axiom_decl_interface_hash
      with
      | Some import_index ->
          Ok
            {
              axiom with
              Ext_cert.axiom_global_ref =
                Ext_term.Imported
                  {
                    import_index;
                    name = axiom.Ext_cert.axiom_name;
                    decl_interface_hash =
                      axiom.Ext_cert.axiom_decl_interface_hash;
                  };
            }
      | None ->
          if
            builtin_is_axiom axiom.Ext_cert.axiom_name
            && Ext_env.builtin_decl_interface_hash axiom.Ext_cert.axiom_name
               = Some axiom.Ext_cert.axiom_decl_interface_hash
          then
            Ok
              {
                axiom with
                Ext_cert.axiom_global_ref =
                  Ext_term.Builtin
                    {
                      name = axiom.Ext_cert.axiom_name;
                      decl_interface_hash =
                        axiom.Ext_cert.axiom_decl_interface_hash;
                    };
              }
          else error section offset)

let expected_axioms_for_decl section offset name_table imports decl_index declaration
    dependencies previous_axioms =
  let direct = ref [] in
  let transitive = ref [] in
  let add_direct axiom = direct := axiom :: !direct in
  let add_transitive axiom = transitive := axiom :: !transitive in
  let add_transitive_all axioms = transitive := axioms @ !transitive in
  let rec loop_dependencies remaining =
    match remaining with
    | [] -> Ok ()
    | dependency :: rest -> (
        match dependency.Ext_cert.dependency_global_ref with
        | Ext_term.Builtin { name; decl_interface_hash } ->
            if builtin_is_axiom name then (
              let axiom =
                {
                  Ext_cert.axiom_global_ref =
                    dependency.Ext_cert.dependency_global_ref;
                  axiom_name = name;
                  axiom_decl_interface_hash = decl_interface_hash;
                }
              in
              add_direct axiom;
              add_transitive axiom);
            loop_dependencies rest
        | Ext_term.Local { decl_index = dependency_index } -> (
            match list_nth_opt dependency_index previous_axioms with
            | None -> error section offset
            | Some dep_axioms ->
                (match local_axiom_ref_for_decl dependency_index dep_axioms with
                | None -> ()
                | Some axiom -> add_direct axiom);
                add_transitive_all dep_axioms;
                loop_dependencies rest)
        | Ext_term.LocalGenerated { decl_index = dependency_index; _ } -> (
            match list_nth_opt dependency_index previous_axioms with
            | None -> error section offset
            | Some dep_axioms ->
                add_transitive_all dep_axioms;
                loop_dependencies rest)
        | Ext_term.Imported { name; decl_interface_hash; _ } ->
            bind
              (imported_export_for_global_ref section offset imports
                 dependency.Ext_cert.dependency_global_ref)
              (fun export ->
                if export.Ext_import_store.public_export_kind = Ext_cert.Export_axiom then
                  add_direct
                    {
                      Ext_cert.axiom_global_ref =
                        dependency.Ext_cert.dependency_global_ref;
                      axiom_name = name;
                      axiom_decl_interface_hash = decl_interface_hash;
                    };
                let rec loop_axioms remaining =
                  match remaining with
                  | [] -> Ok ()
                  | axiom :: rest_axioms ->
                      bind
                        (remap_imported_axiom_dependency Ext_bytes.Axiom_report
                           offset name_table imports axiom)
                        (fun remapped ->
                          add_transitive remapped;
                          loop_axioms rest_axioms)
                in
                bind
                  (loop_axioms
                     export.Ext_import_store.public_axiom_dependencies)
                  (fun () -> loop_dependencies rest)))
  in
  bind (loop_dependencies dependencies) (fun () ->
      (match declaration.Ext_cert.payload with
      | Ext_cert.AxiomDecl { decl_name; _ } ->
          let self_ref =
            {
              Ext_cert.axiom_global_ref = Ext_term.Local { decl_index };
              axiom_name = decl_name;
              axiom_decl_interface_hash =
                (declaration.Ext_cert.hashes).Ext_cert.decl_interface_hash;
            }
          in
          add_direct self_ref;
          add_transitive self_ref
      | _ -> ());
      bind (sort_unique_axioms section offset name_table !direct) (fun direct ->
          bind (sort_unique_axioms section offset name_table !transitive)
            (fun transitive -> Ok (direct, transitive))))

let recompute_axiom_report imports (decoded : Ext_cert.decoded_module) =
  let section = Ext_bytes.Axiom_report in
  let name_table = decoded.Ext_cert.name_table in
  if
    List.length decoded.Ext_cert.axiom_report.Ext_cert.per_declaration
    <> List.length decoded.Ext_cert.declaration_table
  then
    error section decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
  else
    let rec loop decl_index (declarations : Ext_cert.declaration list)
        previous_axioms reports transitive_by_decl =
      match declarations with
      | [] ->
          bind
            (sort_unique_axioms section
               decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
               name_table (List.concat (List.rev transitive_by_decl)))
            (fun module_axioms ->
              Ok
                {
                  decoded.Ext_cert.axiom_report with
                  Ext_cert.per_declaration = List.rev reports;
                  module_axioms;
                })
      | declaration :: rest -> (
          let actual_report =
            list_nth_opt decl_index
              decoded.Ext_cert.axiom_report.Ext_cert.per_declaration
          in
          match actual_report with
          | None ->
              error section
                decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
          | Some actual_report -> (
              let offset = declaration.Ext_cert.offset in
              match
                expected_dependencies_for_decl Ext_bytes.Declarations offset name_table
                  imports decl_index decoded.Ext_cert.declaration_table declaration
              with
              | Error err -> Error err
              | Ok dependencies ->
                  if
                    not
                      (list_equal dependency_equal dependencies
                         declaration.Ext_cert.dependencies)
                  then error Ext_bytes.Declarations offset
                  else
                    bind
                      (expected_axioms_for_decl Ext_bytes.Declarations offset name_table
                         imports decl_index declaration dependencies previous_axioms)
                      (fun (direct_axioms, transitive_axioms) ->
                        let report =
                          {
                            actual_report with
                            Ext_cert.report_decl_index = decl_index;
                            report_direct_axioms = direct_axioms;
                            report_transitive_axioms = transitive_axioms;
                          }
                        in
                        loop (decl_index + 1) rest
                          (previous_axioms @ [ transitive_axioms ])
                          (report :: reports)
                          (transitive_axioms :: transitive_by_decl))))
    in
    loop 0 decoded.Ext_cert.declaration_table [] [] []

let verify_axiom_report imports (decoded : Ext_cert.decoded_module) =
  let stored_report = decoded.Ext_cert.axiom_report in
  bind (recompute_axiom_report imports decoded) (fun expected_report ->
      let rec compare_declaration_reports expected actual =
        match (expected, actual) with
        | [], [] -> Ok ()
        | expected_entry :: expected_rest, actual_entry :: actual_rest ->
            if
              expected_entry.Ext_cert.report_decl_index
              <> actual_entry.Ext_cert.report_decl_index
              || not
                   (list_equal axiom_equal
                      expected_entry.Ext_cert.report_direct_axioms
                      actual_entry.Ext_cert.report_direct_axioms)
              || not
                   (list_equal axiom_equal
                      expected_entry.Ext_cert.report_transitive_axioms
                      actual_entry.Ext_cert.report_transitive_axioms)
            then error Ext_bytes.Axiom_report actual_entry.Ext_cert.report_offset
            else compare_declaration_reports expected_rest actual_rest
        | _ ->
            error Ext_bytes.Axiom_report stored_report.Ext_cert.module_axioms_offset
      in
      bind
        (compare_declaration_reports expected_report.Ext_cert.per_declaration
           stored_report.Ext_cert.per_declaration)
        (fun () ->
          if
            not
              (list_equal axiom_equal expected_report.Ext_cert.module_axioms
                 stored_report.Ext_cert.module_axioms)
          then
            error Ext_bytes.Axiom_report
              stored_report.Ext_cert.module_axioms_offset
          else
            let rec compare_declaration_axioms decl_index declarations =
              match declarations with
              | [] -> Ok ()
              | declaration :: rest -> (
                  match
                    list_nth_opt decl_index
                      expected_report.Ext_cert.per_declaration
                  with
                  | None ->
                      error Ext_bytes.Axiom_report
                        stored_report.Ext_cert.module_axioms_offset
                  | Some report ->
                      if
                        list_equal axiom_equal declaration.Ext_cert.axiom_dependencies
                          report.Ext_cert.report_transitive_axioms
                      then compare_declaration_axioms (decl_index + 1) rest
                      else error Ext_bytes.Declarations declaration.Ext_cert.offset)
            in
            bind
              (compare_declaration_axioms 0 decoded.Ext_cert.declaration_table)
              (fun () ->
                match
                  Ext_canonical.encode_axiom_report decoded.Ext_cert.name_table
                    expected_report
                with
                | Error _ ->
                    error Ext_bytes.Axiom_report
                      stored_report.Ext_cert.module_axioms_offset
                | Ok payload ->
                    let expected_hash =
                      Ext_canonical.hash_with_domain
                        Ext_canonical.domain_axiom_report payload
                    in
                    if expected_hash = (decoded.Ext_cert.hashes).Ext_cert.axiom_report_hash
                    then Ok ()
                    else
                      error Ext_bytes.Hashes
                        (decoded.Ext_cert.hashes).Ext_cert.axiom_report_hash_offset)))

type policy_violation_reason =
  | Sorry_denied
  | Forbidden_axiom

type policy_check_error = {
  policy_section : Ext_bytes.certificate_section;
  policy_offset : Ext_bytes.offset;
  policy_reason : policy_violation_reason;
}

let policy_check_error section offset reason =
  Error { policy_section = section; policy_offset = offset; policy_reason = reason }

let policy_check_error_kind _ = "forbidden_axiom"

let policy_check_error_reason_code error =
  match error.policy_reason with
  | Sorry_denied -> "sorry_denied"
  | Forbidden_axiom -> "forbidden_axiom"

let contains_substring text needle =
  let text_len = String.length text in
  let needle_len = String.length needle in
  let rec loop index =
    if needle_len = 0 then true
    else if index + needle_len > text_len then false
    else if String.sub text index needle_len = needle then true
    else loop (index + 1)
  in
  loop 0

let option_exists predicate value =
  match value with
  | None -> false
  | Some value -> predicate value

let public_export_matches_axiom_ref axiom export =
  export.Ext_import_store.public_export_kind = Ext_cert.Export_axiom
  && Ext_name.equal export.Ext_import_store.public_export_name
       axiom.Ext_cert.axiom_name
  && export.Ext_import_store.public_decl_interface_hash
     = axiom.Ext_cert.axiom_decl_interface_hash

let import_exports_axiom import axiom =
  List.exists
    (public_export_matches_axiom_ref axiom)
    import.Ext_import_store.resolved_public_environment
      .Ext_import_store.public_exports

let import_environment_exports_axiom imports axiom =
  match
    import_index_exporting_axiom imports axiom.Ext_cert.axiom_name
      axiom.Ext_cert.axiom_decl_interface_hash
  with
  | Some _ -> true
  | None -> false

let qualify_name module_name raw_name =
  Ext_name.components module_name @ Ext_name.components raw_name

let global_ref_hash_matches_axiom imports (decoded : Ext_cert.decoded_module) axiom =
  match axiom.Ext_cert.axiom_global_ref with
  | Ext_term.Builtin { name; decl_interface_hash } ->
      Ext_name.equal name axiom.Ext_cert.axiom_name
      && decl_interface_hash = axiom.Ext_cert.axiom_decl_interface_hash
      && Ext_env.builtin_decl_interface_hash name = Some decl_interface_hash
  | Ext_term.Imported { name; decl_interface_hash; _ } -> (
      Ext_name.equal name axiom.Ext_cert.axiom_name
      && decl_interface_hash = axiom.Ext_cert.axiom_decl_interface_hash
      &&
      match
        imported_export_for_global_ref Ext_bytes.Axiom_report
          decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset imports
          axiom.Ext_cert.axiom_global_ref
      with
      | Ok _ -> true
      | Error _ -> false)
  | Ext_term.Local { decl_index } -> (
      match list_nth_opt decl_index decoded.Ext_cert.declaration_table with
      | Some declaration ->
          declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
          = axiom.Ext_cert.axiom_decl_interface_hash
      | None -> false)
  | Ext_term.LocalGenerated { decl_index; name } -> (
      Ext_name.equal name axiom.Ext_cert.axiom_name
      &&
      match list_nth_opt decl_index decoded.Ext_cert.declaration_table with
      | Some declaration ->
          generated_name_exists declaration name
          && declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
             = axiom.Ext_cert.axiom_decl_interface_hash
      | None -> false)

let qualified_name_for_axiom imports decoded axiom =
  match axiom.Ext_cert.axiom_global_ref with
  | Ext_term.Imported { import_index; _ } -> (
      match find_import import_index imports with
      | None -> None
      | Some import ->
          Some
            (qualify_name import.Ext_import_store.resolved_module_name
               axiom.Ext_cert.axiom_name))
  | Ext_term.Local _ | Ext_term.LocalGenerated _ ->
      Some
        (qualify_name decoded.Ext_cert.header.Ext_cert.module_name
           axiom.Ext_cert.axiom_name)
  | Ext_term.Builtin _ -> None

let is_standard_eq_rec_exception imports decoded axiom =
  match axiom.Ext_cert.axiom_global_ref with
  | Ext_term.Builtin _ ->
      Ext_name.to_string axiom.Ext_cert.axiom_name = "Eq.rec"
      && global_ref_hash_matches_axiom imports decoded axiom
  | Ext_term.Imported _ | Ext_term.Local _ | Ext_term.LocalGenerated _ ->
      option_exists
        (fun qualified ->
          Ext_name.to_string qualified = "Std.Logic.Eq.rec"
          && global_ref_hash_matches_axiom imports decoded axiom)
        (qualified_name_for_axiom imports decoded axiom)

let policy_allows_axiom_name policy raw_name qualified_name =
  policy_allows policy raw_name
  || option_exists (fun name -> policy_allows policy name) qualified_name

let enforce_axiom_policy_name policy raw_name qualified_name is_standard_exception
    section offset =
  if
    policy.deny_sorry
    && (contains_substring (Ext_name.to_string raw_name) "sorry"
       || option_exists
            (fun name -> contains_substring (Ext_name.to_string name) "sorry")
            qualified_name)
  then policy_check_error section offset Sorry_denied
  else
    let require_allowlist =
      policy.deny_custom_axioms || policy.allowed_axioms <> []
    in
    if
      (not require_allowlist) || is_standard_exception
      || policy_allows_axiom_name policy raw_name qualified_name
    then Ok ()
    else policy_check_error section offset Forbidden_axiom

let enforce_axiom_ref_policy imports decoded policy axiom =
  enforce_axiom_policy_name policy axiom.Ext_cert.axiom_name
    (qualified_name_for_axiom imports decoded axiom)
    (is_standard_eq_rec_exception imports decoded axiom)
    Ext_bytes.Axiom_report
    decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset

let qualified_name_for_import_axiom imports import axiom =
  if import_exports_axiom import axiom then
    Some
      (qualify_name import.Ext_import_store.resolved_module_name
         axiom.Ext_cert.axiom_name)
  else
    match
      import_index_exporting_axiom imports axiom.Ext_cert.axiom_name
        axiom.Ext_cert.axiom_decl_interface_hash
    with
    | Some import_index -> (
      match find_import import_index imports with
      | Some import ->
          Some
            (qualify_name import.Ext_import_store.resolved_module_name
               axiom.Ext_cert.axiom_name)
      | None ->
          Some
            (qualify_name import.Ext_import_store.resolved_module_name
               axiom.Ext_cert.axiom_name))
    | None ->
        Some
          (qualify_name import.Ext_import_store.resolved_module_name
             axiom.Ext_cert.axiom_name)

let is_standard_import_eq_rec_exception imports import axiom =
  option_exists
    (fun qualified ->
      Ext_name.to_string qualified = "Std.Logic.Eq.rec"
      && (import_exports_axiom import axiom
         || import_environment_exports_axiom imports axiom))
    (qualified_name_for_import_axiom imports import axiom)

let enforce_import_axiom_policy imports policy import axiom offset =
  enforce_axiom_policy_name policy axiom.Ext_cert.axiom_name
    (qualified_name_for_import_axiom imports import axiom)
    (is_standard_import_eq_rec_exception imports import axiom)
    Ext_bytes.Imports offset

let enforce_axiom_policy imports decoded policy =
  let rec enforce_imports index remaining =
    match remaining with
    | [] -> Ok ()
    | import :: rest ->
        let offset =
          match list_nth_opt index decoded.Ext_cert.imports with
          | Some located -> located.Ext_cert.import_offset
          | None -> 0
        in
        let rec enforce_axioms axioms =
          match axioms with
          | [] -> Ok ()
          | axiom :: axiom_rest -> (
              match
                enforce_import_axiom_policy imports policy
                  import axiom offset
              with
              | Error err -> Error err
              | Ok () -> enforce_axioms axiom_rest)
        in
        (match
           enforce_axioms
             import.Ext_import_store.resolved_public_environment
               .Ext_import_store.public_module_axioms
         with
        | Error err -> Error err
        | Ok () -> enforce_imports (index + 1) rest)
  in
  match enforce_imports 0 (Ext_import_store.import_environment_imports imports) with
  | Error err -> Error err
  | Ok () ->
      let rec enforce_module_axioms axioms =
        match axioms with
        | [] -> Ok ()
        | axiom :: rest -> (
            match enforce_axiom_ref_policy imports decoded policy axiom with
            | Error err -> Error err
            | Ok () -> enforce_module_axioms rest)
      in
      enforce_module_axioms decoded.Ext_cert.axiom_report.Ext_cert.module_axioms
