let domain_level = "NPA-LEVEL-0.1"

let domain_term = "NPA-TERM-0.1"

let domain_decl_interface = "NPA-DECL-IFACE-0.1"

let domain_decl_certificate = "NPA-DECL-CERT-0.1"

let domain_generated_recursor_signature = "NPA-GEN-REC-SIG-0.1"

let domain_generated_computation_rule = "NPA-GEN-COMP-RULE-0.1"

let domain_module_export = "NPA-MODULE-EXPORT-0.1"

let domain_axiom_report = "NPA-AXIOM-REPORT-0.1"

let domain_module_certificate = "NPA-MODULE-CERT-0.1"

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

exception Encode_error of Ext_bytes.decode_error

let unwrap result =
  match result with
  | Ok value -> value
  | Error err -> raise (Encode_error err)

let capture f =
  try Ok (f ()) with
  | Encode_error err -> Error err

let byte value = String.make 1 (Char.chr value)

let encode_uvar value = Ext_bytes.encode_uvar (Int64.of_int value)

let encode_hash hash = hash

let encode_string value = encode_uvar (String.length value) ^ value

let encode_name name =
  let components = Ext_name.components name in
  encode_uvar (List.length components)
  ^ String.concat "" (List.map encode_string components)

let hash_with_domain domain payload =
  Bytes.to_string (Ext_hash.sha256_raw_string (domain ^ payload))

let error section offset reason = Ext_bytes.error section offset reason

let name_id section offset name_table name =
  let rec loop index entries =
    match entries with
    | [] -> error section offset Ext_bytes.Dangling_reference
    | entry :: rest ->
        if Ext_name.equal entry.Ext_cert.name name then Ok index else loop (index + 1) rest
  in
  loop 0 name_table

let term_id section offset term_table term =
  let rec loop index entries =
    match entries with
    | [] -> error section offset Ext_bytes.Dangling_reference
    | entry :: rest ->
        if entry.Ext_term.term = term then Ok index else loop (index + 1) rest
  in
  loop 0 term_table

let encode_name_id section offset name_table name =
  bind (name_id section offset name_table name) (fun id -> Ok (encode_uvar id))

let encode_name_value section offset name_table name =
  bind (name_id section offset name_table name) (fun _ -> Ok (encode_name name))

let encode_name_values section offset name_table names =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length names) ^ String.concat "" (List.rev encoded))
    | name :: rest ->
        bind (encode_name_value section offset name_table name) (fun bytes ->
            loop rest (bytes :: encoded))
  in
  loop names []

let encode_term_id section offset term_table term =
  bind (term_id section offset term_table term) (fun id -> Ok (encode_uvar id))

let encode_global_ref section offset name_table global_ref =
  match global_ref with
  | Ext_term.Imported { import_index; name; decl_interface_hash } ->
      bind (encode_name_id section offset name_table name) (fun name_bytes ->
          Ok (byte 0x00 ^ encode_uvar import_index ^ name_bytes ^ encode_hash decl_interface_hash))
  | Ext_term.Local { decl_index } -> Ok (byte 0x01 ^ encode_uvar decl_index)
  | Ext_term.LocalGenerated { decl_index; name } ->
      bind (encode_name_id section offset name_table name) (fun name_bytes ->
          Ok (byte 0x02 ^ encode_uvar decl_index ^ name_bytes))
  | Ext_term.Builtin { name; decl_interface_hash } ->
      bind (encode_name_id section offset name_table name) (fun name_bytes ->
          Ok (byte 0x03 ^ name_bytes ^ encode_hash decl_interface_hash))

let rec level_payload level =
  match level with
  | Ext_level.Zero -> byte 0x00
  | Ext_level.Succ inner -> byte 0x01 ^ level_hash inner
  | Ext_level.Max (lhs, rhs) -> byte 0x02 ^ level_hash lhs ^ level_hash rhs
  | Ext_level.Imax (lhs, rhs) -> byte 0x03 ^ level_hash lhs ^ level_hash rhs
  | Ext_level.Param name -> byte 0x04 ^ encode_name name

and level_hash level = hash_with_domain domain_level (level_payload level)

let rec term_payload section offset name_table term =
  match term with
  | Ext_term.Sort level -> Ok (byte 0x00 ^ level_hash level)
  | Ext_term.BVar index -> Ok (byte 0x01 ^ encode_uvar index)
  | Ext_term.Const (global_ref, levels) ->
      bind (encode_global_ref section offset name_table global_ref) (fun global_ref_bytes ->
          Ok
            (byte 0x02 ^ global_ref_bytes ^ encode_uvar (List.length levels)
           ^ String.concat "" (List.map level_hash levels)))
  | Ext_term.App (fn, arg) ->
      bind (term_hash section offset name_table fn) (fun fn_hash ->
          bind (term_hash section offset name_table arg) (fun arg_hash ->
              Ok (byte 0x03 ^ fn_hash ^ arg_hash)))
  | Ext_term.Lam (ty, body) ->
      bind (term_hash section offset name_table ty) (fun ty_hash ->
          bind (term_hash section offset name_table body) (fun body_hash ->
              Ok (byte 0x04 ^ ty_hash ^ body_hash)))
  | Ext_term.Pi (ty, body) ->
      bind (term_hash section offset name_table ty) (fun ty_hash ->
          bind (term_hash section offset name_table body) (fun body_hash ->
              Ok (byte 0x05 ^ ty_hash ^ body_hash)))
  | Ext_term.Let (ty, value, body) ->
      bind (term_hash section offset name_table ty) (fun ty_hash ->
          bind (term_hash section offset name_table value) (fun value_hash ->
              bind (term_hash section offset name_table body) (fun body_hash ->
                  Ok (byte 0x06 ^ ty_hash ^ value_hash ^ body_hash))))

and term_hash section offset name_table term =
  bind (term_payload section offset name_table term) (fun payload ->
      Ok (hash_with_domain domain_term payload))

let lookup_level_hash section offset level_table level_hashes level =
  let rec loop levels hashes =
    match (levels, hashes) with
    | entry :: rest_levels, hash :: rest_hashes ->
        if entry.Ext_level.level = level then Ok hash else loop rest_levels rest_hashes
    | _ -> error section offset Ext_bytes.Dangling_reference
  in
  loop level_table level_hashes

let level_entry_payload offset previous_levels previous_hashes level =
  match level with
  | Ext_level.Zero -> Ok (byte 0x00)
  | Ext_level.Succ inner ->
      bind
        (lookup_level_hash Ext_bytes.Level_table offset previous_levels previous_hashes inner)
        (fun inner_hash -> Ok (byte 0x01 ^ inner_hash))
  | Ext_level.Max (lhs, rhs) ->
      bind
        (lookup_level_hash Ext_bytes.Level_table offset previous_levels previous_hashes lhs)
        (fun lhs_hash ->
          bind
            (lookup_level_hash Ext_bytes.Level_table offset previous_levels previous_hashes rhs)
            (fun rhs_hash -> Ok (byte 0x02 ^ lhs_hash ^ rhs_hash)))
  | Ext_level.Imax (lhs, rhs) ->
      bind
        (lookup_level_hash Ext_bytes.Level_table offset previous_levels previous_hashes lhs)
        (fun lhs_hash ->
          bind
            (lookup_level_hash Ext_bytes.Level_table offset previous_levels previous_hashes rhs)
            (fun rhs_hash -> Ok (byte 0x03 ^ lhs_hash ^ rhs_hash)))
  | Ext_level.Param name -> Ok (byte 0x04 ^ encode_name name)

let level_hashes level_table =
  let rec loop processed_levels processed_hashes remaining =
    match remaining with
    | [] -> Ok (List.rev processed_hashes)
    | entry :: rest ->
        bind
          (level_entry_payload entry.Ext_level.offset processed_levels processed_hashes
             entry.Ext_level.level)
          (fun payload ->
            loop (entry :: processed_levels)
              (hash_with_domain domain_level payload :: processed_hashes)
              rest)
  in
  loop [] [] level_table

let lookup_term_hash section offset term_table term_hashes term =
  let rec loop terms hashes =
    match (terms, hashes) with
    | entry :: rest_terms, hash :: rest_hashes ->
        if entry.Ext_term.term = term then Ok hash else loop rest_terms rest_hashes
    | _ -> error section offset Ext_bytes.Dangling_reference
  in
  loop term_table term_hashes

let term_entry_payload section offset name_table level_table level_hashes previous_terms
    previous_hashes term =
  match term with
  | Ext_term.Sort level ->
      bind (lookup_level_hash section offset level_table level_hashes level) (fun level_hash ->
          Ok (byte 0x00 ^ level_hash))
  | Ext_term.BVar index -> Ok (byte 0x01 ^ encode_uvar index)
  | Ext_term.Const (global_ref, levels) ->
      bind (encode_global_ref section offset name_table global_ref) (fun global_ref_bytes ->
          let rec loop remaining encoded =
            match remaining with
            | [] ->
                Ok
                  (byte 0x02 ^ global_ref_bytes ^ encode_uvar (List.length levels)
                 ^ String.concat "" (List.rev encoded))
            | level :: rest ->
                bind (lookup_level_hash section offset level_table level_hashes level)
                  (fun level_hash -> loop rest (level_hash :: encoded))
          in
          loop levels [])
  | Ext_term.App (fn, arg) ->
      bind (lookup_term_hash section offset previous_terms previous_hashes fn) (fun fn_hash ->
          bind
            (lookup_term_hash section offset previous_terms previous_hashes arg)
            (fun arg_hash -> Ok (byte 0x03 ^ fn_hash ^ arg_hash)))
  | Ext_term.Lam (ty, body) ->
      bind (lookup_term_hash section offset previous_terms previous_hashes ty) (fun ty_hash ->
          bind
            (lookup_term_hash section offset previous_terms previous_hashes body)
            (fun body_hash -> Ok (byte 0x04 ^ ty_hash ^ body_hash)))
  | Ext_term.Pi (ty, body) ->
      bind (lookup_term_hash section offset previous_terms previous_hashes ty) (fun ty_hash ->
          bind
            (lookup_term_hash section offset previous_terms previous_hashes body)
            (fun body_hash -> Ok (byte 0x05 ^ ty_hash ^ body_hash)))
  | Ext_term.Let (ty, value, body) ->
      bind (lookup_term_hash section offset previous_terms previous_hashes ty) (fun ty_hash ->
          bind
            (lookup_term_hash section offset previous_terms previous_hashes value)
            (fun value_hash ->
              bind
                (lookup_term_hash section offset previous_terms previous_hashes body)
                (fun body_hash -> Ok (byte 0x06 ^ ty_hash ^ value_hash ^ body_hash))))

let term_hashes name_table level_table level_hashes term_table =
  let rec loop processed_terms processed_hashes remaining =
    match remaining with
    | [] -> Ok (List.rev processed_hashes)
    | entry :: rest ->
        bind
          (term_entry_payload Ext_bytes.Term_table entry.Ext_term.offset name_table level_table
             level_hashes processed_terms processed_hashes entry.Ext_term.term)
          (fun payload ->
            loop (entry :: processed_terms)
              (hash_with_domain domain_term payload :: processed_hashes)
              rest)
  in
  loop [] [] term_table

let hash_for_level section offset level_table level_hashes level =
  lookup_level_hash section offset level_table level_hashes level

let hash_for_term section offset _name_table term_table term_hashes term =
  lookup_term_hash section offset term_table term_hashes term

let encode_universe_constraint_relation relation =
  match relation with
  | Ext_cert.Le -> byte 0x00
  | Ext_cert.Eq -> byte 0x01

let encode_universe_constraints section offset level_table level_hashes constraints =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length constraints) ^ String.concat "" (List.rev encoded))
    | constraint_ :: rest ->
        bind
          (hash_for_level section offset level_table level_hashes
             constraint_.Ext_cert.constraint_lhs)
          (fun lhs_hash ->
            bind
              (hash_for_level section offset level_table level_hashes
                 constraint_.Ext_cert.constraint_rhs)
              (fun rhs_hash ->
                loop rest
                  ((lhs_hash ^ encode_universe_constraint_relation constraint_.Ext_cert.constraint_relation
                   ^ rhs_hash)
                  :: encoded)))
  in
  loop constraints []

let encode_reducibility reducibility =
  match reducibility with
  | Ext_cert.Reducible -> byte 0x00
  | Ext_cert.Opaque_reducibility -> byte 0x01

let encode_opacity opacity =
  match opacity with
  | Ext_cert.Opaque -> byte 0x00

let encode_option encode value =
  match value with
  | None -> Ok (byte 0x00)
  | Some value -> bind (encode value) (fun encoded -> Ok (byte 0x01 ^ encoded))

let encode_option_hash value =
  encode_option (fun hash -> Ok (encode_hash hash)) value

let encode_option_reducibility value =
  encode_option (fun reducibility -> Ok (encode_reducibility reducibility)) value

let encode_option_opacity value = encode_option (fun opacity -> Ok (encode_opacity opacity)) value

let encode_dependency_entries section offset name_table dependencies =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length dependencies) ^ String.concat "" (List.rev encoded))
    | dependency :: rest ->
        bind
          (encode_global_ref section offset name_table dependency.Ext_cert.dependency_global_ref)
          (fun global_ref ->
            loop rest ((global_ref ^ encode_hash dependency.Ext_cert.dependency_decl_interface_hash) :: encoded))
  in
  loop dependencies []

let encode_axiom_refs section offset name_table axioms =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length axioms) ^ String.concat "" (List.rev encoded))
    | axiom :: rest ->
        bind (encode_global_ref section offset name_table axiom.Ext_cert.axiom_global_ref)
          (fun global_ref ->
            bind (encode_name_id section offset name_table axiom.Ext_cert.axiom_name)
              (fun name ->
                loop rest
                  ((global_ref ^ name ^ encode_hash axiom.Ext_cert.axiom_decl_interface_hash)
                  :: encoded)))
  in
  loop axioms []

let rec collect_global_refs_from_term term refs =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> refs
  | Ext_term.Const (global_ref, _) ->
      if List.exists (( = ) global_ref) refs then refs else global_ref :: refs
  | Ext_term.App (fn, arg) ->
      collect_global_refs_from_term arg (collect_global_refs_from_term fn refs)
  | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
      collect_global_refs_from_term body (collect_global_refs_from_term ty refs)
  | Ext_term.Let (ty, value, body) ->
      collect_global_refs_from_term body
        (collect_global_refs_from_term value (collect_global_refs_from_term ty refs))

let interface_terms payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_ty; _ } -> [ decl_ty ]
  | Ext_cert.DefDecl { decl_ty; decl_value; decl_reducibility; _ } ->
      if decl_reducibility = Ext_cert.Reducible then [ decl_ty; decl_value ] else [ decl_ty ]
  | Ext_cert.TheoremDecl { decl_ty; _ } -> [ decl_ty ]
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

let interface_dependencies_for_decl payload dependencies =
  let refs =
    List.fold_left
      (fun refs term -> collect_global_refs_from_term term refs)
      [] (interface_terms payload)
  in
  List.filter
    (fun dependency -> List.exists (( = ) dependency.Ext_cert.dependency_global_ref) refs)
    dependencies

let encode_binder_type_hashes section offset name_table term_table term_hashes binders =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length binders) ^ String.concat "" (List.rev encoded))
    | binder :: rest ->
        bind
          (hash_for_term section offset name_table term_table term_hashes binder.Ext_cert.binder_ty)
          (fun hash -> loop rest (hash :: encoded))
  in
  loop binders []

let encode_constructor_specs section offset name_table term_table term_hashes constructors =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length constructors) ^ String.concat "" (List.rev encoded))
    | constructor :: rest ->
        bind (encode_name_value section offset name_table constructor.Ext_cert.constructor_name)
          (fun name ->
            bind
              (hash_for_term section offset name_table term_table term_hashes
                 constructor.Ext_cert.constructor_ty)
              (fun ty_hash -> loop rest ((name ^ ty_hash) :: encoded)))
  in
  loop constructors []

let encode_recursor_rules rules =
  encode_uvar rules.Ext_cert.minor_start ^ encode_uvar rules.Ext_cert.major_index

let generated_recursor_signature_payload section offset name_table term_table term_hashes recursor =
  match recursor with
  | None -> Ok (byte 0x00)
  | Some recursor ->
      bind (encode_name_value section offset name_table recursor.Ext_cert.recursor_name)
        (fun name ->
          bind (encode_name_values section offset name_table recursor.Ext_cert.recursor_universe_params)
            (fun universe_params ->
              bind
                (hash_for_term section offset name_table term_table term_hashes
                   recursor.Ext_cert.recursor_ty)
                (fun ty_hash -> Ok (byte 0x01 ^ name ^ universe_params ^ ty_hash))))

let generated_recursor_signature_hash section offset name_table term_table term_hashes recursor =
  bind
    (generated_recursor_signature_payload section offset name_table term_table term_hashes recursor)
    (fun payload -> Ok (hash_with_domain domain_generated_recursor_signature payload))

let generated_computation_rule_payload recursor =
  match recursor with
  | None -> byte 0x00
  | Some recursor -> byte 0x01 ^ encode_recursor_rules recursor.Ext_cert.recursor_rules

let generated_computation_rule_hash recursor =
  hash_with_domain domain_generated_computation_rule (generated_computation_rule_payload recursor)

let encode_mutual_inductive_specs section offset name_table level_table level_hashes term_table
    term_hashes inductives =
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length inductives) ^ String.concat "" (List.rev encoded))
    | inductive :: rest ->
        bind (encode_name_value section offset name_table inductive.Ext_cert.mutual_name)
          (fun name ->
            bind
              (encode_binder_type_hashes section offset name_table term_table term_hashes
                 inductive.Ext_cert.mutual_params)
              (fun params ->
                bind
                  (encode_binder_type_hashes section offset name_table term_table term_hashes
                     inductive.Ext_cert.mutual_indices)
                  (fun indices ->
                    bind
                      (hash_for_level section offset level_table level_hashes
                         inductive.Ext_cert.mutual_sort)
                      (fun sort_hash ->
                        bind
                          (encode_constructor_specs section offset name_table term_table term_hashes
                             inductive.Ext_cert.mutual_constructors)
                          (fun constructors ->
                            bind
                              (generated_recursor_signature_hash section offset name_table
                                 term_table term_hashes inductive.Ext_cert.mutual_recursor)
                              (fun recursor_sig_hash ->
                                let recursor_rule_hash =
                                  generated_computation_rule_hash
                                    inductive.Ext_cert.mutual_recursor
                                in
                                loop rest
                                  ((name ^ params ^ indices ^ sort_hash ^ constructors
                                   ^ recursor_sig_hash ^ recursor_rule_hash)
                                  :: encoded)))))))
  in
  loop inductives []

let declaration_interface_payload name_table level_table term_table payload dependencies
    axiom_dependencies =
  capture (fun () ->
      let table_level_hashes = unwrap (level_hashes level_table) in
      let table_term_hashes = unwrap (term_hashes name_table level_table table_level_hashes term_table) in
      let section = Ext_bytes.Declarations in
      let offset = 0 in
      let name = encode_name_value section offset name_table in
      let names = encode_name_values section offset name_table in
      let term = hash_for_term section offset name_table term_table table_term_hashes in
      let level = hash_for_level section offset level_table table_level_hashes in
      let constraints = encode_universe_constraints section offset level_table table_level_hashes in
      let interface_dependencies = interface_dependencies_for_decl payload dependencies in
      let deps = encode_dependency_entries section offset name_table interface_dependencies in
      let axioms = encode_axiom_refs section offset name_table axiom_dependencies in
      match payload with
      | Ext_cert.AxiomDecl { decl_name; decl_universe_params; decl_universe_constraints = []; decl_ty }
        ->
          byte 0x00 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (term decl_ty) ^ unwrap deps
      | Ext_cert.AxiomDecl { decl_name; decl_universe_params; decl_universe_constraints; decl_ty }
        ->
          byte 0x10 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (constraints decl_universe_constraints) ^ unwrap (term decl_ty) ^ unwrap deps
      | Ext_cert.DefDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints = [];
            decl_ty;
            decl_value;
            decl_reducibility;
          } ->
          byte 0x01 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (term decl_ty) ^ encode_reducibility decl_reducibility ^ unwrap deps
          ^ unwrap axioms
          ^
          if decl_reducibility = Ext_cert.Reducible then unwrap (term decl_value) else ""
      | Ext_cert.DefDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints;
            decl_ty;
            decl_value;
            decl_reducibility;
          } ->
          byte 0x11 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (constraints decl_universe_constraints) ^ unwrap (term decl_ty)
          ^ encode_reducibility decl_reducibility ^ unwrap deps ^ unwrap axioms
          ^
          if decl_reducibility = Ext_cert.Reducible then unwrap (term decl_value) else ""
      | Ext_cert.TheoremDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints = [];
            decl_ty;
            decl_opacity;
            _;
          } ->
          byte 0x02 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (term decl_ty) ^ encode_opacity decl_opacity ^ unwrap deps
          ^ unwrap axioms
      | Ext_cert.TheoremDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints;
            decl_ty;
            decl_opacity;
            _;
          } ->
          byte 0x12 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (constraints decl_universe_constraints) ^ unwrap (term decl_ty)
          ^ encode_opacity decl_opacity ^ unwrap deps ^ unwrap axioms
      | Ext_cert.InductiveDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints = [];
            ind_params;
            ind_indices;
            ind_sort;
            ind_constructors;
            ind_recursor;
          } ->
          byte 0x03 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap
              (encode_binder_type_hashes section offset name_table term_table table_term_hashes
                 ind_params)
          ^ unwrap
              (encode_binder_type_hashes section offset name_table term_table table_term_hashes
                 ind_indices)
          ^ unwrap (level ind_sort)
          ^ unwrap
              (encode_constructor_specs section offset name_table term_table table_term_hashes
                 ind_constructors)
          ^ unwrap
              (generated_recursor_signature_hash section offset name_table term_table table_term_hashes
                 ind_recursor)
          ^ generated_computation_rule_hash ind_recursor ^ unwrap deps ^ unwrap axioms
      | Ext_cert.InductiveDecl
          {
            decl_name;
            decl_universe_params;
            decl_universe_constraints;
            ind_params;
            ind_indices;
            ind_sort;
            ind_constructors;
            ind_recursor;
          } ->
          byte 0x13 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (constraints decl_universe_constraints)
          ^ unwrap
              (encode_binder_type_hashes section offset name_table term_table table_term_hashes
                 ind_params)
          ^ unwrap
              (encode_binder_type_hashes section offset name_table term_table table_term_hashes
                 ind_indices)
          ^ unwrap (level ind_sort)
          ^ unwrap
              (encode_constructor_specs section offset name_table term_table table_term_hashes
                 ind_constructors)
          ^ unwrap
              (generated_recursor_signature_hash section offset name_table term_table table_term_hashes
                 ind_recursor)
          ^ generated_computation_rule_hash ind_recursor ^ unwrap deps ^ unwrap axioms
      | Ext_cert.MutualInductiveBlockDecl
          { decl_name; decl_universe_params; decl_universe_constraints; mutual_inductives } ->
          byte 0x04 ^ unwrap (name decl_name) ^ unwrap (names decl_universe_params)
          ^ unwrap (constraints decl_universe_constraints)
          ^ unwrap
              (encode_mutual_inductive_specs section offset name_table level_table table_level_hashes
                 term_table table_term_hashes mutual_inductives)
          ^ unwrap deps ^ unwrap axioms)

let declaration_certificate_payload name_table level_table term_table payload interface_hash dependencies
    axiom_dependencies =
  bind (level_hashes level_table) (fun table_level_hashes ->
      bind
        (term_hashes name_table level_table table_level_hashes term_table)
        (fun table_term_hashes ->
          let section = Ext_bytes.Declarations in
          let offset = 0 in
          let term = hash_for_term section offset name_table term_table table_term_hashes in
          let deps = encode_dependency_entries section offset name_table dependencies in
          let axioms = encode_axiom_refs section offset name_table axiom_dependencies in
          match payload with
          | Ext_cert.AxiomDecl _ -> bind axioms (fun axioms -> Ok (interface_hash ^ axioms))
          | Ext_cert.DefDecl { decl_value; _ } ->
              bind (term decl_value) (fun value ->
                  bind deps (fun deps ->
                      bind axioms (fun axioms -> Ok (interface_hash ^ value ^ deps ^ axioms))))
          | Ext_cert.TheoremDecl { decl_proof; _ } ->
              bind (term decl_proof) (fun proof ->
                  bind deps (fun deps -> Ok (interface_hash ^ proof ^ deps)))
          | Ext_cert.InductiveDecl _ | Ext_cert.MutualInductiveBlockDecl _ ->
              bind deps (fun deps ->
                  bind axioms (fun axioms -> Ok (interface_hash ^ deps ^ axioms)))))

type declaration_hash_role =
  | Decl_interface_hash
  | Decl_certificate_hash

type declaration_hash_mismatch_kind =
  | Declaration_hash_material_mismatch
  | Dependency_hash_material_mismatch

type declaration_hash_mismatch = {
  mismatch_kind : declaration_hash_mismatch_kind;
  mismatch_role : declaration_hash_role;
  mismatch_decl_index : int;
  mismatch_offset : Ext_bytes.offset;
  expected_hash : string;
  actual_hash : string;
}

type declaration_hash_check_result =
  | Declaration_hashes_ok
  | Declaration_hash_mismatch of declaration_hash_mismatch

let declaration_hash_mismatch_kind_code kind =
  match kind with
  | Declaration_hash_material_mismatch -> "declaration_hash_mismatch"
  | Dependency_hash_material_mismatch -> "dependency_hash_mismatch"

let declaration_hash_role_reason_code role =
  match role with
  | Decl_interface_hash -> "decl_interface_hash_mismatch"
  | Decl_certificate_hash -> "decl_certificate_hash_mismatch"

let declaration_hash_role_offset (declaration : Ext_cert.declaration) role =
  match role with
  | Decl_interface_hash -> declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash_offset
  | Decl_certificate_hash -> declaration.Ext_cert.hashes.Ext_cert.decl_certificate_hash_offset

let declaration_hashes name_table level_table term_table
    (declaration : Ext_cert.declaration) =
  bind
    (declaration_interface_payload name_table level_table term_table declaration.Ext_cert.payload
       declaration.Ext_cert.dependencies declaration.Ext_cert.axiom_dependencies)
    (fun interface_payload ->
      let interface_hash = hash_with_domain domain_decl_interface interface_payload in
      bind
        (declaration_certificate_payload name_table level_table term_table
           declaration.Ext_cert.payload interface_hash declaration.Ext_cert.dependencies
           declaration.Ext_cert.axiom_dependencies)
        (fun certificate_payload ->
          Ok (interface_hash, hash_with_domain domain_decl_certificate certificate_payload)))

let interface_payload_has_dependency_material (declaration : Ext_cert.declaration) =
  interface_dependencies_for_decl declaration.Ext_cert.payload declaration.Ext_cert.dependencies <> []
  ||
  match declaration.Ext_cert.payload with
  | Ext_cert.AxiomDecl _ -> false
  | Ext_cert.DefDecl _ | Ext_cert.TheoremDecl _ | Ext_cert.InductiveDecl _
  | Ext_cert.MutualInductiveBlockDecl _ ->
      declaration.Ext_cert.axiom_dependencies <> []

let certificate_payload_has_dependency_material (declaration : Ext_cert.declaration) =
  match declaration.Ext_cert.payload with
  | Ext_cert.AxiomDecl _ -> declaration.Ext_cert.axiom_dependencies <> []
  | Ext_cert.TheoremDecl _ -> declaration.Ext_cert.dependencies <> []
  | Ext_cert.DefDecl _ | Ext_cert.InductiveDecl _ | Ext_cert.MutualInductiveBlockDecl _ ->
      declaration.Ext_cert.dependencies <> [] || declaration.Ext_cert.axiom_dependencies <> []

let declaration_hash_mismatch_kind (declaration : Ext_cert.declaration) role =
  let has_dependency_material =
    match role with
    | Decl_interface_hash -> interface_payload_has_dependency_material declaration
    | Decl_certificate_hash -> certificate_payload_has_dependency_material declaration
  in
  if has_dependency_material then Dependency_hash_material_mismatch
  else Declaration_hash_material_mismatch

let make_declaration_hash_mismatch decl_index (declaration : Ext_cert.declaration) role
    expected_hash actual_hash =
  {
    mismatch_kind = declaration_hash_mismatch_kind declaration role;
    mismatch_role = role;
    mismatch_decl_index = decl_index;
    mismatch_offset = declaration_hash_role_offset declaration role;
    expected_hash;
    actual_hash;
  }

let verify_declaration_hashes (decoded : Ext_cert.decoded_module) =
  let rec loop index remaining =
    match remaining with
    | [] -> Ok Declaration_hashes_ok
    | declaration :: rest ->
        bind
          (declaration_hashes decoded.Ext_cert.name_table decoded.Ext_cert.level_table
             decoded.Ext_cert.term_table declaration)
          (fun (interface_hash, certificate_hash) ->
            let stored_interface =
              declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
            in
            let stored_certificate =
              declaration.Ext_cert.hashes.Ext_cert.decl_certificate_hash
            in
            if interface_hash <> stored_interface then
              Ok
                (Declaration_hash_mismatch
                   (make_declaration_hash_mismatch index declaration Decl_interface_hash
                      stored_interface interface_hash))
            else if certificate_hash <> stored_certificate then
              Ok
                (Declaration_hash_mismatch
                   (make_declaration_hash_mismatch index declaration Decl_certificate_hash
                      stored_certificate certificate_hash))
            else loop (index + 1) rest)
  in
  loop 0 decoded.Ext_cert.declaration_table

let encode_export_kind kind =
  match kind with
  | Ext_cert.Export_axiom -> byte 0x00
  | Ext_cert.Export_def -> byte 0x01
  | Ext_cert.Export_theorem -> byte 0x02
  | Ext_cert.Export_inductive -> byte 0x03
  | Ext_cert.Export_constructor -> byte 0x04
  | Ext_cert.Export_recursor -> byte 0x05

let encode_usize_vector values =
  encode_uvar (List.length values) ^ String.concat "" (List.map encode_uvar values)

let list_name_ids section offset name_table names =
  let rec loop remaining ids =
    match remaining with
    | [] -> Ok (List.rev ids)
    | name :: rest ->
        bind (name_id section offset name_table name) (fun id -> loop rest (id :: ids))
  in
  loop names []

let encode_option_usize value =
  match value with
  | None -> Ok (byte 0x00)
  | Some value -> Ok (byte 0x01 ^ encode_uvar value)

let encode_export_entries name_table term_table entries =
  let section = Ext_bytes.Export_block in
  let rec loop remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length entries) ^ String.concat "" (List.rev encoded))
    | export :: rest ->
        let offset = export.Ext_cert.export_offset in
        bind (name_id section offset name_table export.Ext_cert.export_name) (fun export_name_id ->
            bind
              (list_name_ids section offset name_table export.Ext_cert.export_universe_params)
              (fun universe_param_ids ->
                bind (term_id section offset term_table export.Ext_cert.export_ty) (fun ty_id ->
                    bind
                      (match export.Ext_cert.export_body with
                      | None -> encode_option_usize None
                      | Some body ->
                          bind (term_id section offset term_table body) (fun body_id ->
                              encode_option_usize (Some body_id)))
                      (fun body ->
                        bind (encode_option_hash export.Ext_cert.export_body_hash) (fun body_hash ->
                            bind (encode_option_reducibility export.Ext_cert.export_reducibility)
                              (fun reducibility ->
                                bind (encode_option_opacity export.Ext_cert.export_opacity)
                                  (fun opacity ->
                                    bind
                                      (encode_axiom_refs section offset name_table
                                         export.Ext_cert.export_axiom_dependencies)
                                      (fun axioms ->
                                        loop rest
                                          ((encode_uvar export_name_id
                                           ^ encode_export_kind export.Ext_cert.export_kind
                                           ^ encode_usize_vector universe_param_ids
                                           ^ encode_uvar ty_id ^ body
                                           ^ encode_hash export.Ext_cert.export_type_hash ^ body_hash
                                           ^ reducibility ^ opacity
                                           ^ encode_hash export.Ext_cert.export_decl_interface_hash
                                          ^ axioms)
                                          :: encoded)))))))))
  in
  loop entries []

let encode_export_block decoded =
  encode_export_entries decoded.Ext_cert.name_table decoded.Ext_cert.term_table
    decoded.Ext_cert.export_block

let export_entry_material_equal lhs rhs =
  Ext_name.equal lhs.Ext_cert.export_name rhs.Ext_cert.export_name
  && lhs.Ext_cert.export_kind = rhs.Ext_cert.export_kind
  && lhs.Ext_cert.export_universe_params = rhs.Ext_cert.export_universe_params
  && lhs.Ext_cert.export_ty = rhs.Ext_cert.export_ty
  && lhs.Ext_cert.export_body = rhs.Ext_cert.export_body
  && lhs.Ext_cert.export_type_hash = rhs.Ext_cert.export_type_hash
  && lhs.Ext_cert.export_body_hash = rhs.Ext_cert.export_body_hash
  && lhs.Ext_cert.export_reducibility = rhs.Ext_cert.export_reducibility
  && lhs.Ext_cert.export_opacity = rhs.Ext_cert.export_opacity
  && lhs.Ext_cert.export_decl_interface_hash = rhs.Ext_cert.export_decl_interface_hash
  && lhs.Ext_cert.export_axiom_dependencies = rhs.Ext_cert.export_axiom_dependencies

let export_block_material_equal lhs rhs =
  let rec loop left right =
    match (left, right) with
    | [], [] -> true
    | left_entry :: left_rest, right_entry :: right_rest ->
        export_entry_material_equal left_entry right_entry && loop left_rest right_rest
    | _ -> false
  in
  loop lhs rhs

let export_name_compare lhs rhs =
  String.compare (Ext_name.to_string lhs.Ext_cert.export_name)
    (Ext_name.to_string rhs.Ext_cert.export_name)

let term_hash_for_export section offset name_table term_table term_hashes term =
  hash_for_term section offset name_table term_table term_hashes term

let inductive_export_type_term params indices sort =
  List.fold_right
    (fun binder body -> Ext_term.Pi (binder.Ext_cert.binder_ty, body))
    (params @ indices) Ext_term.(Sort sort)

let expected_export_entry ~offset ~name ~kind ~universe_params ~ty ~body ~body_hash
    ~reducibility ~opacity ~decl_interface_hash ~axiom_dependencies type_hash =
  {
    Ext_cert.export_name = name;
    export_kind = kind;
    export_universe_params = universe_params;
    export_ty = ty;
    export_body = body;
    export_type_hash = type_hash;
    export_body_hash = body_hash;
    export_reducibility = reducibility;
    export_opacity = opacity;
    export_decl_interface_hash = decl_interface_hash;
    export_axiom_dependencies = axiom_dependencies;
    export_offset = offset;
  }

let expected_export_block (decoded : Ext_cert.decoded_module) =
  bind (level_hashes decoded.Ext_cert.level_table) (fun level_hashes ->
      bind
        (term_hashes decoded.Ext_cert.name_table decoded.Ext_cert.level_table level_hashes
           decoded.Ext_cert.term_table)
        (fun term_hashes ->
          let section = Ext_bytes.Export_block in
          let term_hash offset term =
            term_hash_for_export section offset decoded.Ext_cert.name_table
              decoded.Ext_cert.term_table term_hashes term
          in
          let rec exports_for_declarations
              (declarations : Ext_cert.declaration list) entries =
            match declarations with
            | [] ->
                Ok (List.sort export_name_compare entries)
            | declaration :: rest ->
                let offset = declaration.Ext_cert.offset in
                let decl_interface_hash =
                  declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
                in
                let axiom_dependencies = declaration.Ext_cert.axiom_dependencies in
                let with_term_hash term f =
                  bind (term_hash offset term) (fun type_hash ->
                      f type_hash)
                in
                let add entry = exports_for_declarations rest (entry :: entries) in
                (match declaration.Ext_cert.payload with
                | Ext_cert.AxiomDecl { decl_name; decl_universe_params; decl_ty; _ } ->
                    with_term_hash decl_ty (fun type_hash ->
                        add
                          (expected_export_entry ~offset ~name:decl_name
                             ~kind:Ext_cert.Export_axiom
                             ~universe_params:decl_universe_params ~ty:decl_ty ~body:None
                             ~body_hash:None ~reducibility:None ~opacity:None
                             ~decl_interface_hash ~axiom_dependencies type_hash))
                | Ext_cert.DefDecl
                    {
                      decl_name;
                      decl_universe_params;
                      decl_ty;
                      decl_value;
                      decl_reducibility;
                      _;
                    } ->
                    with_term_hash decl_ty (fun type_hash ->
                        let reducible = decl_reducibility = Ext_cert.Reducible in
                        let body = if reducible then Some decl_value else None in
                        bind
                          (if reducible then
                             bind (term_hash offset decl_value) (fun hash -> Ok (Some hash))
                           else Ok None)
                          (fun body_hash ->
                            add
                              (expected_export_entry ~offset ~name:decl_name
                                 ~kind:Ext_cert.Export_def
                                 ~universe_params:decl_universe_params ~ty:decl_ty ~body
                                 ~body_hash ~reducibility:(Some decl_reducibility)
                                 ~opacity:None ~decl_interface_hash ~axiom_dependencies
                                 type_hash)))
                | Ext_cert.TheoremDecl { decl_name; decl_universe_params; decl_ty; _ } ->
                    with_term_hash decl_ty (fun type_hash ->
                        add
                          (expected_export_entry ~offset ~name:decl_name
                             ~kind:Ext_cert.Export_theorem
                             ~universe_params:decl_universe_params ~ty:decl_ty ~body:None
                             ~body_hash:None ~reducibility:None
                             ~opacity:(Some Ext_cert.Opaque) ~decl_interface_hash
                             ~axiom_dependencies type_hash))
                | Ext_cert.InductiveDecl
                    {
                      decl_name;
                      decl_universe_params;
                      ind_params;
                      ind_indices;
                      ind_sort;
                      ind_constructors;
                      ind_recursor;
                      _;
                    } ->
                    let ind_ty =
                      inductive_export_type_term ind_params ind_indices ind_sort
                    in
                    with_term_hash ind_ty (fun type_hash ->
                        let inductive_entry =
                          expected_export_entry ~offset ~name:decl_name
                            ~kind:Ext_cert.Export_inductive
                            ~universe_params:decl_universe_params ~ty:ind_ty ~body:None
                            ~body_hash:None ~reducibility:None ~opacity:None
                            ~decl_interface_hash ~axiom_dependencies type_hash
                        in
                        let add_constructor entries constructor =
                          bind
                            (term_hash offset constructor.Ext_cert.constructor_ty)
                            (fun constructor_hash ->
                              let constructor_entry =
                                expected_export_entry ~offset
                                  ~name:constructor.Ext_cert.constructor_name
                                  ~kind:Ext_cert.Export_constructor
                                  ~universe_params:decl_universe_params
                                  ~ty:constructor.Ext_cert.constructor_ty ~body:None
                                  ~body_hash:None ~reducibility:None ~opacity:None
                                  ~decl_interface_hash ~axiom_dependencies constructor_hash
                              in
                              Ok (constructor_entry :: entries))
                        in
                        let rec add_constructors constructors entries =
                          match constructors with
                          | [] -> Ok entries
                          | constructor :: rest ->
                              bind (add_constructor entries constructor)
                                (fun entries -> add_constructors rest entries)
                        in
                        bind (add_constructors ind_constructors (inductive_entry :: entries))
                          (fun entries ->
                            match ind_recursor with
                            | None -> exports_for_declarations rest entries
                            | Some recursor ->
                                bind (term_hash offset recursor.Ext_cert.recursor_ty)
                                  (fun recursor_hash ->
                                    let recursor_entry =
                                      expected_export_entry ~offset
                                        ~name:recursor.Ext_cert.recursor_name
                                        ~kind:Ext_cert.Export_recursor
                                        ~universe_params:
                                          recursor.Ext_cert.recursor_universe_params
                                        ~ty:recursor.Ext_cert.recursor_ty ~body:None
                                        ~body_hash:None ~reducibility:None ~opacity:None
                                        ~decl_interface_hash ~axiom_dependencies
                                        recursor_hash
                                    in
                                    exports_for_declarations rest
                                      (recursor_entry :: entries))))
                | Ext_cert.MutualInductiveBlockDecl { decl_universe_params; mutual_inductives; _ }
                  ->
                    let add_inductive entries inductive =
                      let ind_ty =
                        inductive_export_type_term inductive.Ext_cert.mutual_params
                          inductive.Ext_cert.mutual_indices inductive.Ext_cert.mutual_sort
                      in
                      bind (term_hash offset ind_ty) (fun type_hash ->
                          let inductive_entry =
                            expected_export_entry ~offset
                              ~name:inductive.Ext_cert.mutual_name
                              ~kind:Ext_cert.Export_inductive
                              ~universe_params:decl_universe_params ~ty:ind_ty ~body:None
                              ~body_hash:None ~reducibility:None ~opacity:None
                              ~decl_interface_hash ~axiom_dependencies type_hash
                          in
                          let rec add_constructors constructors entries =
                            match constructors with
                            | [] -> Ok entries
                            | constructor :: rest ->
                                bind
                                  (term_hash offset constructor.Ext_cert.constructor_ty)
                                  (fun constructor_hash ->
                                    let constructor_entry =
                                      expected_export_entry ~offset
                                        ~name:constructor.Ext_cert.constructor_name
                                        ~kind:Ext_cert.Export_constructor
                                        ~universe_params:decl_universe_params
                                        ~ty:constructor.Ext_cert.constructor_ty ~body:None
                                        ~body_hash:None ~reducibility:None ~opacity:None
                                        ~decl_interface_hash ~axiom_dependencies
                                        constructor_hash
                                    in
                                    add_constructors rest (constructor_entry :: entries))
                          in
                          bind
                            (add_constructors inductive.Ext_cert.mutual_constructors
                               (inductive_entry :: entries))
                            (fun entries ->
                              match inductive.Ext_cert.mutual_recursor with
                              | None -> Ok entries
                              | Some recursor ->
                                  bind (term_hash offset recursor.Ext_cert.recursor_ty)
                                    (fun recursor_hash ->
                                      let recursor_entry =
                                        expected_export_entry ~offset
                                          ~name:recursor.Ext_cert.recursor_name
                                          ~kind:Ext_cert.Export_recursor
                                          ~universe_params:
                                            recursor.Ext_cert.recursor_universe_params
                                          ~ty:recursor.Ext_cert.recursor_ty ~body:None
                                          ~body_hash:None ~reducibility:None ~opacity:None
                                          ~decl_interface_hash ~axiom_dependencies
                                          recursor_hash
                                      in
                                      Ok (recursor_entry :: entries))))
                    in
                    let rec add_inductives inductives entries =
                      match inductives with
                      | [] -> exports_for_declarations rest entries
                      | inductive :: rest_inductives ->
                          bind (add_inductive entries inductive) (fun entries ->
                              add_inductives rest_inductives entries)
                    in
                    add_inductives mutual_inductives entries)
          in
          exports_for_declarations decoded.Ext_cert.declaration_table []))

let encode_axiom_report name_table report =
  let section = Ext_bytes.Axiom_report in
  let rec encode_decl_reports remaining encoded =
    match remaining with
    | [] -> Ok (encode_uvar (List.length report.Ext_cert.per_declaration) ^ String.concat "" (List.rev encoded))
    | entry :: rest ->
        let offset = entry.Ext_cert.report_offset in
        bind (encode_axiom_refs section offset name_table entry.Ext_cert.report_direct_axioms)
          (fun direct ->
            bind (encode_axiom_refs section offset name_table entry.Ext_cert.report_transitive_axioms)
              (fun transitive ->
                encode_decl_reports rest
                  ((encode_uvar entry.Ext_cert.report_decl_index ^ direct ^ transitive) :: encoded)))
  in
  bind (encode_decl_reports report.Ext_cert.per_declaration []) (fun per_declaration ->
      bind
        (encode_axiom_refs section report.Ext_cert.module_axioms_offset name_table
           report.Ext_cert.module_axioms)
        (fun module_axioms ->
          let core_features =
            match report.Ext_cert.core_features with
            | [] -> ""
            | features ->
                encode_string Ext_cert.core_feature_report_tag
                ^ encode_uvar (List.length features)
                ^ String.concat ""
                    (List.map
                       (fun feature -> encode_string feature.Ext_feature.feature)
                       features)
          in
          Ok (per_declaration ^ module_axioms ^ core_features)))

let export_hash decoded =
  bind (encode_export_block decoded) (fun payload -> Ok (hash_with_domain domain_module_export payload))

let expected_export_hash decoded =
  bind (expected_export_block decoded) (fun entries ->
      bind (encode_export_entries decoded.Ext_cert.name_table decoded.Ext_cert.term_table entries)
        (fun payload -> Ok (hash_with_domain domain_module_export payload)))

let axiom_report_hash decoded =
  bind (encode_axiom_report decoded.Ext_cert.name_table decoded.Ext_cert.axiom_report) (fun payload ->
      Ok (hash_with_domain domain_axiom_report payload))

let certificate_hash certificate_bytes (decoded : Ext_cert.decoded_module) =
  let offset = decoded.Ext_cert.hashes.Ext_cert.certificate_hash_offset in
  if offset < 0 || offset > String.length certificate_bytes then
    error Ext_bytes.Hashes offset Ext_bytes.Unexpected_eof
  else
    Ok
      (hash_with_domain domain_module_certificate
         (String.sub certificate_bytes 0 offset))

type module_hash_role =
  | Export_hash
  | Axiom_report_hash
  | Certificate_hash

type module_hash_mismatch = {
  module_mismatch_role : module_hash_role;
  module_mismatch_offset : Ext_bytes.offset;
  module_expected_hash : string;
  module_actual_hash : string;
}

type module_hash_check_result =
  | Module_hashes_ok
  | Module_hash_mismatch of module_hash_mismatch

let module_hash_role_kind_code role =
  match role with
  | Export_hash -> "export_hash_mismatch"
  | Axiom_report_hash -> "axiom_report_mismatch"
  | Certificate_hash -> "certificate_hash_mismatch"

let module_hash_role_offset (decoded : Ext_cert.decoded_module) role =
  match role with
  | Export_hash -> decoded.Ext_cert.hashes.Ext_cert.export_hash_offset
  | Axiom_report_hash -> decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash_offset
  | Certificate_hash -> decoded.Ext_cert.hashes.Ext_cert.certificate_hash_offset

let make_module_hash_mismatch decoded role expected_hash actual_hash =
  {
    module_mismatch_role = role;
    module_mismatch_offset = module_hash_role_offset decoded role;
    module_expected_hash = expected_hash;
    module_actual_hash = actual_hash;
  }

let verify_module_hashes certificate_bytes (decoded : Ext_cert.decoded_module) =
  bind (expected_export_block decoded) (fun expected_exports ->
      bind
        (encode_export_entries decoded.Ext_cert.name_table decoded.Ext_cert.term_table
           expected_exports)
        (fun expected_export_payload ->
          let expected_export_hash =
            hash_with_domain domain_module_export expected_export_payload
          in
          let stored_export_hash = decoded.Ext_cert.hashes.Ext_cert.export_hash in
          if
            (not (export_block_material_equal expected_exports decoded.Ext_cert.export_block))
            || expected_export_hash <> stored_export_hash
          then
            Ok
              (Module_hash_mismatch
                 (make_module_hash_mismatch decoded Export_hash stored_export_hash
                    expected_export_hash))
          else
            bind (axiom_report_hash decoded) (fun expected_axiom_hash ->
                let stored_axiom_hash =
                  decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash
                in
                if expected_axiom_hash <> stored_axiom_hash then
                  Ok
                    (Module_hash_mismatch
                       (make_module_hash_mismatch decoded Axiom_report_hash
                          stored_axiom_hash expected_axiom_hash))
                else
                  bind (certificate_hash certificate_bytes decoded)
                    (fun expected_certificate_hash ->
                      let stored_certificate_hash =
                        decoded.Ext_cert.hashes.Ext_cert.certificate_hash
                      in
                      if expected_certificate_hash <> stored_certificate_hash then
                        Ok
                          (Module_hash_mismatch
                             (make_module_hash_mismatch decoded Certificate_hash
                                stored_certificate_hash expected_certificate_hash))
                      else Ok Module_hashes_ok))))
