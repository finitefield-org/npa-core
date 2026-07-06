type hash = string

type declaration_kind =
  | Axiom
  | Definition
  | Theorem
  | Inductive
  | Mutual_inductive

type reducibility =
  | Reducible
  | Opaque_reducibility

type opacity = Opaque

type universe_constraint_relation =
  | Le
  | Eq

type universe_constraint = {
  constraint_lhs : Ext_level.t;
  constraint_relation : universe_constraint_relation;
  constraint_rhs : Ext_level.t;
}

type binder_type = { binder_ty : Ext_term.t }

type constructor_spec = {
  constructor_name : Ext_name.t;
  constructor_ty : Ext_term.t;
}

type recursor_rules = {
  minor_start : int;
  major_index : int;
}

type recursor_spec = {
  recursor_name : Ext_name.t;
  recursor_universe_params : Ext_name.t list;
  recursor_ty : Ext_term.t;
  recursor_rules : recursor_rules;
}

type mutual_inductive_spec = {
  mutual_name : Ext_name.t;
  mutual_params : binder_type list;
  mutual_indices : binder_type list;
  mutual_sort : Ext_level.t;
  mutual_constructors : constructor_spec list;
  mutual_recursor : recursor_spec option;
}

type decl_payload =
  | AxiomDecl of {
      decl_name : Ext_name.t;
      decl_universe_params : Ext_name.t list;
      decl_universe_constraints : universe_constraint list;
      decl_ty : Ext_term.t;
    }
  | DefDecl of {
      decl_name : Ext_name.t;
      decl_universe_params : Ext_name.t list;
      decl_universe_constraints : universe_constraint list;
      decl_ty : Ext_term.t;
      decl_value : Ext_term.t;
      decl_reducibility : reducibility;
    }
  | TheoremDecl of {
      decl_name : Ext_name.t;
      decl_universe_params : Ext_name.t list;
      decl_universe_constraints : universe_constraint list;
      decl_ty : Ext_term.t;
      decl_proof : Ext_term.t;
      decl_opacity : opacity;
    }
  | InductiveDecl of {
      decl_name : Ext_name.t;
      decl_universe_params : Ext_name.t list;
      decl_universe_constraints : universe_constraint list;
      ind_params : binder_type list;
      ind_indices : binder_type list;
      ind_sort : Ext_level.t;
      ind_constructors : constructor_spec list;
      ind_recursor : recursor_spec option;
    }
  | MutualInductiveBlockDecl of {
      decl_name : Ext_name.t;
      decl_universe_params : Ext_name.t list;
      decl_universe_constraints : universe_constraint list;
      mutual_inductives : mutual_inductive_spec list;
    }

type dependency_entry = {
  dependency_global_ref : Ext_term.global_ref;
  dependency_decl_interface_hash : hash;
}

type axiom_ref = {
  axiom_global_ref : Ext_term.global_ref;
  axiom_name : Ext_name.t;
  axiom_decl_interface_hash : hash;
}

type decl_hashes = {
  decl_interface_hash : hash;
  decl_certificate_hash : hash;
  decl_interface_hash_offset : Ext_bytes.offset;
  decl_certificate_hash_offset : Ext_bytes.offset;
}

type declaration = {
  name : Ext_name.t;
  kind : declaration_kind;
  payload : decl_payload;
  dependencies : dependency_entry list;
  axiom_dependencies : axiom_ref list;
  hashes : decl_hashes;
  offset : Ext_bytes.offset;
}

type t = {
  module_name : Ext_name.t option;
  declarations : declaration list;
}

let empty = { module_name = None; declarations = [] }

type header = {
  format : string;
  core_spec : string;
  module_name : Ext_name.t;
}

type located_name = {
  name : Ext_name.t;
  offset : Ext_bytes.offset;
}

type located_import = {
  import_entry : Ext_import.entry;
  import_offset : Ext_bytes.offset;
}

type export_kind =
  | Export_axiom
  | Export_def
  | Export_theorem
  | Export_inductive
  | Export_constructor
  | Export_recursor

type export_entry = {
  export_name : Ext_name.t;
  export_kind : export_kind;
  export_universe_params : Ext_name.t list;
  export_ty : Ext_term.t;
  export_body : Ext_term.t option;
  export_type_hash : hash;
  export_body_hash : hash option;
  export_reducibility : reducibility option;
  export_opacity : opacity option;
  export_decl_interface_hash : hash;
  export_axiom_dependencies : axiom_ref list;
  export_offset : Ext_bytes.offset;
}

type decl_axiom_report = {
  report_decl_index : int;
  report_direct_axioms : axiom_ref list;
  report_transitive_axioms : axiom_ref list;
  report_offset : Ext_bytes.offset;
}

type axiom_report = {
  per_declaration : decl_axiom_report list;
  module_axioms : axiom_ref list;
  module_axioms_offset : Ext_bytes.offset;
  core_features : Ext_feature.feature_report_entry list;
  core_features_offset : Ext_bytes.offset option;
}

type module_hashes = {
  export_hash : hash;
  axiom_report_hash : hash;
  certificate_hash : hash;
  export_hash_offset : Ext_bytes.offset;
  axiom_report_hash_offset : Ext_bytes.offset;
  certificate_hash_offset : Ext_bytes.offset;
}

type decoded_module = {
  header : header;
  imports : located_import list;
  name_table : located_name list;
  level_table : Ext_level.located list;
  term_table : Ext_term.located list;
  declaration_table : declaration list;
  export_block : export_entry list;
  axiom_report : axiom_report;
  hashes : module_hashes;
}

let expected_format = "NPA-CERT-0.1"

let expected_core_spec = "NPA-Core-0.1"

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let find_dot_offset component =
  let rec loop index =
    if index >= String.length component then None
    else if component.[index] = '.' then Some index
    else loop (index + 1)
  in
  loop 0

let read_hash section reader = Ext_bytes.take section 32 reader

let read_vector section read_item reader =
  match Ext_bytes.read_usize section reader with
  | Error err -> Error err
  | Ok (count, after_count) ->
      if count > Ext_bytes.remaining after_count then
        Ext_bytes.error section (Ext_bytes.offset after_count) Ext_bytes.Unexpected_eof
      else
        let rec loop remaining current decoded =
          if remaining = 0 then Ok (List.rev decoded, current)
          else
            match read_item current with
            | Error err -> Error err
            | Ok (value, next) -> loop (remaining - 1) next (value :: decoded)
        in
        loop count after_count []

let read_option section read_value reader =
  let tag_offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte section reader with
  | Error err -> Error err
  | Ok (tag, after_tag) -> (
      match tag with
      | 0x00 -> Ok (None, after_tag)
      | 0x01 ->
          bind (read_value after_tag) (fun (value, next) -> Ok (Some value, next))
      | tag -> Ext_bytes.error section tag_offset (Ext_bytes.Unknown_tag tag))

let names_array names = Array.of_list (List.map (fun entry -> entry.name) names)

let name_values names = List.map (fun entry -> entry.name) names

let name_at section names id offset =
  if id < 0 || id >= Array.length names then
    Ext_bytes.error section offset Ext_bytes.Dangling_reference
  else Ok names.(id)

let level_at section levels id offset =
  if id < 0 || id >= Array.length levels then
    Ext_bytes.error section offset Ext_bytes.Dangling_reference
  else Ok levels.(id).Ext_level.level

let term_at section terms id offset =
  if id < 0 || id >= Array.length terms then
    Ext_bytes.error section offset Ext_bytes.Dangling_reference
  else Ok terms.(id).Ext_term.term

let read_name_ref section names reader =
  let offset = Ext_bytes.offset reader in
  bind (Ext_bytes.read_usize section reader) (fun (id, next) ->
      bind (name_at section names id offset) (fun name -> Ok (name, next)))

let read_level_ref section levels reader =
  let offset = Ext_bytes.offset reader in
  bind (Ext_bytes.read_usize section reader) (fun (id, next) ->
      bind (level_at section levels id offset) (fun level -> Ok (level, next)))

let read_term_ref section terms reader =
  let offset = Ext_bytes.offset reader in
  bind (Ext_bytes.read_usize section reader) (fun (id, next) ->
      bind (term_at section terms id offset) (fun term -> Ok (term, next)))

let read_name_vec section names reader =
  read_vector section (read_name_ref section names) reader

let validate_global_ref section import_count declaration_count offset global_ref =
  match global_ref with
  | Ext_term.Imported { import_index; _ } ->
      if import_index >= import_count then
        Ext_bytes.error section offset Ext_bytes.Dangling_reference
      else Ok ()
  | Ext_term.Local { decl_index }
  | Ext_term.LocalGenerated { decl_index; _ } ->
      if decl_index >= declaration_count then
        Ext_bytes.error section offset Ext_bytes.Dangling_reference
      else Ok ()
  | Ext_term.Builtin _ -> Ok ()

let read_global_ref section import_count declaration_count names reader =
  let offset = Ext_bytes.offset reader in
  bind (Ext_term.read_global_ref section names offset reader) (fun (global_ref, next) ->
      bind
        (validate_global_ref section import_count declaration_count offset global_ref)
        (fun () -> Ok (global_ref, next)))

let rec validate_term_global_refs section import_count declaration_count offset term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> Ok ()
  | Ext_term.Const (global_ref, _) ->
      validate_global_ref section import_count declaration_count offset global_ref
  | Ext_term.App (fn, arg) ->
      bind (validate_term_global_refs section import_count declaration_count offset fn)
        (fun () -> validate_term_global_refs section import_count declaration_count offset arg)
  | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
      bind (validate_term_global_refs section import_count declaration_count offset ty)
        (fun () -> validate_term_global_refs section import_count declaration_count offset body)
  | Ext_term.Let (ty, value, body) ->
      bind (validate_term_global_refs section import_count declaration_count offset ty)
        (fun () ->
          bind (validate_term_global_refs section import_count declaration_count offset value)
            (fun () ->
              validate_term_global_refs section import_count declaration_count offset body))

let read_reducibility section reader =
  let offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte section reader with
  | Error err -> Error err
  | Ok (tag, next) -> (
      match tag with
      | 0x00 -> Ok (Reducible, next)
      | 0x01 -> Ok (Opaque_reducibility, next)
      | tag -> Ext_bytes.error section offset (Ext_bytes.Unknown_tag tag))

let read_opacity section reader =
  let offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte section reader with
  | Error err -> Error err
  | Ok (tag, next) -> (
      match tag with
      | 0x00 -> Ok (Opaque, next)
      | tag -> Ext_bytes.error section offset (Ext_bytes.Unknown_tag tag))

let read_universe_constraints levels reader =
  let read_constraint current =
    bind (read_level_ref Ext_bytes.Declarations levels current) (fun (lhs, after_lhs) ->
        let relation_offset = Ext_bytes.offset after_lhs in
        match Ext_bytes.read_byte Ext_bytes.Declarations after_lhs with
        | Error err -> Error err
        | Ok (relation_tag, after_relation) -> (
            let relation =
              match relation_tag with
              | 0x00 -> Ok Le
              | 0x01 -> Ok Eq
              | tag ->
                  Ext_bytes.error Ext_bytes.Declarations relation_offset
                    (Ext_bytes.Unknown_tag tag)
            in
            bind relation (fun constraint_relation ->
                bind (read_level_ref Ext_bytes.Declarations levels after_relation)
                  (fun (rhs, next) ->
                    Ok ({ constraint_lhs = lhs; constraint_relation; constraint_rhs = rhs }, next)))))
  in
  read_vector Ext_bytes.Declarations read_constraint reader

let read_binder_types terms reader =
  read_vector Ext_bytes.Declarations
    (fun current ->
      bind (read_term_ref Ext_bytes.Declarations terms current) (fun (ty, next) ->
          Ok ({ binder_ty = ty }, next)))
    reader

let read_constructor_specs names terms reader =
  read_vector Ext_bytes.Declarations
    (fun current ->
      bind (read_name_ref Ext_bytes.Declarations names current) (fun (constructor_name, after_name) ->
          bind (read_term_ref Ext_bytes.Declarations terms after_name)
            (fun (constructor_ty, next) -> Ok ({ constructor_name; constructor_ty }, next))))
    reader

let read_recursor_spec names terms reader =
  let recursor_offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte Ext_bytes.Declarations reader with
  | Error err -> Error err
  | Ok (tag, after_tag) -> (
      match tag with
      | 0x00 -> Ok (None, after_tag)
      | 0x01 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (recursor_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (recursor_universe_params, after_params) ->
                  bind (read_term_ref Ext_bytes.Declarations terms after_params)
                    (fun (recursor_ty, after_ty) ->
                      bind (Ext_bytes.read_usize Ext_bytes.Declarations after_ty)
                        (fun (minor_start, after_minor) ->
                          bind (Ext_bytes.read_usize Ext_bytes.Declarations after_minor)
                            (fun (major_index, next) ->
                              let recursor_rules = { minor_start; major_index } in
                              Ok
                                ( Some
                                    {
                                      recursor_name;
                                      recursor_universe_params;
                                      recursor_ty;
                                      recursor_rules;
                                    },
                                  next ))))))
      | tag ->
          Ext_bytes.error Ext_bytes.Declarations recursor_offset (Ext_bytes.Unknown_tag tag))

let read_mutual_inductive_spec names levels terms reader =
  bind (read_name_ref Ext_bytes.Declarations names reader) (fun (mutual_name, after_name) ->
      bind (read_binder_types terms after_name) (fun (mutual_params, after_params) ->
          bind (read_binder_types terms after_params) (fun (mutual_indices, after_indices) ->
              bind (read_level_ref Ext_bytes.Declarations levels after_indices)
                (fun (mutual_sort, after_sort) ->
                  bind (read_constructor_specs names terms after_sort)
                    (fun (mutual_constructors, after_constructors) ->
                      bind (read_recursor_spec names terms after_constructors)
                        (fun (mutual_recursor, next) ->
                          Ok
                            ( {
                                mutual_name;
                                mutual_params;
                                mutual_indices;
                                mutual_sort;
                                mutual_constructors;
                                mutual_recursor;
                              },
                              next )))))))

let read_decl_payload names levels terms reader =
  let offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte Ext_bytes.Declarations reader with
  | Error err -> Error err
  | Ok (tag, after_tag) -> (
      let no_constraints = [] in
      match tag with
      | 0x00 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_term_ref Ext_bytes.Declarations terms after_params)
                    (fun (decl_ty, next) ->
                      Ok
                        ( AxiomDecl
                            {
                              decl_name;
                              decl_universe_params;
                              decl_universe_constraints = no_constraints;
                              decl_ty;
                            },
                          next ))))
      | 0x10 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_universe_constraints levels after_params)
                    (fun (decl_universe_constraints, after_constraints) ->
                      bind (read_term_ref Ext_bytes.Declarations terms after_constraints)
                        (fun (decl_ty, next) ->
                          Ok
                            ( AxiomDecl
                                {
                                  decl_name;
                                  decl_universe_params;
                                  decl_universe_constraints;
                                  decl_ty;
                                },
                              next )))))
      | 0x01 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_term_ref Ext_bytes.Declarations terms after_params)
                    (fun (decl_ty, after_ty) ->
                      bind (read_term_ref Ext_bytes.Declarations terms after_ty)
                        (fun (decl_value, after_value) ->
                          bind (read_reducibility Ext_bytes.Declarations after_value)
                            (fun (decl_reducibility, next) ->
                              Ok
                                ( DefDecl
                                    {
                                      decl_name;
                                      decl_universe_params;
                                      decl_universe_constraints = no_constraints;
                                      decl_ty;
                                      decl_value;
                                      decl_reducibility;
                                    },
                                  next ))))))
      | 0x11 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_universe_constraints levels after_params)
                    (fun (decl_universe_constraints, after_constraints) ->
                      bind (read_term_ref Ext_bytes.Declarations terms after_constraints)
                        (fun (decl_ty, after_ty) ->
                          bind (read_term_ref Ext_bytes.Declarations terms after_ty)
                            (fun (decl_value, after_value) ->
                              bind (read_reducibility Ext_bytes.Declarations after_value)
                                (fun (decl_reducibility, next) ->
                                  Ok
                                    ( DefDecl
                                        {
                                          decl_name;
                                          decl_universe_params;
                                          decl_universe_constraints;
                                          decl_ty;
                                          decl_value;
                                          decl_reducibility;
                                        },
                                      next )))))))
      | 0x02 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_term_ref Ext_bytes.Declarations terms after_params)
                    (fun (decl_ty, after_ty) ->
                      bind (read_term_ref Ext_bytes.Declarations terms after_ty)
                        (fun (decl_proof, after_proof) ->
                          bind (read_opacity Ext_bytes.Declarations after_proof)
                            (fun (decl_opacity, next) ->
                              Ok
                                ( TheoremDecl
                                    {
                                      decl_name;
                                      decl_universe_params;
                                      decl_universe_constraints = no_constraints;
                                      decl_ty;
                                      decl_proof;
                                      decl_opacity;
                                    },
                                  next ))))))
      | 0x12 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_universe_constraints levels after_params)
                    (fun (decl_universe_constraints, after_constraints) ->
                      bind (read_term_ref Ext_bytes.Declarations terms after_constraints)
                        (fun (decl_ty, after_ty) ->
                          bind (read_term_ref Ext_bytes.Declarations terms after_ty)
                            (fun (decl_proof, after_proof) ->
                              bind (read_opacity Ext_bytes.Declarations after_proof)
                                (fun (decl_opacity, next) ->
                                  Ok
                                    ( TheoremDecl
                                        {
                                          decl_name;
                                          decl_universe_params;
                                          decl_universe_constraints;
                                          decl_ty;
                                          decl_proof;
                                          decl_opacity;
                                        },
                                      next )))))))
      | 0x03 | 0x13 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  let constraints_result =
                    if tag = 0x13 then read_universe_constraints levels after_params
                    else Ok (no_constraints, after_params)
                  in
                  bind constraints_result (fun (decl_universe_constraints, after_constraints) ->
                      bind (read_binder_types terms after_constraints)
                        (fun (ind_params, after_params_tys) ->
                          bind (read_binder_types terms after_params_tys)
                            (fun (ind_indices, after_indices) ->
                              bind (read_level_ref Ext_bytes.Declarations levels after_indices)
                                (fun (ind_sort, after_sort) ->
                                  bind (read_constructor_specs names terms after_sort)
                                    (fun (ind_constructors, after_constructors) ->
                                      bind (read_recursor_spec names terms after_constructors)
                                        (fun (ind_recursor, next) ->
                                          Ok
                                            ( InductiveDecl
                                                {
                                                  decl_name;
                                                  decl_universe_params;
                                                  decl_universe_constraints;
                                                  ind_params;
                                                  ind_indices;
                                                  ind_sort;
                                                  ind_constructors;
                                                  ind_recursor;
                                                },
                                              next )))))))))
      | 0x04 ->
          bind (read_name_ref Ext_bytes.Declarations names after_tag)
            (fun (decl_name, after_name) ->
              bind (read_name_vec Ext_bytes.Declarations names after_name)
                (fun (decl_universe_params, after_params) ->
                  bind (read_universe_constraints levels after_params)
                    (fun (decl_universe_constraints, after_constraints) ->
                      bind
                        (read_vector Ext_bytes.Declarations
                           (read_mutual_inductive_spec names levels terms)
                           after_constraints)
                        (fun (mutual_inductives, next) ->
                          Ok
                            ( MutualInductiveBlockDecl
                                {
                                  decl_name;
                                  decl_universe_params;
                                  decl_universe_constraints;
                                  mutual_inductives;
                                },
                              next )))))
      | tag -> Ext_bytes.error Ext_bytes.Declarations offset (Ext_bytes.Unknown_tag tag))

let decl_payload_name payload =
  match payload with
  | AxiomDecl { decl_name; _ }
  | DefDecl { decl_name; _ }
  | TheoremDecl { decl_name; _ }
  | InductiveDecl { decl_name; _ }
  | MutualInductiveBlockDecl { decl_name; _ } ->
      decl_name

let decl_payload_kind payload =
  match payload with
  | AxiomDecl _ -> Axiom
  | DefDecl _ -> Definition
  | TheoremDecl _ -> Theorem
  | InductiveDecl _ -> Inductive
  | MutualInductiveBlockDecl _ -> Mutual_inductive

let read_dependency_entries section import_count declaration_count names reader =
  read_vector section
    (fun current ->
      bind (read_global_ref section import_count declaration_count names current)
        (fun (dependency_global_ref, after_ref) ->
          bind (read_hash section after_ref)
            (fun (dependency_decl_interface_hash, next) ->
              Ok ({ dependency_global_ref; dependency_decl_interface_hash }, next))))
    reader

let read_axiom_refs section import_count declaration_count names reader =
  read_vector section
    (fun current ->
      bind (read_global_ref section import_count declaration_count names current)
        (fun (axiom_global_ref, after_ref) ->
          bind (read_name_ref section names after_ref) (fun (axiom_name, after_name) ->
              bind (read_hash section after_name) (fun (axiom_decl_interface_hash, next) ->
                  Ok ({ axiom_global_ref; axiom_name; axiom_decl_interface_hash }, next)))))
    reader

let read_declarations import_count names levels terms reader =
  match Ext_bytes.read_usize Ext_bytes.Declarations reader with
  | Error err -> Error err
  | Ok (declaration_count, after_count) ->
      if declaration_count > Ext_bytes.remaining after_count then
        Ext_bytes.error Ext_bytes.Declarations (Ext_bytes.offset after_count)
          Ext_bytes.Unexpected_eof
      else
        let name_values = Array.of_list names in
        let level_values = Array.of_list levels in
        let term_values = Array.of_list terms in
        let rec loop remaining current seen decoded =
          if remaining = 0 then Ok (List.rev decoded, current)
          else
            let offset = Ext_bytes.offset current in
            bind (read_decl_payload name_values level_values term_values current)
              (fun (payload, after_payload) ->
                let name = decl_payload_name payload in
                if List.exists (Ext_name.equal name) seen then
                  Ext_bytes.error Ext_bytes.Declarations offset Ext_bytes.Duplicate_declaration
                else
                  bind
                    (read_dependency_entries Ext_bytes.Declarations import_count declaration_count
                       name_values after_payload)
                    (fun (dependencies, after_dependencies) ->
                      bind
                        (read_axiom_refs Ext_bytes.Declarations import_count declaration_count
                           name_values after_dependencies)
                        (fun (axiom_dependencies, after_axioms) ->
                          let decl_interface_hash_offset = Ext_bytes.offset after_axioms in
                          bind (read_hash Ext_bytes.Declarations after_axioms)
                            (fun (decl_interface_hash, after_interface_hash) ->
                              let decl_certificate_hash_offset =
                                Ext_bytes.offset after_interface_hash
                              in
                              bind (read_hash Ext_bytes.Declarations after_interface_hash)
                                (fun (decl_certificate_hash, next) ->
                                  let hashes =
                                    {
                                      decl_interface_hash;
                                      decl_certificate_hash;
                                      decl_interface_hash_offset;
                                      decl_certificate_hash_offset;
                                    }
                                  in
                                  let declaration =
                                    {
                                      name;
                                      kind = decl_payload_kind payload;
                                      payload;
                                      dependencies;
                                      axiom_dependencies;
                                      hashes;
                                      offset;
                                    }
                                  in
                                  loop (remaining - 1) next (name :: seen)
                                    (declaration :: decoded))))))
        in
        loop declaration_count after_count [] []

let read_name section reader =
  let name_offset = Ext_bytes.offset reader in
  match Ext_bytes.read_usize section reader with
  | Error err -> Error err
  | Ok (component_count, after_count) ->
      if component_count = 0 then Ext_bytes.error section name_offset Ext_bytes.Empty_name
      else
        let rec loop remaining current components =
          if remaining = 0 then
            match Ext_name.of_components (List.rev components) with
            | None -> Ext_bytes.error section name_offset Ext_bytes.Empty_name
            | Some name -> Ok (name, current)
          else
            let component_offset = Ext_bytes.offset current in
            match Ext_bytes.read_string_with_offset section current with
            | Error err -> Error err
            | Ok ((component, component_content_offset), next) ->
                if component = "" then
                  Ext_bytes.error section component_offset Ext_bytes.Empty_name_component
	                else (
	                  match find_dot_offset component with
	                  | Some dot_offset ->
	                      Ext_bytes.error section (component_content_offset + dot_offset)
	                        Ext_bytes.Dotted_name_component
	                  | None ->
	                      if not (Ext_name.is_component component) then
	                        Ext_bytes.error section component_content_offset
	                          Ext_bytes.Invalid_name_component
	                      else loop (remaining - 1) next (component :: components))
	        in
	        loop component_count after_count []

let read_header reader =
  match Ext_bytes.read_string Ext_bytes.Header_format reader with
  | Error err -> Error err
  | Ok (format, after_format) ->
      if format <> expected_format then
        Ext_bytes.error Ext_bytes.Header_format (Ext_bytes.offset after_format)
          Ext_bytes.Format_mismatch
      else (
        match Ext_bytes.read_string Ext_bytes.Header_core_spec after_format with
        | Error err -> Error err
        | Ok (core_spec, after_core_spec) ->
            if core_spec <> expected_core_spec then
              Ext_bytes.error Ext_bytes.Header_core_spec (Ext_bytes.offset after_core_spec)
                Ext_bytes.Core_spec_mismatch
            else (
              match read_name Ext_bytes.Header_module after_core_spec with
              | Error err -> Error err
              | Ok (module_name, next) -> Ok ({ format; core_spec; module_name }, next)))

let read_imports reader =
  read_vector Ext_bytes.Imports
    (fun current ->
      let import_offset = Ext_bytes.offset current in
      bind (read_name Ext_bytes.Imports current) (fun (module_name, after_name) ->
          bind (read_hash Ext_bytes.Imports after_name) (fun (export_hash, after_export_hash) ->
              bind
                (read_option Ext_bytes.Imports (read_hash Ext_bytes.Imports) after_export_hash)
                (fun (certificate_hash, next) ->
                  Ok ({ import_entry = { module_name; export_hash; certificate_hash }; import_offset }, next)))))
    reader

let read_name_table reader =
  match Ext_bytes.read_usize Ext_bytes.Name_table reader with
  | Error err -> Error err
  | Ok (name_count, after_count) ->
      let rec loop remaining current names =
        if remaining = 0 then Ok (List.rev names, current)
        else
          let entry_offset = Ext_bytes.offset current in
          match read_name Ext_bytes.Name_table current with
          | Error err -> Error err
          | Ok (name, next) ->
              if List.exists (fun entry -> Ext_name.equal entry.name name) names then
                Ext_bytes.error Ext_bytes.Name_table entry_offset Ext_bytes.Duplicate_name
              else loop (remaining - 1) next ({ name; offset = entry_offset } :: names)
      in
      loop name_count after_count []

let read_option_term section terms reader =
  read_option section (read_term_ref section terms) reader

let read_export_kind reader =
  let offset = Ext_bytes.offset reader in
  match Ext_bytes.read_byte Ext_bytes.Export_block reader with
  | Error err -> Error err
  | Ok (tag, next) -> (
      match tag with
      | 0x00 -> Ok (Export_axiom, next)
      | 0x01 -> Ok (Export_def, next)
      | 0x02 -> Ok (Export_theorem, next)
      | 0x03 -> Ok (Export_inductive, next)
      | 0x04 -> Ok (Export_constructor, next)
      | 0x05 -> Ok (Export_recursor, next)
      | tag -> Ext_bytes.error Ext_bytes.Export_block offset (Ext_bytes.Unknown_tag tag))

let read_export_block import_count names terms declaration_count reader =
  read_vector Ext_bytes.Export_block
    (fun current ->
      let export_offset = Ext_bytes.offset current in
      bind (read_name_ref Ext_bytes.Export_block names current) (fun (export_name, after_name) ->
          bind (read_export_kind after_name) (fun (export_kind, after_kind) ->
              bind (read_name_vec Ext_bytes.Export_block names after_kind)
                (fun (export_universe_params, after_params) ->
                  bind (read_term_ref Ext_bytes.Export_block terms after_params)
                    (fun (export_ty, after_ty) ->
                      bind
                        (validate_term_global_refs Ext_bytes.Export_block import_count
                           declaration_count export_offset export_ty)
                        (fun () ->
                          bind (read_option_term Ext_bytes.Export_block terms after_ty)
                            (fun (export_body, after_body) ->
                              let validate_body =
                                match export_body with
                                | None -> Ok ()
                                | Some body ->
                                    validate_term_global_refs Ext_bytes.Export_block import_count
                                      declaration_count export_offset body
                              in
                              bind validate_body (fun () ->
                                  bind (read_hash Ext_bytes.Export_block after_body)
                                    (fun (export_type_hash, after_type_hash) ->
                                      bind
                                        (read_option Ext_bytes.Export_block
                                           (read_hash Ext_bytes.Export_block) after_type_hash)
                                        (fun (export_body_hash, after_body_hash) ->
                                          bind
                                            (read_option Ext_bytes.Export_block
                                               (read_reducibility Ext_bytes.Export_block)
                                               after_body_hash)
                                            (fun (export_reducibility, after_reducibility) ->
                                              bind
                                                (read_option Ext_bytes.Export_block
                                                   (read_opacity Ext_bytes.Export_block)
                                                   after_reducibility)
                                                (fun (export_opacity, after_opacity) ->
                                                  bind
                                                    (read_hash Ext_bytes.Export_block after_opacity)
                                                    (fun
                                                      ( export_decl_interface_hash,
                                                        after_interface_hash )
                                                    ->
                                                      bind
                                                        (read_axiom_refs Ext_bytes.Export_block
                                                           import_count declaration_count names
                                                           after_interface_hash)
                                                        (fun
                                                          ( export_axiom_dependencies,
                                                            next )
                                                        ->
                                                          Ok
                                                            ( {
                                                                export_name;
                                                                export_kind;
                                                                export_universe_params;
                                                                export_ty;
                                                                export_body;
                                                                export_type_hash;
                                                                export_body_hash;
                                                                export_reducibility;
                                                                export_opacity;
                                                                export_decl_interface_hash;
                                                                export_axiom_dependencies;
                                                                export_offset;
                                                              },
                                                              next )))))))))))))))
    reader

let read_axiom_report import_count names declaration_count reader =
  let read_decl_report current =
    let report_offset = Ext_bytes.offset current in
    bind (Ext_bytes.read_usize Ext_bytes.Axiom_report current)
      (fun (report_decl_index, after_index) ->
        bind
          (read_axiom_refs Ext_bytes.Axiom_report import_count declaration_count names after_index)
          (fun (report_direct_axioms, after_direct) ->
            bind
              (read_axiom_refs Ext_bytes.Axiom_report import_count declaration_count names
                 after_direct)
              (fun (report_transitive_axioms, next) ->
                Ok
                  ( {
                      report_decl_index;
                      report_direct_axioms;
                      report_transitive_axioms;
                      report_offset;
                    },
                    next ))))
  in
  bind (read_vector Ext_bytes.Axiom_report read_decl_report reader)
    (fun (per_declaration, after_reports) ->
      let module_axioms_offset = Ext_bytes.offset after_reports in
      bind
        (read_axiom_refs Ext_bytes.Axiom_report import_count declaration_count names after_reports)
        (fun (module_axioms, next) ->
          Ok
            ( {
                per_declaration;
                module_axioms;
                module_axioms_offset;
                core_features = [];
                core_features_offset = None;
              },
              next )))

let core_feature_report_tag = "core_features"

let encoded_core_feature_report_tag =
  Ext_bytes.encode_uvar (Int64.of_int (String.length core_feature_report_tag))
  ^ core_feature_report_tag

let module_hash_trailer_len = 32 * 3

let has_core_feature_report reader =
  Ext_bytes.remaining reader
  > module_hash_trailer_len + String.length encoded_core_feature_report_tag
  &&
  match Ext_bytes.take Ext_bytes.Axiom_report (String.length encoded_core_feature_report_tag) reader with
  | Error _ -> false
  | Ok (prefix, _) -> prefix = encoded_core_feature_report_tag

let ensure_strict_feature_order features offset =
  let rec loop previous rest =
    match rest with
    | [] -> Ok ()
    | feature :: tail ->
        if previous >= feature.Ext_feature.feature then
          Ext_bytes.error Ext_bytes.Axiom_report offset Ext_bytes.Noncanonical_order
        else loop feature.Ext_feature.feature tail
  in
  match features with
  | [] -> Ext_bytes.error Ext_bytes.Axiom_report offset Ext_bytes.Noncanonical_order
  | first :: rest -> loop first.Ext_feature.feature rest

let read_core_features reader =
  let offset = Ext_bytes.offset reader in
  bind (Ext_bytes.read_string Ext_bytes.Axiom_report reader) (fun (tag, after_tag) ->
      if tag <> core_feature_report_tag then
        Ext_bytes.error Ext_bytes.Axiom_report offset Ext_bytes.Noncanonical_order
      else
        bind
          (read_vector Ext_bytes.Axiom_report
             (fun current ->
               let feature_offset = Ext_bytes.offset current in
               bind (Ext_bytes.read_string Ext_bytes.Axiom_report current)
                 (fun (feature, next) ->
                   Ok ({ Ext_feature.feature; offset = Some feature_offset }, next)))
             after_tag)
          (fun (features, next) ->
            bind (ensure_strict_feature_order features offset) (fun () -> Ok (features, next))))

let read_hashes reader =
  let export_hash_offset = Ext_bytes.offset reader in
  bind (read_hash Ext_bytes.Hashes reader) (fun (export_hash, after_export) ->
      let axiom_report_hash_offset = Ext_bytes.offset after_export in
      bind (read_hash Ext_bytes.Hashes after_export)
        (fun (axiom_report_hash, after_axiom) ->
          let certificate_hash_offset = Ext_bytes.offset after_axiom in
          bind (read_hash Ext_bytes.Hashes after_axiom)
            (fun (certificate_hash, next) ->
              Ok
                ( {
                    export_hash;
                    axiom_report_hash;
                    certificate_hash;
                    export_hash_offset;
                    axiom_report_hash_offset;
                    certificate_hash_offset;
                  },
                  next ))))

let read_module_sections reader =
  bind (read_header reader) (fun (header, after_header) ->
      bind (read_imports after_header) (fun (imports, after_imports) ->
          bind (read_name_table after_imports) (fun (name_table, after_names) ->
              let names = name_values name_table in
              let name_array = names_array name_table in
              bind (Ext_level.read_table names after_names) (fun (level_table, after_levels) ->
                  bind (Ext_term.read_table names level_table after_levels)
                    (fun (term_table, after_terms) ->
                      let term_array = Array.of_list term_table in
                      bind
                        (read_declarations (List.length imports) names level_table term_table
                           after_terms)
                        (fun (declaration_table, after_declarations) ->
                          bind
                            (read_export_block (List.length imports) name_array term_array
                               (List.length declaration_table) after_declarations)
                            (fun (export_block, after_exports) ->
                              bind
                                (read_axiom_report (List.length imports) name_array
                                   (List.length declaration_table) after_exports)
                                (fun (axiom_report, after_axiom_report) ->
                                  let feature_result =
                                    if has_core_feature_report after_axiom_report then
                                      bind (read_core_features after_axiom_report)
                                        (fun (core_features, next) ->
                                          Ok
                                            ( {
                                                axiom_report with
                                                core_features;
                                                core_features_offset =
                                                  Some (Ext_bytes.offset after_axiom_report);
                                              },
                                              next ))
                                    else Ok (axiom_report, after_axiom_report)
                                  in
                                  bind feature_result (fun (axiom_report, after_features) ->
                                      bind (read_hashes after_features) (fun (hashes, next) ->
                                          Ok
                                            ( {
                                                header;
                                                imports;
                                                name_table;
                                                level_table;
                                                term_table;
                                                declaration_table;
                                                export_block;
                                                axiom_report;
                                                hashes;
                                              },
                                              next )))))))))))

let add_unique equal value values =
  if List.exists (fun existing -> equal existing value) values then values else value :: values

let list_contains equal value values = List.exists (fun existing -> equal existing value) values

type used_tables = {
  mutable used_names : Ext_name.t list;
  mutable used_levels : Ext_level.t list;
  mutable used_terms : Ext_term.t list;
}

let empty_used_tables () = { used_names = []; used_levels = []; used_terms = [] }

let mark_name used name =
  used.used_names <- add_unique Ext_name.equal name used.used_names

let byte value = String.make 1 (Char.chr value)

let encode_usize value = Ext_bytes.encode_uvar (Int64.of_int value)

let encode_name_key name =
  let components = Ext_name.components name in
  encode_usize (List.length components)
  ^ String.concat ""
      (List.map (fun component -> encode_usize (String.length component) ^ component) components)

let hash_with_domain domain payload =
  Bytes.to_string (Ext_hash.sha256_raw_string (domain ^ payload))

let name_index section offset name_table name =
  let rec loop index entries =
    match entries with
    | [] -> Ext_bytes.error section offset Ext_bytes.Dangling_reference
    | entry :: rest ->
        if Ext_name.equal entry.name name then Ok index else loop (index + 1) rest
  in
  loop 0 name_table

let global_ref_payload section offset name_table global_ref =
  match global_ref with
  | Ext_term.Imported { import_index; name; decl_interface_hash } ->
      bind (name_index section offset name_table name) (fun name_id ->
          Ok
            (byte 0x00 ^ encode_usize import_index ^ encode_usize name_id
           ^ decl_interface_hash))
  | Ext_term.Local { decl_index } -> Ok (byte 0x01 ^ encode_usize decl_index)
  | Ext_term.LocalGenerated { decl_index; name } ->
      bind (name_index section offset name_table name) (fun name_id ->
          Ok (byte 0x02 ^ encode_usize decl_index ^ encode_usize name_id))
  | Ext_term.Builtin { name; decl_interface_hash } ->
      bind (name_index section offset name_table name) (fun name_id ->
          Ok (byte 0x03 ^ encode_usize name_id ^ decl_interface_hash))

let rec level_height level =
  match level with
  | Ext_level.Zero | Ext_level.Param _ -> 0
  | Ext_level.Succ inner -> level_height inner + 1
  | Ext_level.Max (lhs, rhs) | Ext_level.Imax (lhs, rhs) ->
      max (level_height lhs) (level_height rhs) + 1

let rec level_payload level =
  match level with
  | Ext_level.Zero -> byte 0x00
  | Ext_level.Succ inner -> byte 0x01 ^ level_hash inner
  | Ext_level.Max (lhs, rhs) -> byte 0x02 ^ level_hash lhs ^ level_hash rhs
  | Ext_level.Imax (lhs, rhs) -> byte 0x03 ^ level_hash lhs ^ level_hash rhs
  | Ext_level.Param name -> byte 0x04 ^ encode_name_key name

and level_hash level = hash_with_domain "NPA-LEVEL-0.1" (level_payload level)

let level_order_key level = (level_height level, level_payload level)

let rec term_height term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ | Ext_term.Const _ -> 0
  | Ext_term.App (fn, arg) -> max (term_height fn) (term_height arg) + 1
  | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
      max (term_height ty) (term_height body) + 1
  | Ext_term.Let (ty, value, body) ->
      max (term_height ty) (max (term_height value) (term_height body)) + 1

let rec term_payload name_table offset term =
  match term with
  | Ext_term.Sort level -> Ok (byte 0x00 ^ level_hash level)
  | Ext_term.BVar index -> Ok (byte 0x01 ^ encode_usize index)
  | Ext_term.Const (global_ref, levels) ->
      bind (global_ref_payload Ext_bytes.Term_table offset name_table global_ref)
        (fun global_ref_bytes ->
          Ok
            (byte 0x02 ^ global_ref_bytes ^ encode_usize (List.length levels)
           ^ String.concat "" (List.map level_hash levels)))
  | Ext_term.App (fn, arg) ->
      bind (term_hash name_table offset fn) (fun fn_hash ->
          bind (term_hash name_table offset arg) (fun arg_hash ->
              Ok (byte 0x03 ^ fn_hash ^ arg_hash)))
  | Ext_term.Lam (ty, body) ->
      bind (term_hash name_table offset ty) (fun ty_hash ->
          bind (term_hash name_table offset body) (fun body_hash ->
              Ok (byte 0x04 ^ ty_hash ^ body_hash)))
  | Ext_term.Pi (ty, body) ->
      bind (term_hash name_table offset ty) (fun ty_hash ->
          bind (term_hash name_table offset body) (fun body_hash ->
              Ok (byte 0x05 ^ ty_hash ^ body_hash)))
  | Ext_term.Let (ty, value, body) ->
      bind (term_hash name_table offset ty) (fun ty_hash ->
          bind (term_hash name_table offset value) (fun value_hash ->
              bind (term_hash name_table offset body) (fun body_hash ->
                  Ok (byte 0x06 ^ ty_hash ^ value_hash ^ body_hash))))

and term_hash name_table offset term =
  bind (term_payload name_table offset term) (fun payload ->
      Ok (hash_with_domain "NPA-TERM-0.1" payload))

let term_order_key name_table offset term =
  bind (term_payload name_table offset term) (fun payload -> Ok (term_height term, payload))

let validate_strict_order section offset_of value_of key_of entries =
  let rec loop previous entries =
    match entries with
    | [] -> Ok ()
    | entry :: rest ->
        let current = key_of (value_of entry) in
        if Stdlib.compare previous current >= 0 then
          Ext_bytes.error section (offset_of entry) Ext_bytes.Noncanonical_order
        else loop current rest
  in
  match entries with
  | [] -> Ok ()
  | entry :: rest -> loop (key_of (value_of entry)) rest

let validate_name_table_order name_table =
  validate_strict_order Ext_bytes.Name_table
    (fun (entry : located_name) -> entry.offset)
    (fun entry -> entry.name)
    (fun name -> name) name_table

let validate_level_table_order level_table =
  validate_strict_order Ext_bytes.Level_table
    (fun (entry : Ext_level.located) -> entry.offset)
    (fun entry -> entry.Ext_level.level)
    level_order_key level_table

let validate_term_table_order name_table term_table =
  let rec loop previous entries =
    match entries with
    | [] -> Ok ()
    | entry :: rest ->
        bind (term_order_key name_table entry.Ext_term.offset entry.Ext_term.term)
          (fun current ->
            if Stdlib.compare previous current >= 0 then
              Ext_bytes.error Ext_bytes.Term_table entry.Ext_term.offset
                Ext_bytes.Noncanonical_order
            else loop current rest)
  in
  match term_table with
  | [] -> Ok ()
  | entry :: rest ->
      bind (term_order_key name_table entry.Ext_term.offset entry.Ext_term.term) (fun first ->
          loop first rest)

let rec mark_level used level =
  if list_contains ( = ) level used.used_levels then Ok ()
  else (
    used.used_levels <- level :: used.used_levels;
    match level with
    | Ext_level.Zero -> Ok ()
    | Ext_level.Param name ->
        mark_name used name;
        Ok ()
    | Ext_level.Succ inner -> mark_level used inner
    | Ext_level.Max (lhs, rhs) | Ext_level.Imax (lhs, rhs) ->
        bind (mark_level used lhs) (fun () -> mark_level used rhs))

let mark_global_ref used import_count declaration_count section offset global_ref =
  bind (validate_global_ref section import_count declaration_count offset global_ref) (fun () ->
      match global_ref with
      | Ext_term.Imported { name; _ } | Ext_term.Builtin { name; _ } ->
          mark_name used name;
          Ok ()
      | Ext_term.LocalGenerated { name; _ } ->
          mark_name used name;
          Ok ()
      | Ext_term.Local _ -> Ok ())

let rec mark_term used import_count declaration_count section offset term =
  if list_contains ( = ) term used.used_terms then Ok ()
  else (
    used.used_terms <- term :: used.used_terms;
    match term with
    | Ext_term.Sort level -> mark_level used level
    | Ext_term.BVar _ -> Ok ()
    | Ext_term.Const (global_ref, levels) ->
        bind (mark_global_ref used import_count declaration_count section offset global_ref)
          (fun () ->
            List.fold_left
              (fun result level -> bind result (fun () -> mark_level used level))
              (Ok ()) levels)
    | Ext_term.App (fn, arg) ->
        bind (mark_term used import_count declaration_count section offset fn)
          (fun () -> mark_term used import_count declaration_count section offset arg)
    | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
        bind (mark_term used import_count declaration_count section offset ty)
          (fun () -> mark_term used import_count declaration_count section offset body)
    | Ext_term.Let (ty, value, body) ->
        bind (mark_term used import_count declaration_count section offset ty)
          (fun () ->
            bind (mark_term used import_count declaration_count section offset value) (fun () ->
                mark_term used import_count declaration_count section offset body)))

let mark_names used names =
  List.iter (mark_name used) names;
  Ok ()

let mark_universe_constraints used constraints =
  List.fold_left
    (fun result constraint_ ->
      bind result (fun () ->
          bind (mark_level used constraint_.constraint_lhs) (fun () ->
              mark_level used constraint_.constraint_rhs)))
    (Ok ()) constraints

let mark_binder_types used import_count declaration_count section offset binders =
  List.fold_left
    (fun result binder ->
      bind result (fun () ->
          mark_term used import_count declaration_count section offset binder.binder_ty))
    (Ok ()) binders

let mark_constructor_specs used import_count declaration_count section offset constructors =
  List.fold_left
    (fun result constructor ->
      bind result (fun () ->
          mark_name used constructor.constructor_name;
          mark_term used import_count declaration_count section offset constructor.constructor_ty))
    (Ok ()) constructors

let mark_recursor_spec used import_count declaration_count section offset recursor =
  match recursor with
  | None -> Ok ()
  | Some recursor ->
      mark_name used recursor.recursor_name;
      bind (mark_names used recursor.recursor_universe_params) (fun () ->
          mark_term used import_count declaration_count section offset recursor.recursor_ty)

let mark_axiom_refs used import_count declaration_count section offset axioms =
  List.fold_left
    (fun result axiom ->
      bind result (fun () ->
          bind
            (mark_global_ref used import_count declaration_count section offset
               axiom.axiom_global_ref)
            (fun () ->
              mark_name used axiom.axiom_name;
              Ok ())))
    (Ok ()) axioms

let mark_dependency_entries used import_count declaration_count section offset dependencies =
  List.fold_left
    (fun result dependency ->
      bind result (fun () ->
          mark_global_ref used import_count declaration_count section offset
            dependency.dependency_global_ref))
    (Ok ()) dependencies

let mark_decl_payload used import_count declaration_count payload offset =
  match payload with
  | AxiomDecl { decl_name; decl_universe_params; decl_universe_constraints; decl_ty } ->
      mark_name used decl_name;
      bind (mark_names used decl_universe_params) (fun () ->
          bind (mark_universe_constraints used decl_universe_constraints) (fun () ->
              mark_term used import_count declaration_count Ext_bytes.Declarations offset decl_ty))
  | DefDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        decl_ty;
        decl_value;
        _;
      } ->
      mark_name used decl_name;
      bind (mark_names used decl_universe_params) (fun () ->
          bind (mark_universe_constraints used decl_universe_constraints) (fun () ->
              bind
                (mark_term used import_count declaration_count Ext_bytes.Declarations offset decl_ty)
                (fun () ->
                  mark_term used import_count declaration_count Ext_bytes.Declarations offset
                    decl_value)))
  | TheoremDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        decl_ty;
        decl_proof;
        _;
      } ->
      mark_name used decl_name;
      bind (mark_names used decl_universe_params) (fun () ->
          bind (mark_universe_constraints used decl_universe_constraints) (fun () ->
              bind
                (mark_term used import_count declaration_count Ext_bytes.Declarations offset decl_ty)
                (fun () ->
                  mark_term used import_count declaration_count Ext_bytes.Declarations offset
                    decl_proof)))
  | InductiveDecl
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
      mark_name used decl_name;
      bind (mark_names used decl_universe_params) (fun () ->
          bind (mark_universe_constraints used decl_universe_constraints) (fun () ->
              bind (mark_level used ind_sort) (fun () ->
                  bind
                    (mark_binder_types used import_count declaration_count Ext_bytes.Declarations
                       offset ind_params)
                    (fun () ->
                      bind
                        (mark_binder_types used import_count declaration_count
                           Ext_bytes.Declarations offset ind_indices)
                        (fun () ->
                          bind
                            (mark_constructor_specs used import_count declaration_count
                               Ext_bytes.Declarations offset ind_constructors)
                            (fun () ->
                              mark_recursor_spec used import_count declaration_count
                                Ext_bytes.Declarations offset ind_recursor))))))
  | MutualInductiveBlockDecl
      { decl_name; decl_universe_params; decl_universe_constraints; mutual_inductives } ->
      mark_name used decl_name;
      bind (mark_names used decl_universe_params) (fun () ->
          bind (mark_universe_constraints used decl_universe_constraints) (fun () ->
              List.fold_left
                (fun result inductive ->
                  bind result (fun () ->
                      mark_name used inductive.mutual_name;
                      bind (mark_level used inductive.mutual_sort) (fun () ->
                          bind
                            (mark_binder_types used import_count declaration_count
                               Ext_bytes.Declarations offset inductive.mutual_params)
                            (fun () ->
                              bind
                                (mark_binder_types used import_count declaration_count
                                   Ext_bytes.Declarations offset inductive.mutual_indices)
                                (fun () ->
                                  bind
                                    (mark_constructor_specs used import_count declaration_count
                                       Ext_bytes.Declarations offset
                                       inductive.mutual_constructors)
                                    (fun () ->
                                      mark_recursor_spec used import_count declaration_count
                                        Ext_bytes.Declarations offset
                                        inductive.mutual_recursor))))))
                (Ok ()) mutual_inductives))

let mark_declaration used import_count declaration_count declaration =
  bind
    (mark_decl_payload used import_count declaration_count declaration.payload declaration.offset)
    (fun () ->
      bind
        (mark_dependency_entries used import_count declaration_count Ext_bytes.Declarations
           declaration.offset declaration.dependencies)
        (fun () ->
          mark_axiom_refs used import_count declaration_count Ext_bytes.Declarations
            declaration.offset declaration.axiom_dependencies))

let mark_export used import_count declaration_count export =
  mark_name used export.export_name;
  bind (mark_names used export.export_universe_params) (fun () ->
      bind
        (mark_term used import_count declaration_count Ext_bytes.Export_block export.export_offset
           export.export_ty)
        (fun () ->
          bind
            (match export.export_body with
            | None -> Ok ()
            | Some body ->
                mark_term used import_count declaration_count Ext_bytes.Export_block
                  export.export_offset body)
            (fun () ->
              mark_axiom_refs used import_count declaration_count Ext_bytes.Export_block
                export.export_offset export.export_axiom_dependencies)))

let mark_decl_axiom_report used import_count declaration_count report =
  if report.report_decl_index >= declaration_count then
    Ext_bytes.error Ext_bytes.Axiom_report report.report_offset Ext_bytes.Dangling_reference
  else
    bind
      (mark_axiom_refs used import_count declaration_count Ext_bytes.Axiom_report
         report.report_offset report.report_direct_axioms)
      (fun () ->
        mark_axiom_refs used import_count declaration_count Ext_bytes.Axiom_report
          report.report_offset report.report_transitive_axioms)

let fold_unit values f =
  List.fold_left (fun result value -> bind result (fun () -> f value)) (Ok ()) values

let collect_roots decoded =
  let used = empty_used_tables () in
  mark_name used decoded.header.module_name;
  List.iter (fun import -> mark_name used import.import_entry.module_name) decoded.imports;
  let import_count = List.length decoded.imports in
  let declaration_count = List.length decoded.declaration_table in
  bind
    (fold_unit decoded.declaration_table
       (mark_declaration used import_count declaration_count))
    (fun () ->
      bind
        (fold_unit decoded.export_block (mark_export used import_count declaration_count))
        (fun () ->
          bind
            (fold_unit decoded.axiom_report.per_declaration
               (mark_decl_axiom_report used import_count declaration_count))
            (fun () ->
              bind
                (mark_axiom_refs used import_count declaration_count Ext_bytes.Axiom_report
                   decoded.axiom_report.module_axioms_offset decoded.axiom_report.module_axioms)
                (fun () -> Ok used))))

let validate_used_names name_table used_names =
  match
    List.find_opt (fun entry -> not (list_contains Ext_name.equal entry.name used_names)) name_table
  with
  | None -> Ok ()
  | Some entry -> Ext_bytes.error Ext_bytes.Name_table entry.offset Ext_bytes.Unused_table_entry

let validate_used_levels level_table used_levels =
  let rec loop entries =
    match entries with
    | [] -> Ok ()
    | entry :: rest ->
        if list_contains ( = ) entry.Ext_level.level used_levels then loop rest
        else Ext_bytes.error Ext_bytes.Level_table entry.offset Ext_bytes.Unused_table_entry
  in
  loop level_table

let validate_used_terms term_table used_terms =
  let rec loop entries =
    match entries with
    | [] -> Ok ()
    | entry :: rest ->
        if list_contains ( = ) entry.Ext_term.term used_terms then loop rest
        else Ext_bytes.error Ext_bytes.Term_table entry.offset Ext_bytes.Unused_table_entry
  in
  loop term_table

let validate_decoded_module decoded =
  bind (validate_name_table_order decoded.name_table) (fun () ->
      bind (validate_level_table_order decoded.level_table) (fun () ->
          bind (validate_term_table_order decoded.name_table decoded.term_table) (fun () ->
              bind (collect_roots decoded) (fun used ->
                  bind (validate_used_names decoded.name_table used.used_names) (fun () ->
                      bind (validate_used_levels decoded.level_table used.used_levels) (fun () ->
                          validate_used_terms decoded.term_table used.used_terms))))))

let read_module reader =
  bind (read_module_sections reader) (fun (decoded, next) ->
      bind (validate_decoded_module decoded) (fun () ->
          if Ext_bytes.remaining next = 0 then Ok (decoded, next)
          else Ext_bytes.error Ext_bytes.Full_certificate (Ext_bytes.offset next) Ext_bytes.Trailing_bytes))
