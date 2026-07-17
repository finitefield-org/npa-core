type signature_origin =
  | Builtin
  | Imported of { import_index : int }
  | Local of { decl_index : int }
  | Local_generated of {
      decl_index : int;
      name : Ext_name.t;
    }

type unfolding =
  | No_unfolding
  | Reducible of Ext_term.t
  | Opaque

type signature = {
  signature_name : Ext_name.t;
  signature_decl_interface_hash : Ext_hash.digest option;
  signature_universe_params : Ext_name.t list;
  signature_universe_constraints : Ext_cert.universe_constraint list;
  signature_ty : Ext_term.t;
  signature_unfolding : unfolding;
  signature_origin : signature_origin;
}

type generated_key = {
  generated_decl_index : int;
  generated_name : Ext_name.t;
}

type imported_single_recursor_runtime = {
  imported_runtime_import_index : int;
  imported_runtime_decl_interface_hash : Ext_hash.digest;
  imported_runtime_synthetic_decl_index : int;
  imported_runtime_universe_params : Ext_name.t list;
  imported_runtime_params : Ext_cert.binder_type list;
  imported_runtime_indices : Ext_cert.binder_type list;
  imported_runtime_constructors : Ext_cert.constructor_spec list;
  imported_runtime_rules : Ext_cert.recursor_rules;
}

type imported_mutual_recursor_runtime = {
  imported_mutual_import_index : int;
  imported_mutual_decl_interface_hash : Ext_hash.digest;
  imported_mutual_synthetic_decl_index : int;
  imported_mutual_universe_params : Ext_name.t list;
  imported_mutual_families : Ext_cert.mutual_inductive_spec list;
  imported_mutual_target_index : int;
  imported_mutual_recursor : Ext_cert.recursor_spec;
}

type imported_recursor_runtime =
  | Imported_single of imported_single_recursor_runtime
  | Imported_mutual of imported_mutual_recursor_runtime

type t = {
  imports : Ext_import_store.import_environment;
  checked_declaration_count : int;
  local_declarations : (int * Ext_cert.declaration) list;
  local_signatures : (int * signature) list;
  generated_signatures : (generated_key * signature) list;
  imported_recursor_cache :
    ((int * Ext_name.t * Ext_hash.digest), imported_recursor_runtime option)
    Hashtbl.t;
  imported_mutual_block_cache :
    ((int * Ext_hash.digest), imported_mutual_recursor_runtime list option)
    Hashtbl.t;
}

type error_reason =
  | Unknown_reference
  | Duplicate_universe_param

type error = {
  reason : error_reason;
  section : Ext_bytes.certificate_section;
  offset : Ext_bytes.offset;
}

let empty =
  {
    imports = Ext_import_store.import_environment_empty;
    checked_declaration_count = 0;
    local_declarations = [];
    local_signatures = [];
    generated_signatures = [];
    imported_recursor_cache = Hashtbl.create 0;
    imported_mutual_block_cache = Hashtbl.create 0;
  }

let of_imports imports =
  {
    empty with
    imports;
    imported_recursor_cache = Hashtbl.create 16;
    imported_mutual_block_cache = Hashtbl.create 8;
  }

let find_imported_recursor_cache env import_index recursor_name
    decl_interface_hash =
  Hashtbl.find_opt env.imported_recursor_cache
    (import_index, recursor_name, decl_interface_hash)

let cache_imported_recursor env import_index recursor_name decl_interface_hash
    runtime =
  Hashtbl.replace env.imported_recursor_cache
    (import_index, recursor_name, decl_interface_hash)
    runtime

let find_imported_mutual_block_cache env import_index decl_interface_hash =
  Hashtbl.find_opt env.imported_mutual_block_cache
    (import_index, decl_interface_hash)

let cache_imported_mutual_block env import_index decl_interface_hash runtimes =
  Hashtbl.replace env.imported_mutual_block_cache
    (import_index, decl_interface_hash)
    runtimes

let error section offset reason = Error { reason; section; offset }

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let error_reason_code reason =
  match reason with
  | Unknown_reference -> "unknown_reference"
  | Duplicate_universe_param -> "duplicate_universe_param"

let error_kind error =
  match error.reason with
  | Unknown_reference -> "type_mismatch"
  | Duplicate_universe_param -> "universe_inconsistency"

let get index values =
  if index < 0 then None
  else
    let rec loop cursor remaining =
      match remaining with
      | [] -> None
      | value :: rest ->
          if cursor = index then Some value else loop (cursor + 1) rest
    in
    loop 0 values

let rec has_name name names =
  match names with
  | [] -> false
  | current :: rest -> Ext_name.equal current name || has_name name rest

let validate_universe_params section offset params =
  let rec loop seen remaining =
    match remaining with
    | [] -> Ok ()
    | name :: rest ->
        if has_name name seen then error section offset Duplicate_universe_param
        else loop (name :: seen) rest
  in
  loop [] params

let make_signature ?decl_interface_hash section offset name universe_params
    universe_constraints ty unfolding origin =
  bind (validate_universe_params section offset universe_params) (fun () ->
      Ok
        {
          signature_name = name;
          signature_decl_interface_hash = decl_interface_hash;
          signature_universe_params = universe_params;
          signature_universe_constraints = universe_constraints;
          signature_ty = ty;
          signature_unfolding = unfolding;
          signature_origin = origin;
        })

let name components =
  match Ext_name.of_components components with
  | Some name -> name
  | None -> invalid_arg "invalid builtin name"

let split_dotted dotted =
  let length = String.length dotted in
  let rec loop start parts =
    try
      let index = String.index_from dotted start '.' in
      loop (index + 1) (String.sub dotted start (index - start) :: parts)
    with Not_found ->
      List.rev (String.sub dotted start (length - start) :: parts)
  in
  loop 0 []

let name_of_dotted dotted = name (split_dotted dotted)

let level_param dotted = Ext_level.Param (name_of_dotted dotted)

let level_type0 = Ext_level.Succ Ext_level.Zero


let sort level = Ext_term.Sort level

let bvar index = Ext_term.BVar index

let pi ty body = Ext_term.Pi (ty, body)

let app fn arg = Ext_term.App (fn, arg)

let rec apps fn args =
  match args with
  | [] -> fn
  | arg :: rest -> apps (app fn arg) rest

let builtin_hash_tag dotted =
  match dotted with
  | "Nat" -> Some "npa.machine-tactic.builtin.nat.v1"
  | "Nat.zero" -> Some "npa.machine-tactic.builtin.nat.zero.v1"
  | "Nat.succ" -> Some "npa.machine-tactic.builtin.nat.succ.v1"
  | "Nat.rec" -> Some "npa.machine-tactic.builtin.nat.rec.v1"
  | "Eq" -> Some "npa.machine-tactic.builtin.eq.v1"
  | "Eq.refl" -> Some "npa.machine-tactic.builtin.eq.refl.v1"
  | "Eq.rec" -> Some "npa.machine-tactic.builtin.eq.rec.v1"
  | _ -> None

let builtin_decl_interface_hash builtin_name =
  match builtin_hash_tag (Ext_name.to_string builtin_name) with
  | None -> None
  | Some tag -> Some (Ext_canonical.hash_with_domain "NPA-BUILTIN-INTERFACE-0.1" tag)

let builtin_const dotted levels =
  let builtin_name = name_of_dotted dotted in
  match builtin_decl_interface_hash builtin_name with
  | None -> invalid_arg "unknown builtin"
  | Some decl_interface_hash ->
      Ext_term.Const (Ext_term.Builtin { name = builtin_name; decl_interface_hash }, levels)

let nat = builtin_const "Nat" []

let nat_zero = builtin_const "Nat.zero" []

let nat_succ value = app (builtin_const "Nat.succ" []) value

let nat_rec_type level =
  let motive_ty = pi nat (sort level) in
  let z_ty = app (bvar 0) nat_zero in
  let s_ty =
    pi nat (pi (app (bvar 2) (bvar 0)) (app (bvar 3) (nat_succ (bvar 1))))
  in
  pi motive_ty (pi z_ty (pi s_ty (pi nat (app (bvar 3) (bvar 0)))))

let eq level ty lhs rhs = apps (builtin_const "Eq" [ level ]) [ ty; lhs; rhs ]

let eq_refl level ty value = apps (builtin_const "Eq.refl" [ level ]) [ ty; value ]

let eq_type level = pi (sort level) (pi (bvar 0) (pi (bvar 1) (sort Ext_level.Zero)))

let eq_refl_type level =
  pi (sort level) (pi (bvar 0) (eq level (bvar 1) (bvar 0) (bvar 0)))

let eq_rec_type value_level motive_level =
  let motive_ty =
    pi
      (bvar 1)
      (pi (eq value_level (bvar 2) (bvar 1) (bvar 0)) (sort motive_level))
  in
  let refl_proof = eq_refl value_level (bvar 2) (bvar 1) in
  let minor_ty = apps (bvar 0) [ bvar 1; refl_proof ] in
  let major_ty = eq value_level (bvar 4) (bvar 3) (bvar 0) in
  let result_ty = apps (bvar 3) [ bvar 1; bvar 0 ] in
  pi
    (sort value_level)
    (pi
       (bvar 0)
       (pi motive_ty (pi minor_ty (pi (bvar 3) (pi major_ty result_ty)))))

let builtin_signature builtin_name decl_interface_hash =
  if builtin_decl_interface_hash builtin_name <> Some decl_interface_hash then None
  else
    let dotted = Ext_name.to_string builtin_name in
    let signature =
      match dotted with
      | "Nat" -> Some ([], sort level_type0)
      | "Nat.zero" -> Some ([], nat)
      | "Nat.succ" -> Some ([], pi nat nat)
      | "Nat.rec" -> Some ([ name [ "u" ] ], nat_rec_type (level_param "u"))
      | "Eq" -> Some ([ name [ "u" ] ], eq_type (level_param "u"))
      | "Eq.refl" -> Some ([ name [ "u" ] ], eq_refl_type (level_param "u"))
      | "Eq.rec" ->
          Some
            ([ name [ "u" ]; name [ "v" ] ], eq_rec_type (level_param "u") (level_param "v"))
      | _ -> None
    in
    match signature with
    | None -> None
    | Some (universe_params, ty) ->
        Some
          {
            signature_name = builtin_name;
            signature_decl_interface_hash = Some decl_interface_hash;
            signature_universe_params = universe_params;
            signature_universe_constraints = [];
            signature_ty = ty;
            signature_unfolding = No_unfolding;
            signature_origin = Builtin;
          }

let generated_key_equal left right =
  left.generated_decl_index = right.generated_decl_index
  && Ext_name.equal left.generated_name right.generated_name

let find_local_signature decl_index signatures =
  let rec loop remaining =
    match remaining with
    | [] -> None
    | (index, signature) :: rest ->
        if index = decl_index then Some signature else loop rest
  in
  loop signatures

let find_local_declaration decl_index declarations =
  let rec loop remaining =
    match remaining with
    | [] -> None
    | (index, declaration) :: rest ->
        if index = decl_index then Some declaration else loop rest
  in
  loop declarations

let find_generated_signature key signatures =
  let rec loop remaining =
    match remaining with
    | [] -> None
    | (current, signature) :: rest ->
        if generated_key_equal current key then Some signature else loop rest
  in
  loop signatures

let find_import import_index imports =
  get import_index (Ext_import_store.import_environment_imports imports)

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

let find_current_import_index imports source =
  let resolved = Ext_import_store.import_environment_imports imports in
  let rec loop index remaining =
    match remaining with
    | [] -> None
    | current :: rest ->
        if
          Ext_name.equal current.Ext_import_store.resolved_module_name
            source.Ext_import.module_name
          && current.Ext_import_store.resolved_export_hash = source.Ext_import.export_hash
        then Some index
        else loop (index + 1) rest
  in
  loop 0 resolved

let rec instantiate_public_term env owner_import_index owner_public_env section offset term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> Ok term
  | Ext_term.Const (global_ref, levels) ->
      bind
        (instantiate_public_global_ref env owner_import_index owner_public_env section offset
           global_ref)
        (fun public_ref -> Ok (Ext_term.Const (public_ref, levels)))
  | Ext_term.App (fn, arg) ->
      bind
        (instantiate_public_term env owner_import_index owner_public_env section offset fn)
        (fun public_fn ->
          bind
            (instantiate_public_term env owner_import_index owner_public_env section offset arg)
            (fun public_arg -> Ok (Ext_term.App (public_fn, public_arg))))
  | Ext_term.Lam (ty, body) ->
      bind
        (instantiate_public_term env owner_import_index owner_public_env section offset ty)
        (fun public_ty ->
          bind
            (instantiate_public_term env owner_import_index owner_public_env section offset body)
            (fun public_body -> Ok (Ext_term.Lam (public_ty, public_body))))
  | Ext_term.Pi (ty, body) ->
      bind
        (instantiate_public_term env owner_import_index owner_public_env section offset ty)
        (fun public_ty ->
          bind
            (instantiate_public_term env owner_import_index owner_public_env section offset body)
            (fun public_body -> Ok (Ext_term.Pi (public_ty, public_body))))
  | Ext_term.Let (ty, value, body) ->
      bind
        (instantiate_public_term env owner_import_index owner_public_env section offset ty)
        (fun public_ty ->
          bind
            (instantiate_public_term env owner_import_index owner_public_env section offset value)
            (fun public_value ->
              bind
                (instantiate_public_term env owner_import_index owner_public_env section offset
                   body)
                (fun public_body -> Ok (Ext_term.Let (public_ty, public_value, public_body)))))

and instantiate_public_global_ref env owner_import_index owner_public_env section offset
    global_ref =
  match global_ref with
  | Ext_term.Builtin _ -> Ok global_ref
  | Ext_term.Imported { import_index; name; decl_interface_hash }
    when import_index = Ext_import_store.public_self_import_index ->
      Ok (Ext_term.Imported { import_index = owner_import_index; name; decl_interface_hash })
  | Ext_term.Imported { import_index; name; decl_interface_hash } -> (
      match get import_index owner_public_env.Ext_import_store.public_imports with
      | None -> error section offset Unknown_reference
      | Some source -> (
          match find_current_import_index env.imports source with
          | None -> error section offset Unknown_reference
          | Some remapped ->
              Ok (Ext_term.Imported { import_index = remapped; name; decl_interface_hash })))
  | Ext_term.Local _ | Ext_term.LocalGenerated _ -> error section offset Unknown_reference

let signature_of_public_export env import_index public_environment section offset export =
  bind
    (instantiate_public_term env import_index public_environment section offset
       export.Ext_import_store.public_ty)
    (fun ty ->
      let body =
        match export.Ext_import_store.public_export_kind with
        | Ext_cert.Export_theorem -> Ok None
        | _ -> (
            match export.Ext_import_store.public_body with
            | None -> Ok None
            | Some body ->
                bind
                  (instantiate_public_term env import_index public_environment section offset
                     body)
                  (fun instantiated -> Ok (Some instantiated)))
      in
      bind body (fun body ->
          let unfolding =
            match export.Ext_import_store.public_export_kind with
            | Ext_cert.Export_theorem -> Opaque
            | _ -> (
                match body with
                | None -> No_unfolding
                | Some value -> Reducible value)
          in
          make_signature
            ~decl_interface_hash:export.Ext_import_store.public_decl_interface_hash
            section offset export.Ext_import_store.public_export_name
            export.Ext_import_store.public_universe_params
            export.Ext_import_store.public_universe_constraints ty unfolding
            (Imported { import_index })))

let declaration_universe_params payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_universe_params; _ }
  | Ext_cert.DefDecl { decl_universe_params; _ }
  | Ext_cert.TheoremDecl { decl_universe_params; _ }
  | Ext_cert.InductiveDecl { decl_universe_params; _ }
  | Ext_cert.MutualInductiveBlockDecl { decl_universe_params; _ } ->
      decl_universe_params

let rec pi_of_binders (binders : Ext_cert.binder_type list) result =
  match binders with
  | [] -> result
  | binder :: rest -> Ext_term.Pi (binder.Ext_cert.binder_ty, pi_of_binders rest result)

let signature_of_declaration decl_index (declaration : Ext_cert.declaration) =
  let section = Ext_bytes.Declarations in
  let offset = declaration.Ext_cert.offset in
  let decl_interface_hash =
    declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
  in
  match declaration.Ext_cert.payload with
  | Ext_cert.AxiomDecl
      { decl_name; decl_universe_params; decl_universe_constraints; decl_ty } ->
      make_signature ~decl_interface_hash section offset decl_name decl_universe_params
        decl_universe_constraints decl_ty No_unfolding (Local { decl_index })
  | Ext_cert.DefDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        decl_ty;
        decl_value;
        decl_reducibility;
      } ->
      let unfolding =
        match decl_reducibility with
        | Ext_cert.Reducible -> Reducible decl_value
        | Ext_cert.Opaque_reducibility -> Opaque
      in
      make_signature ~decl_interface_hash section offset decl_name decl_universe_params
        decl_universe_constraints decl_ty unfolding (Local { decl_index })
  | Ext_cert.TheoremDecl
      { decl_name; decl_universe_params; decl_universe_constraints; decl_ty; _ } ->
      make_signature ~decl_interface_hash section offset decl_name decl_universe_params
        decl_universe_constraints decl_ty Opaque (Local { decl_index })
  | Ext_cert.InductiveDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        ind_params;
        ind_indices;
        ind_sort;
        _;
      } ->
      make_signature ~decl_interface_hash section offset decl_name decl_universe_params
        decl_universe_constraints
        (pi_of_binders (ind_params @ ind_indices) (Ext_term.Sort ind_sort))
        No_unfolding (Local { decl_index })
  | Ext_cert.MutualInductiveBlockDecl _ -> error section offset Unknown_reference

let constructor_signature decl_index decl_interface_hash universe_params
    universe_constraints offset (constructor : Ext_cert.constructor_spec) =
  make_signature ~decl_interface_hash Ext_bytes.Declarations offset
    constructor.Ext_cert.constructor_name
    universe_params universe_constraints constructor.Ext_cert.constructor_ty No_unfolding
    (Local_generated { decl_index; name = constructor.Ext_cert.constructor_name })

let recursor_signature decl_index decl_interface_hash universe_constraints offset
    (recursor : Ext_cert.recursor_spec) =
  make_signature ~decl_interface_hash Ext_bytes.Declarations offset
    recursor.Ext_cert.recursor_name
    recursor.Ext_cert.recursor_universe_params universe_constraints
    recursor.Ext_cert.recursor_ty
    No_unfolding
    (Local_generated { decl_index; name = recursor.Ext_cert.recursor_name })

let generated_signatures_of_declaration decl_index (declaration : Ext_cert.declaration) =
  let offset = declaration.Ext_cert.offset in
  let decl_interface_hash =
    declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
  in
  let add_generated signature generated =
    let key =
      {
        generated_decl_index = decl_index;
        generated_name = signature.signature_name;
      }
    in
    generated @ [ (key, signature) ]
  in
  let collect_constructor_signatures universe_params universe_constraints constructors generated =
    let rec loop remaining generated =
      match remaining with
      | [] -> Ok generated
      | constructor :: rest ->
          bind
            (constructor_signature decl_index decl_interface_hash universe_params
               universe_constraints offset constructor)
            (fun signature -> loop rest (add_generated signature generated))
    in
    loop constructors generated
  in
  let collect_recursor_signature universe_constraints recursor generated =
    match recursor with
    | None -> Ok generated
    | Some recursor ->
        bind
          (recursor_signature decl_index decl_interface_hash universe_constraints offset
             recursor)
          (fun signature -> Ok (add_generated signature generated))
  in
  match declaration.Ext_cert.payload with
  | Ext_cert.InductiveDecl
      {
        decl_universe_params;
        decl_universe_constraints;
        ind_constructors;
        ind_recursor;
        _;
      } ->
      bind
        (collect_constructor_signatures decl_universe_params
           decl_universe_constraints ind_constructors [])
        (fun generated ->
          collect_recursor_signature decl_universe_constraints ind_recursor
            generated)
  | Ext_cert.MutualInductiveBlockDecl
      { decl_universe_params; decl_universe_constraints; mutual_inductives; _ } ->
      let rec loop remaining generated =
        match remaining with
        | [] -> Ok generated
        | mutual :: rest ->
            let family_sig =
              make_signature ~decl_interface_hash Ext_bytes.Declarations offset
                mutual.Ext_cert.mutual_name
                decl_universe_params decl_universe_constraints
                (pi_of_binders
                   (mutual.Ext_cert.mutual_params @ mutual.Ext_cert.mutual_indices)
                   (Ext_term.Sort mutual.Ext_cert.mutual_sort))
                No_unfolding
                (Local_generated { decl_index; name = mutual.Ext_cert.mutual_name })
            in
            bind family_sig (fun signature ->
                bind
                  (collect_constructor_signatures decl_universe_params
                     decl_universe_constraints
                     mutual.Ext_cert.mutual_constructors
                     (add_generated signature generated))
                  (fun generated ->
                    bind
                      (collect_recursor_signature decl_universe_constraints
                         mutual.Ext_cert.mutual_recursor generated)
                      (fun generated -> loop rest generated)))
      in
      loop mutual_inductives []
  | _ -> Ok []

let add_checked_declaration env (declaration : Ext_cert.declaration) =
  let decl_index = env.checked_declaration_count in
  let section = Ext_bytes.Declarations in
  let offset = declaration.Ext_cert.offset in
  bind
    (validate_universe_params section offset
       (declaration_universe_params declaration.Ext_cert.payload))
    (fun () ->
      bind (generated_signatures_of_declaration decl_index declaration) (fun generated ->
          match signature_of_declaration decl_index declaration with
          | Ok signature ->
              Ok
                {
                  env with
                  checked_declaration_count = decl_index + 1;
                  local_declarations =
                    (decl_index, declaration) :: env.local_declarations;
                  local_signatures = (decl_index, signature) :: env.local_signatures;
                  generated_signatures = generated @ env.generated_signatures;
                }
          | Error { reason = Unknown_reference; _ }
            when (match declaration.Ext_cert.payload with
            | Ext_cert.MutualInductiveBlockDecl _ -> true
            | _ -> false) ->
              Ok
                {
                  env with
                  checked_declaration_count = decl_index + 1;
                  local_declarations =
                    (decl_index, declaration) :: env.local_declarations;
                  generated_signatures = generated @ env.generated_signatures;
                }
          | Error err -> Error err))

let resolve_global_ref ?(section = Ext_bytes.Declarations) ?(offset = 0) env global_ref =
  match global_ref with
  | Ext_term.Builtin { name; decl_interface_hash } -> (
      match builtin_signature name decl_interface_hash with
      | None -> error section offset Unknown_reference
      | Some signature -> Ok signature)
  | Ext_term.Imported { import_index; name; decl_interface_hash } -> (
      match find_import import_index env.imports with
      | None -> error section offset Unknown_reference
      | Some import -> (
          let public_environment = import.Ext_import_store.resolved_public_environment in
          match
            find_public_export name decl_interface_hash
              public_environment.Ext_import_store.public_exports
          with
          | None -> error section offset Unknown_reference
          | Some export ->
              signature_of_public_export env import_index public_environment section offset
                export))
  | Ext_term.Local { decl_index } ->
      if decl_index >= env.checked_declaration_count then error section offset Unknown_reference
      else (
        match find_local_signature decl_index env.local_signatures with
        | None -> error section offset Unknown_reference
        | Some signature -> Ok signature)
  | Ext_term.LocalGenerated { decl_index; name } ->
      if decl_index >= env.checked_declaration_count then error section offset Unknown_reference
      else
        let key = { generated_decl_index = decl_index; generated_name = name } in
        match find_generated_signature key env.generated_signatures with
        | None -> error section offset Unknown_reference
        | Some signature -> Ok signature
