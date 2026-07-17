type error_reason =
  | Unknown_reference
  | Bad_universe_arity
  | Duplicate_universe_param
  | Unresolved_metavariable
  | Invalid_bvar
  | Expected_sort
  | Expected_function
  | Type_mismatch
  | Unsupported_declaration
  | Inductive_invalid
  | Positivity_failure
  | Noncanonical_universe_params
  | Noncanonical_universe_constraints
  | Duplicate_universe_constraint
  | Unsupported_universe_constraint
  | Unsatisfiable_universe_constraints
  | Universe_constraint_violation
  | Constructor_universe_bound_violation
  | Resource_limit

type error = {
  reason : error_reason;
  section : Ext_bytes.certificate_section;
  offset : Ext_bytes.offset;
}

type local_binding = {
  local_ty : Ext_term.t;
  local_value : Ext_term.t option;
}

type context = local_binding list

let max_fuel = 100_000

let empty_context = []

let push_assumption context ty = { local_ty = ty; local_value = None } :: context

let push_definition context ty value =
  { local_ty = ty; local_value = Some value } :: context

let error section offset reason = Error { reason; section; offset }

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let error_reason_code reason =
  match reason with
  | Unknown_reference -> "unknown_reference"
  | Bad_universe_arity -> "bad_universe_arity"
  | Duplicate_universe_param -> "duplicate_universe_param"
  | Unresolved_metavariable -> "unresolved_metavariable"
  | Invalid_bvar -> "invalid_bvar"
  | Expected_sort -> "expected_sort"
  | Expected_function -> "expected_function"
  | Type_mismatch -> "type_mismatch"
  | Unsupported_declaration -> "unsupported_declaration"
  | Inductive_invalid -> "inductive_invalid"
  | Positivity_failure -> "positivity_failure"
  | Noncanonical_universe_params -> "noncanonical_universe_params"
  | Noncanonical_universe_constraints -> "noncanonical_universe_constraints"
  | Duplicate_universe_constraint -> "duplicate_universe_constraint"
  | Unsupported_universe_constraint -> "unsupported_universe_constraint"
  | Unsatisfiable_universe_constraints -> "unsatisfiable_universe_constraints"
  | Universe_constraint_violation -> "universe_constraint_violation"
  | Constructor_universe_bound_violation ->
      "constructor_universe_bound_violation"
  | Resource_limit -> "resource_limit"

let error_kind error =
  match error.reason with
  | Bad_universe_arity | Duplicate_universe_param | Unresolved_metavariable ->
      "universe_inconsistency"
  | Noncanonical_universe_params | Noncanonical_universe_constraints ->
      "noncanonical_encoding"
  | Duplicate_universe_constraint | Unsupported_universe_constraint
  | Unsatisfiable_universe_constraints | Universe_constraint_violation
  | Constructor_universe_bound_violation ->
      "universe_inconsistency"
  | Unknown_reference | Invalid_bvar | Expected_sort | Expected_function | Type_mismatch
  | Unsupported_declaration ->
      "type_mismatch"
  | Inductive_invalid -> "inductive_invalid"
  | Positivity_failure -> "positivity_failure"
  | Resource_limit -> "conversion_failure"

let error_of_universe_error section offset (universe_error : Ext_universe.error) =
  let reason =
    match universe_error.Ext_universe.reason with
    | Ext_universe.Noncanonical_universe_params -> Noncanonical_universe_params
    | Ext_universe.Duplicate_universe_param -> Duplicate_universe_param
    | Ext_universe.Unresolved_metavariable -> Unresolved_metavariable
    | Ext_universe.Unknown_universe_param -> Unknown_reference
    | Ext_universe.Noncanonical_universe_constraints ->
        Noncanonical_universe_constraints
    | Ext_universe.Duplicate_universe_constraint -> Duplicate_universe_constraint
    | Ext_universe.Unsupported_universe_constraint -> Unsupported_universe_constraint
    | Ext_universe.Unsatisfiable_universe_constraints ->
        Unsatisfiable_universe_constraints
    | Ext_universe.Universe_constraint_violation -> Universe_constraint_violation
    | Ext_universe.Resource_limit -> Resource_limit
  in
  Error { reason; section; offset }

let error_of_env_error (env_error : Ext_env.error) =
  let reason =
    match env_error.Ext_env.reason with
    | Ext_env.Unknown_reference -> Unknown_reference
    | Ext_env.Duplicate_universe_param -> Duplicate_universe_param
  in
  Error
    {
      reason;
      section = env_error.Ext_env.section;
      offset = env_error.Ext_env.offset;
    }

let resolve_signature section offset env global_ref =
  match Ext_env.resolve_global_ref ~section ~offset env global_ref with
  | Ok signature -> Ok signature
  | Error env_error -> error_of_env_error env_error

let rec list_nth_opt index values =
  match (index, values) with
  | _, _ when index < 0 -> None
  | 0, value :: _ -> Some value
  | _, _ :: rest -> list_nth_opt (index - 1) rest
  | _, [] -> None

let spend_fuel section offset fuel =
  if !fuel = 0 then error section offset Resource_limit
  else (
    fuel := !fuel - 1;
    Ok ())

let spend_fuel_units section offset fuel units =
  if units < 0 || units > !fuel then error section offset Resource_limit
  else (
    fuel := !fuel - units;
    Ok ())

let capped_fuel_cost_add lhs rhs =
  let cap = max_fuel + 1 in
  if lhs >= cap || rhs >= cap || lhs > cap - rhs then cap else lhs + rhs

let capped_fuel_cost_mul lhs rhs =
  let cap = max_fuel + 1 in
  if lhs = 0 || rhs = 0 then 0
  else if lhs >= cap || rhs >= cap || lhs > cap / rhs then cap
  else lhs * rhs

let rec position_name name params =
  match params with
  | [] -> None
  | current :: rest ->
      if Ext_name.equal current name then Some 0
      else (
        match position_name name rest with
        | None -> None
        | Some index -> Some (index + 1))

let rec ensure_level_wf section offset delta level =
  match level with
  | Ext_level.Zero -> Ok ()
  | Ext_level.Succ inner -> ensure_level_wf section offset delta inner
  | Ext_level.Max (lhs, rhs) | Ext_level.Imax (lhs, rhs) ->
      bind (ensure_level_wf section offset delta lhs) (fun () ->
          ensure_level_wf section offset delta rhs)
  | Ext_level.Param name ->
      if Ext_level.component_contains_universe_meta name then
        error section offset Unresolved_metavariable
      else if position_name name delta <> None then Ok ()
      else error section offset Unknown_reference

let rec subst_level params levels level =
  match level with
  | Ext_level.Zero -> Ext_level.Zero
  | Ext_level.Succ inner -> Ext_level.Succ (subst_level params levels inner)
  | Ext_level.Max (lhs, rhs) ->
      Ext_level.Max (subst_level params levels lhs, subst_level params levels rhs)
  | Ext_level.Imax (lhs, rhs) ->
      Ext_level.Imax (subst_level params levels lhs, subst_level params levels rhs)
  | Ext_level.Param name -> (
      match position_name name params with
      | None -> Ext_level.Param name
      | Some index -> (
          match list_nth_opt index levels with
          | None -> Ext_level.Param name
          | Some level -> level))

let rec subst_levels_term params levels term =
  match term with
  | Ext_term.Sort level -> Ext_term.Sort (subst_level params levels level)
  | Ext_term.BVar _ -> term
  | Ext_term.Const (global_ref, term_levels) ->
      Ext_term.Const (global_ref, List.map (subst_level params levels) term_levels)
  | Ext_term.App (fn, arg) ->
      Ext_term.App (subst_levels_term params levels fn, subst_levels_term params levels arg)
  | Ext_term.Lam (ty, body) ->
      Ext_term.Lam (subst_levels_term params levels ty, subst_levels_term params levels body)
  | Ext_term.Pi (ty, body) ->
      Ext_term.Pi (subst_levels_term params levels ty, subst_levels_term params levels body)
  | Ext_term.Let (ty, value, body) ->
      Ext_term.Let
        ( subst_levels_term params levels ty,
          subst_levels_term params levels value,
          subst_levels_term params levels body )

let rec shift_at section offset term amount cutoff =
  match term with
  | Ext_term.Sort _ | Ext_term.Const _ -> Ok term
  | Ext_term.BVar index ->
      if index < 0 then error section offset Invalid_bvar
      else if index < cutoff then Ok term
      else
        let shifted = index + amount in
        if shifted < 0 then error section offset Invalid_bvar
        else Ok (Ext_term.BVar shifted)
  | Ext_term.App (fn, arg) ->
      bind (shift_at section offset fn amount cutoff) (fun shifted_fn ->
          bind (shift_at section offset arg amount cutoff) (fun shifted_arg ->
              Ok (Ext_term.App (shifted_fn, shifted_arg))))
  | Ext_term.Lam (ty, body) ->
      bind (shift_at section offset ty amount cutoff) (fun shifted_ty ->
          bind (shift_at section offset body amount (cutoff + 1)) (fun shifted_body ->
              Ok (Ext_term.Lam (shifted_ty, shifted_body))))
  | Ext_term.Pi (ty, body) ->
      bind (shift_at section offset ty amount cutoff) (fun shifted_ty ->
          bind (shift_at section offset body amount (cutoff + 1)) (fun shifted_body ->
              Ok (Ext_term.Pi (shifted_ty, shifted_body))))
  | Ext_term.Let (ty, value, body) ->
      bind (shift_at section offset ty amount cutoff) (fun shifted_ty ->
          bind (shift_at section offset value amount cutoff) (fun shifted_value ->
              bind (shift_at section offset body amount (cutoff + 1)) (fun shifted_body ->
                  Ok (Ext_term.Let (shifted_ty, shifted_value, shifted_body)))))

let shift section offset term amount cutoff =
  if cutoff < 0 then error section offset Invalid_bvar
  else shift_at section offset term amount cutoff

let rec substitute_at section offset term target replacement =
  match term with
  | Ext_term.Sort _ | Ext_term.Const _ -> Ok term
  | Ext_term.BVar index ->
      if index < 0 then error section offset Invalid_bvar
      else if index = target then shift section offset replacement target 0
      else if index > target then Ok (Ext_term.BVar (index - 1))
      else Ok term
  | Ext_term.App (fn, arg) ->
      bind (substitute_at section offset fn target replacement) (fun substituted_fn ->
          bind (substitute_at section offset arg target replacement) (fun substituted_arg ->
              Ok (Ext_term.App (substituted_fn, substituted_arg))))
  | Ext_term.Lam (ty, body) ->
      bind (substitute_at section offset ty target replacement) (fun substituted_ty ->
          bind (substitute_at section offset body (target + 1) replacement)
            (fun substituted_body -> Ok (Ext_term.Lam (substituted_ty, substituted_body))))
  | Ext_term.Pi (ty, body) ->
      bind (substitute_at section offset ty target replacement) (fun substituted_ty ->
          bind (substitute_at section offset body (target + 1) replacement)
            (fun substituted_body -> Ok (Ext_term.Pi (substituted_ty, substituted_body))))
  | Ext_term.Let (ty, value, body) ->
      bind (substitute_at section offset ty target replacement) (fun substituted_ty ->
          bind (substitute_at section offset value target replacement) (fun substituted_value ->
              bind (substitute_at section offset body (target + 1) replacement)
                (fun substituted_body ->
                  Ok (Ext_term.Let (substituted_ty, substituted_value, substituted_body)))))

let substitute section offset term target replacement =
  if target < 0 then error section offset Invalid_bvar
  else substitute_at section offset term target replacement

let instantiate section offset body value = substitute section offset body 0 value

let lookup_binding section offset context index =
  match list_nth_opt index context with
  | Some binding -> Ok binding
  | None -> error section offset Invalid_bvar

let lookup_type section offset context index =
  bind (lookup_binding section offset context index) (fun binding ->
      shift section offset binding.local_ty (index + 1) 0)

let lookup_value section offset context index =
  bind (lookup_binding section offset context index) (fun binding ->
      match binding.local_value with
      | None -> Ok None
      | Some value ->
          bind (shift section offset value (index + 1) 0) (fun shifted ->
              Ok (Some shifted)))

let levels_equal lhs rhs =
  List.length lhs = List.length rhs
  && List.for_all2
       (fun left right -> Ext_level.normalize left = Ext_level.normalize right)
       lhs rhs

let imported_std_logic_eq_ref_matches_builtin env import_index imported_name
    imported_hash builtin_name builtin_hash =
  Ext_name.equal imported_name builtin_name
  && (match Ext_name.to_string builtin_name with
     | "Eq" | "Eq.refl" | "Eq.rec" -> true
     | _ -> false)
  && Ext_env.builtin_decl_interface_hash builtin_name = Some builtin_hash
  &&
  match Ext_env.find_import import_index env.Ext_env.imports with
  | None -> false
  | Some import ->
      Ext_name.to_string import.Ext_import_store.resolved_module_name = "Std.Logic.Eq"
      &&
      (match
         Ext_env.find_public_export imported_name imported_hash
           import.Ext_import_store.resolved_public_environment.public_exports
       with
      | Some _ -> true
      | None -> false)

let global_ref_equal env left right =
  match (left, right) with
  | ( Ext_term.Imported
        {
          import_index = left_import;
          name = left_name;
          decl_interface_hash = left_hash;
        },
      Ext_term.Imported
        {
          import_index = right_import;
          name = right_name;
          decl_interface_hash = right_hash;
        } ) ->
      left_import = right_import && Ext_name.equal left_name right_name && left_hash = right_hash
  | Ext_term.Local { decl_index = left_index }, Ext_term.Local { decl_index = right_index } ->
      left_index = right_index
  | ( Ext_term.LocalGenerated { decl_index = left_index; name = left_name },
      Ext_term.LocalGenerated { decl_index = right_index; name = right_name } ) ->
      left_index = right_index && Ext_name.equal left_name right_name
  | ( Ext_term.Builtin { name = left_name; decl_interface_hash = left_hash },
      Ext_term.Builtin { name = right_name; decl_interface_hash = right_hash } ) ->
      Ext_name.equal left_name right_name && left_hash = right_hash
  | ( Ext_term.Imported
        {
          import_index;
          name = imported_name;
          decl_interface_hash = imported_hash;
        },
      Ext_term.Builtin
        { name = builtin_name; decl_interface_hash = builtin_hash } )
  | ( Ext_term.Builtin
        { name = builtin_name; decl_interface_hash = builtin_hash },
      Ext_term.Imported
        {
          import_index;
          name = imported_name;
          decl_interface_hash = imported_hash;
        } ) ->
      imported_std_logic_eq_ref_matches_builtin env import_index imported_name
        imported_hash builtin_name builtin_hash
  | _ -> false

let collect_apps term =
  let rec loop current args =
    match current with
    | Ext_term.App (fn, arg) -> loop fn (arg :: args)
    | _ -> (current, args)
  in
  loop term []

let peel_pi_domains term =
  let rec loop domains current =
    match current with
    | Ext_term.Pi (domain, body) -> loop (domain :: domains) body
    | _ -> (List.rev domains, current)
  in
  loop [] term

let rec apply_args fn args =
  match args with
  | [] -> fn
  | arg :: rest -> apply_args (Ext_term.App (fn, arg)) rest

let rec take count values =
  if count <= 0 then []
  else
    match values with
    | [] -> []
    | value :: rest -> value :: take (count - 1) rest

let rec drop count values =
  if count <= 0 then values
  else
    match values with
    | [] -> []
    | _ :: rest -> drop (count - 1) rest

let rec find_index predicate values =
  let rec loop index remaining =
    match remaining with
    | [] -> None
    | value :: rest -> if predicate value then Some index else loop (index + 1) rest
  in
  loop 0 values

let builtin_name_is dotted global_ref =
  match global_ref with
  | Ext_term.Builtin { name; _ } -> Ext_name.to_string name = dotted
  | _ -> false

let rec instantiate_constructor_args_at section offset term args_by_abs depth =
  match term with
  | Ext_term.Sort _ | Ext_term.Const _ -> Ok term
  | Ext_term.BVar index ->
      if index < depth then Ok term
      else
        let outer_index = index - depth in
        let source_abs = List.length args_by_abs - 1 - outer_index in
        (match list_nth_opt source_abs args_by_abs with
        | None -> error section offset Invalid_bvar
        | Some arg -> shift section offset arg depth 0)
  | Ext_term.App (fn, arg) ->
      bind
        (instantiate_constructor_args_at section offset fn args_by_abs depth)
        (fun fn ->
          bind
            (instantiate_constructor_args_at section offset arg args_by_abs depth)
            (fun arg -> Ok (Ext_term.App (fn, arg))))
  | Ext_term.Lam (ty, body) ->
      bind
        (instantiate_constructor_args_at section offset ty args_by_abs depth)
        (fun ty ->
          bind
            (instantiate_constructor_args_at section offset body args_by_abs
               (depth + 1))
            (fun body -> Ok (Ext_term.Lam (ty, body))))
  | Ext_term.Pi (ty, body) ->
      bind
        (instantiate_constructor_args_at section offset ty args_by_abs depth)
        (fun ty ->
          bind
            (instantiate_constructor_args_at section offset body args_by_abs
               (depth + 1))
            (fun body -> Ok (Ext_term.Pi (ty, body))))
  | Ext_term.Let (ty, value, body) ->
      bind
        (instantiate_constructor_args_at section offset ty args_by_abs depth)
        (fun ty ->
          bind
            (instantiate_constructor_args_at section offset value args_by_abs
               depth)
            (fun value ->
              bind
                (instantiate_constructor_args_at section offset body args_by_abs
                   (depth + 1))
                (fun body -> Ok (Ext_term.Let (ty, value, body)))))

let instantiate_constructor_args section offset term args_by_abs =
  instantiate_constructor_args_at section offset term args_by_abs 0

let imported_recursor_iota_hook =
  ref
    (fun (_env : Ext_env.t) (_context : context)
         (_section : Ext_bytes.certificate_section) (_offset : Ext_bytes.offset)
         (_delta : Ext_name.t list) (_term : Ext_term.t) (_fuel : int ref) ->
      Ok None)

let rec whnf_with_fuel env context section offset delta term fuel =
  bind (spend_fuel section offset fuel) (fun () ->
      match term with
      | Ext_term.BVar index ->
          bind (lookup_value section offset context index) (function
            | None -> Ok term
            | Some value -> whnf_with_fuel env context section offset delta value fuel)
      | Ext_term.Const (global_ref, levels) ->
          bind (resolve_signature section offset env global_ref) (fun signature ->
              if
                List.length signature.Ext_env.signature_universe_params
                <> List.length levels
              then error section offset Bad_universe_arity
              else
                match signature.Ext_env.signature_unfolding with
                | Ext_env.Reducible value ->
                    let value =
                      subst_levels_term signature.Ext_env.signature_universe_params levels value
                    in
                    whnf_with_fuel env context section offset delta value fuel
                | Ext_env.No_unfolding | Ext_env.Opaque -> Ok term)
      | Ext_term.App (fn, arg) ->
          bind (whnf_with_fuel env context section offset delta fn fuel) (function
            | Ext_term.Lam (_, body) ->
                bind (instantiate section offset body arg) (fun instantiated ->
                    whnf_with_fuel env context section offset delta instantiated fuel)
            | whnf_fn ->
                let app = Ext_term.App (whnf_fn, arg) in
                bind
                  (reduce_nat_rec_iota env context section offset delta app fuel)
                  (function
                    | Some reduced ->
                        whnf_with_fuel env context section offset delta reduced fuel
                    | None ->
                        bind
                          (reduce_local_recursor_iota env context section offset delta
                             app fuel)
                          (function
                            | None ->
                                bind
                                  (!imported_recursor_iota_hook env context section
                                     offset delta app fuel)
                                  (function
                                    | None -> Ok app
                                    | Some reduced ->
                                        whnf_with_fuel env context section offset delta
                                          reduced fuel)
                            | Some reduced ->
                                whnf_with_fuel env context section offset delta reduced
                                  fuel)))
      | Ext_term.Let (_, value, body) ->
          bind (instantiate section offset body value) (fun instantiated ->
              whnf_with_fuel env context section offset delta instantiated fuel)
      | Ext_term.Sort _ | Ext_term.Lam _ | Ext_term.Pi _ -> Ok term)

and reduce_nat_rec_iota env context section offset delta term fuel =
  let head, args = collect_apps term in
  match head with
  | Ext_term.Const (global_ref, levels) when builtin_name_is "Nat.rec" global_ref -> (
      match args with
      | motive :: z_case :: s_case :: major :: rest ->
          bind
            (whnf_with_fuel env context section offset delta major fuel)
            (fun major_whnf ->
              let ctor_head, ctor_args = collect_apps major_whnf in
              match ctor_head with
              | Ext_term.Const (zero_ref, _) when builtin_name_is "Nat.zero" zero_ref ->
                  if ctor_args = [] then Ok (Some (apply_args z_case rest))
                  else Ok None
              | Ext_term.Const (succ_ref, _) when builtin_name_is "Nat.succ" succ_ref -> (
                  match ctor_args with
                  | [ predecessor ] ->
                      let recursor =
                        apply_args
                          (Ext_term.Const (global_ref, levels))
                          [ motive; z_case; s_case; predecessor ]
                      in
                      let reduced = apply_args s_case [ predecessor; recursor ] in
                      Ok (Some (apply_args reduced rest))
                  | _ -> Ok None)
              | _ -> Ok None)
      | _ -> Ok None)
  | _ -> Ok None

and reduce_local_recursor_iota env context section offset delta term fuel =
  let head, args = collect_apps term in
  match head with
  | Ext_term.Const
      ( Ext_term.LocalGenerated { decl_index; name = recursor_name },
        recursor_levels ) -> (
      match Ext_env.find_local_declaration decl_index env.Ext_env.local_declarations with
      | None -> Ok None
      | Some declaration -> (
          match declaration.Ext_cert.payload with
          | Ext_cert.InductiveDecl
              {
                decl_universe_params;
                ind_params;
                ind_indices;
                ind_constructors;
                ind_recursor = Some recursor;
                _;
              } ->
              if
                not
                  (Ext_name.equal recursor.Ext_cert.recursor_name
                     recursor_name)
              then Ok None
              else (
              let major_index = recursor.Ext_cert.recursor_rules.major_index in
              let minor_start = recursor.Ext_cert.recursor_rules.minor_start in
              if List.length args <= major_index then Ok None
              else
                match list_nth_opt major_index args with
                | None -> Ok None
                | Some major ->
                    bind
                      (whnf_with_fuel env context section offset delta major fuel)
                      (fun major_whnf ->
                        let ctor_head, ctor_args = collect_apps major_whnf in
                        match ctor_head with
                        | Ext_term.Const
                            ( Ext_term.LocalGenerated
                                {
                                  decl_index = ctor_decl_index;
                                  name = constructor_name;
                                },
                              _ )
                          when ctor_decl_index = decl_index -> (
                            match
                              find_index
                                (fun constructor ->
                                  Ext_name.equal
                                    constructor.Ext_cert.constructor_name
                                    constructor_name)
                                ind_constructors
                            with
                            | None -> Ok None
                            | Some constructor_index -> (
                                match
                                  ( list_nth_opt
                                      (minor_start + constructor_index)
                                      args,
                                    list_nth_opt constructor_index
                                      ind_constructors )
                                with
                                | Some minor, Some constructor ->
                                    let domains, _ =
                                      peel_pi_domains
                                        constructor.Ext_cert.constructor_ty
                                    in
                                    let param_count = List.length ind_params in
                                    let field_domains =
                                      drop param_count domains
                                    in
                                    let field_args = drop param_count ctor_args in
                                    if
                                      List.length field_args
                                      < List.length field_domains
                                    then Ok None
                                    else
                                      let family =
                                        Ext_inductive.family ~decl_index
                                          ~universe_params:decl_universe_params
                                          ~param_count
                                          ~index_count:(List.length ind_indices)
                                      in
                                      let index_start =
                                        major_index - List.length ind_indices
                                      in
                                      let rec loop field_index current
                                          remaining_args remaining_domains =
                                        match
                                          (remaining_args, remaining_domains)
                                        with
                                        | _, [] -> Ok current
                                        | ( field_arg :: rest_args,
                                            field_domain :: rest_domains ) ->
                                            let applied =
                                              Ext_term.App (current, field_arg)
                                            in
                                            (match
                                               Ext_inductive.direct_recursive_index_args
                                                 family field_domain
                                                 (param_count + field_index)
                                             with
                                            | Some recursive_indices ->
                                              let source_ctx_len =
                                                param_count + field_index
                                              in
                                              let source_args =
                                                take source_ctx_len ctor_args
                                              in
                                              let rec instantiate_indices
                                                  remaining instantiated =
                                                match remaining with
                                                | [] -> Ok (List.rev instantiated)
                                                | index_arg :: index_rest ->
                                                    bind
                                                      (instantiate_constructor_args
                                                         section offset index_arg
                                                         source_args)
                                                      (fun instantiated_arg ->
                                                        instantiate_indices
                                                          index_rest
                                                          (instantiated_arg
                                                          :: instantiated))
                                              in
                                              bind
                                                (instantiate_indices
                                                   recursive_indices [])
                                                (fun recursive_indices ->
                                              let recursive_args =
                                                take index_start args
                                                @ recursive_indices @ [ field_arg ]
                                              in
                                              let recursive_call =
                                                apply_args
                                                  (Ext_term.Const
                                                     ( Ext_term.LocalGenerated
                                                         {
                                                           decl_index;
                                                           name =
                                                             recursor_name;
                                                         },
                                                       recursor_levels ))
                                                  recursive_args
                                              in
                                              loop (field_index + 1)
                                                (Ext_term.App
                                                   (applied, recursive_call))
                                                rest_args rest_domains)
                                            | None ->
                                              loop (field_index + 1) applied
                                                rest_args rest_domains)
                                        | [], _ :: _ -> Ok current
                                      in
                                      bind
                                        (loop 0 minor field_args field_domains)
                                        (fun reduced ->
                                          Ok
                                            (Some
                                               (apply_args reduced
                                                  (drop (major_index + 1)
                                                     args))))
                                | _ -> Ok None))
                        | _ -> Ok None))
          | Ext_cert.MutualInductiveBlockDecl
              {
                decl_universe_params;
                mutual_inductives;
                _;
              } ->
              reduce_mutual_recursor_iota env context section offset delta fuel
                decl_index recursor_name recursor_levels decl_universe_params
                mutual_inductives args
          | _ -> Ok None))
  | _ -> Ok None

and reduce_mutual_recursor_iota env context section offset delta fuel decl_index
    recursor_name recursor_levels decl_universe_params mutuals args =
  let rec find_target index remaining =
    match remaining with
    | [] -> None
    | mutual :: rest -> (
        match mutual.Ext_cert.mutual_recursor with
        | Some recursor
          when Ext_name.equal recursor.Ext_cert.recursor_name recursor_name ->
            Some (index, mutual, recursor)
        | _ -> find_target (index + 1) rest)
  in
  let rec find_constructor family_index constructor_offset remaining name =
    match remaining with
    | [] -> None
    | mutual :: rest -> (
        match
          find_index
            (fun constructor ->
              Ext_name.equal constructor.Ext_cert.constructor_name name)
            mutual.Ext_cert.mutual_constructors
        with
        | Some local_index ->
            (match
               list_nth_opt local_index mutual.Ext_cert.mutual_constructors
             with
            | None -> None
            | Some constructor ->
                Some
                  ( family_index,
                    constructor_offset + local_index,
                    mutual,
                    constructor ))
        | None ->
            find_constructor (family_index + 1)
              (constructor_offset
              + List.length mutual.Ext_cert.mutual_constructors)
              rest name)
  in
  match find_target 0 mutuals with
  | None -> Ok None
  | Some (_, target, recursor) ->
      let major_index = recursor.Ext_cert.recursor_rules.major_index in
      let minor_start = recursor.Ext_cert.recursor_rules.minor_start in
      if List.length args <= major_index then Ok None
      else
        match list_nth_opt major_index args with
        | None -> Ok None
        | Some major ->
            bind
              (whnf_with_fuel env context section offset delta major fuel)
              (fun major_whnf ->
                let ctor_head, ctor_args = collect_apps major_whnf in
                match ctor_head with
                | Ext_term.Const
                    ( Ext_term.LocalGenerated
                        {
                          decl_index = ctor_decl_index;
                          name = constructor_name;
                        },
                      _ )
                  when ctor_decl_index = decl_index -> (
                    match
                      find_constructor 0 0 mutuals constructor_name
                    with
                    | None -> Ok None
                    | Some
                        ( _, constructor_index, owner, constructor ) -> (
                        match
                          list_nth_opt (minor_start + constructor_index) args
                        with
                        | None -> Ok None
                        | Some minor ->
                            let domains, _ =
                              peel_pi_domains
                                constructor.Ext_cert.constructor_ty
                            in
                            let param_count =
                              List.length owner.Ext_cert.mutual_params
                            in
                            let field_domains = drop param_count domains in
                            let field_args = drop param_count ctor_args in
                            if
                              List.length field_args < List.length field_domains
                            then Ok None
                            else
                              let families =
                                List.map
                                  (fun mutual ->
                                    Ext_inductive.named_family
                                      ~name:mutual.Ext_cert.mutual_name
                                      ~decl_index
                                      ~universe_params:decl_universe_params
                                      ~param_count:
                                        (List.length
                                           mutual.Ext_cert.mutual_params)
                                      ~index_count:
                                        (List.length
                                           mutual.Ext_cert.mutual_indices))
                                  mutuals
                              in
                              let index_start =
                                major_index
                                - List.length target.Ext_cert.mutual_indices
                              in
                              let rec loop field_index current remaining_args
                                  remaining_domains =
                                match (remaining_args, remaining_domains) with
                                | _, [] -> Ok current
                                | ( field_arg :: rest_args,
                                    field_domain :: rest_domains ) ->
                                    let applied =
                                      Ext_term.App (current, field_arg)
                                    in
                                    (match
                                       Ext_inductive
                                       .direct_mutual_recursive_index_args
                                         families field_domain
                                         (param_count + field_index)
                                     with
                                    | None ->
                                        loop (field_index + 1) applied rest_args
                                          rest_domains
                                    | Some
                                        ( field_family_index,
                                          recursive_indices ) -> (
                                        match
                                          list_nth_opt field_family_index mutuals
                                        with
                                        | None -> Ok current
                                        | Some recursive_family -> (
                                            match
                                              recursive_family.Ext_cert
                                              .mutual_recursor
                                            with
                                            | None -> Ok current
                                            | Some recursive_recursor ->
                                                let source_ctx_len =
                                                  param_count + field_index
                                                in
                                                let source_args =
                                                  take source_ctx_len ctor_args
                                                in
                                                let rec instantiate_indices
                                                    remaining instantiated =
                                                  match remaining with
                                                  | [] ->
                                                      Ok (List.rev instantiated)
                                                  | index_arg :: rest ->
                                                      bind
                                                        (instantiate_constructor_args
                                                           section offset
                                                           index_arg source_args)
                                                        (fun instantiated_arg ->
                                                          instantiate_indices
                                                            rest
                                                            (instantiated_arg
                                                            :: instantiated))
                                                in
                                                bind
                                                  (instantiate_indices
                                                     recursive_indices [])
                                                  (fun recursive_indices ->
                                                    let recursive_args =
                                                      take index_start args
                                                      @ recursive_indices
                                                      @ [ field_arg ]
                                                    in
                                                    let recursive_call =
                                                      apply_args
                                                        (Ext_term.Const
                                                           ( Ext_term
                                                             .LocalGenerated
                                                               {
                                                                 decl_index;
                                                                 name =
                                                                   recursive_recursor
                                                                   .Ext_cert
                                                                   .recursor_name;
                                                               },
                                                             recursor_levels ))
                                                        recursive_args
                                                    in
                                                    loop (field_index + 1)
                                                      (Ext_term.App
                                                         ( applied,
                                                           recursive_call ))
                                                      rest_args rest_domains))))
                                | [], _ :: _ -> Ok current
                              in
                              bind
                                (loop 0 minor field_args field_domains)
                                (fun reduced ->
                                  Ok
                                    (Some
                                       (apply_args reduced
                                          (drop (major_index + 1) args))))))
                | _ -> Ok None)

let whnf ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = []) env context term =
  let fuel = ref max_fuel in
  whnf_with_fuel env context section offset delta term fuel

let whnf_with_fuel_budget ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = [])
    ~fuel_budget env context term =
  if fuel_budget < 0 then error section offset Resource_limit
  else
    let fuel = ref fuel_budget in
    whnf_with_fuel env context section offset delta term fuel

let rec is_defeq_with_fuel env context section offset delta lhs rhs fuel =
  bind (spend_fuel section offset fuel) (fun () ->
      bind (whnf_with_fuel env context section offset delta lhs fuel) (fun lhs_whnf ->
          bind (whnf_with_fuel env context section offset delta rhs fuel) (fun rhs_whnf ->
              match (lhs_whnf, rhs_whnf) with
              | Ext_term.Sort lhs_level, Ext_term.Sort rhs_level ->
                  Ok (Ext_level.normalize lhs_level = Ext_level.normalize rhs_level)
              | Ext_term.BVar lhs_index, Ext_term.BVar rhs_index -> Ok (lhs_index = rhs_index)
              | ( Ext_term.Const (lhs_ref, lhs_levels),
                  Ext_term.Const (rhs_ref, rhs_levels) ) ->
                  Ok
                    (levels_equal lhs_levels rhs_levels
                    && global_ref_equal env lhs_ref rhs_ref)
              | Ext_term.App (lhs_fn, lhs_arg), Ext_term.App (rhs_fn, rhs_arg) ->
                  bind
                    (is_defeq_with_fuel env context section offset delta lhs_fn rhs_fn fuel)
                    (fun fn_equal ->
                      if not fn_equal then Ok false
                      else
                        is_defeq_with_fuel env context section offset delta lhs_arg rhs_arg
                          fuel)
              | Ext_term.Pi (lhs_ty, lhs_body), Ext_term.Pi (rhs_ty, rhs_body) ->
                  bind
                    (is_defeq_with_fuel env context section offset delta lhs_ty rhs_ty fuel)
                    (fun ty_equal ->
                      if not ty_equal then Ok false
                      else
                        let body_context = push_assumption context lhs_ty in
                        is_defeq_with_fuel env body_context section offset delta lhs_body
                          rhs_body fuel)
              | Ext_term.Lam (lhs_ty, lhs_body), Ext_term.Lam (rhs_ty, rhs_body) ->
                  bind
                    (is_defeq_with_fuel env context section offset delta lhs_ty rhs_ty fuel)
                    (fun ty_equal ->
                      if not ty_equal then Ok false
                      else
                        let body_context = push_assumption context lhs_ty in
                        is_defeq_with_fuel env body_context section offset delta lhs_body
                          rhs_body fuel)
              | ( Ext_term.Let (lhs_ty, lhs_value, lhs_body),
                  Ext_term.Let (rhs_ty, rhs_value, rhs_body) ) ->
                  bind
                    (is_defeq_with_fuel env context section offset delta lhs_ty rhs_ty fuel)
                    (fun ty_equal ->
                      if not ty_equal then Ok false
                      else
                        bind
                          (is_defeq_with_fuel env context section offset delta lhs_value
                             rhs_value fuel)
                          (fun value_equal ->
                            if not value_equal then Ok false
                            else
                              let body_context =
                                push_definition context lhs_ty lhs_value
                              in
                              is_defeq_with_fuel env body_context section offset delta
                                lhs_body rhs_body fuel))
              | _ -> Ok false)))

let is_defeq ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = []) env context lhs
    rhs =
  let fuel = ref max_fuel in
  is_defeq_with_fuel env context section offset delta lhs rhs fuel

let is_defeq_with_fuel_budget ?(section = Ext_bytes.Declarations) ?(offset = 0)
    ?(delta = []) ~fuel_budget env context lhs rhs =
  if fuel_budget < 0 then error section offset Resource_limit
  else
    let fuel = ref fuel_budget in
    is_defeq_with_fuel env context section offset delta lhs rhs fuel

let rec infer ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = [])
    ?(universe_context = Ext_universe.empty) ?(fuel = ref max_fuel) env context term =
  match term with
  | Ext_term.Sort level ->
      bind (ensure_level_wf section offset delta level) (fun () ->
          Ok (Ext_term.Sort (Ext_level.Succ level)))
  | Ext_term.BVar index -> lookup_type section offset context index
  | Ext_term.Const (global_ref, levels) ->
      let rec ensure_levels remaining =
        match remaining with
        | [] -> Ok ()
        | level :: rest ->
            bind (ensure_level_wf section offset delta level) (fun () ->
                ensure_levels rest)
      in
      bind (ensure_levels levels) (fun () ->
          bind (resolve_signature section offset env global_ref) (fun signature ->
              if
                List.length signature.Ext_env.signature_universe_params
                <> List.length levels
              then error section offset Bad_universe_arity
              else
                (match
                   Ext_universe.substitute_constraints
                     signature.Ext_env.signature_universe_params levels
                     signature.Ext_env.signature_universe_constraints
                 with
                | Error universe_error ->
                    error_of_universe_error section offset universe_error
                | Ok obligations -> (
                    match
                      Ext_universe.entails_constraints universe_context obligations
                    with
                    | Error universe_error ->
                        error_of_universe_error section offset universe_error
                    | Ok () ->
                        Ok
                          (subst_levels_term
                             signature.Ext_env.signature_universe_params levels
                             signature.Ext_env.signature_ty)))))
  | Ext_term.Pi (ty, body) ->
      bind
        (expect_sort ~section ~offset ~delta ~universe_context ~fuel env context ty)
        (fun domain_sort ->
          let body_context = push_assumption context ty in
          bind
            (expect_sort ~section ~offset ~delta ~universe_context ~fuel env
               body_context body)
            (fun body_sort -> Ok (Ext_term.Sort (Ext_level.Imax (domain_sort, body_sort)))))
  | Ext_term.Lam (ty, body) ->
      bind
        (expect_sort ~section ~offset ~delta ~universe_context ~fuel env context ty)
        (fun _ ->
          let body_context = push_assumption context ty in
          bind
            (infer ~section ~offset ~delta ~universe_context ~fuel env body_context
               body)
            (fun body_ty -> Ok (Ext_term.Pi (ty, body_ty))))
  | Ext_term.App (fn, arg) ->
      bind
        (infer ~section ~offset ~delta ~universe_context ~fuel env context fn)
        (fun fn_ty ->
          bind
            (whnf_with_fuel env context section offset delta fn_ty fuel)
            (function
            | Ext_term.Pi (domain_ty, body_ty) ->
                bind
                  (check ~section ~offset ~delta ~universe_context ~fuel env context
                     arg domain_ty)
                  (fun () -> instantiate section offset body_ty arg)
            | _ -> error section offset Expected_function))
  | Ext_term.Let (ty, value, body) ->
      bind
        (expect_sort ~section ~offset ~delta ~universe_context ~fuel env context ty)
        (fun _ ->
          bind
            (check ~section ~offset ~delta ~universe_context ~fuel env context value
               ty)
            (fun () ->
              let body_context = push_definition context ty value in
              bind
                (infer ~section ~offset ~delta ~universe_context ~fuel env
                   body_context body)
                (fun body_ty -> instantiate section offset body_ty value)))

and check ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = [])
    ?(universe_context = Ext_universe.empty) ?(fuel = ref max_fuel) env context term
    expected =
  match term with
  | Ext_term.Lam (ty, body) ->
      bind
        (whnf_with_fuel env context section offset delta expected fuel)
        (function
        | Ext_term.Pi (expected_ty, expected_body) ->
            bind
              (expect_sort ~section ~offset ~delta ~universe_context ~fuel env context
                 ty)
              (fun _ ->
                bind
                  (is_defeq_with_fuel env context section offset delta ty expected_ty
                     fuel)
                  (fun domain_equal ->
                    if not domain_equal then error section offset Type_mismatch
                    else
                      let body_context = push_assumption context ty in
                      check ~section ~offset ~delta ~universe_context ~fuel env
                        body_context body expected_body))
        | _ -> error section offset Type_mismatch)
  | _ ->
      bind
        (infer ~section ~offset ~delta ~universe_context ~fuel env context term)
        (fun actual ->
          bind
            (is_defeq_with_fuel env context section offset delta actual expected fuel)
            (fun equal ->
              if equal then Ok () else error section offset Type_mismatch))

and expect_sort ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = [])
    ?(universe_context = Ext_universe.empty) ?(fuel = ref max_fuel) env context term =
  bind
    (infer ~section ~offset ~delta ~universe_context ~fuel env context term)
    (fun ty ->
      bind
        (whnf_with_fuel env context section offset delta ty fuel)
        (function
        | Ext_term.Sort level -> Ok level
        | _ -> error section offset Expected_sort))

let declaration_universe_constraints payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_universe_constraints; _ }
  | Ext_cert.DefDecl { decl_universe_constraints; _ }
  | Ext_cert.TheoremDecl { decl_universe_constraints; _ }
  | Ext_cert.InductiveDecl { decl_universe_constraints; _ }
  | Ext_cert.MutualInductiveBlockDecl { decl_universe_constraints; _ } ->
      decl_universe_constraints

let check_dependency section offset env (dependency : Ext_cert.dependency_entry) =
  bind
    (resolve_signature section offset env dependency.Ext_cert.dependency_global_ref)
    (fun signature ->
      match signature.Ext_env.signature_decl_interface_hash with
      | Some hash when hash = dependency.Ext_cert.dependency_decl_interface_hash -> Ok ()
      | _ -> error section offset Type_mismatch)

let rec check_dependencies section offset env dependencies =
  match dependencies with
  | [] -> Ok ()
  | dependency :: rest ->
      bind (check_dependency section offset env dependency) (fun () ->
          check_dependencies section offset env rest)

let add_checked_declaration env declaration =
  match Ext_env.add_checked_declaration env declaration with
  | Ok env -> Ok env
  | Error env_error -> error_of_env_error env_error

let rec names_equal lhs rhs =
  match (lhs, rhs) with
  | [], [] -> true
  | left :: left_rest, right :: right_rest ->
      Ext_name.equal left right && names_equal left_rest right_rest
  | _ -> false

let rec has_name name names =
  match names with
  | [] -> false
  | current :: rest -> Ext_name.equal current name || has_name name rest

let ensure_constructor_names_unique section offset family_name constructors =
  let rec loop seen remaining =
    match remaining with
    | [] -> Ok ()
    | constructor :: rest ->
        let constructor_name = constructor.Ext_cert.constructor_name in
        if
          Ext_name.equal constructor_name family_name
          || has_name constructor_name seen
        then error section offset Inductive_invalid
        else loop (constructor_name :: seen) rest
  in
  loop [] constructors

let universe_param_levels delta =
  List.map (fun name -> Ext_level.Param name) delta

let check_constructor_result_for_family section offset family delta param_count
    index_count domain_count result =
  let head, args = collect_apps result in
  let expected_levels = universe_param_levels delta in
  match head with
  | Ext_term.Const (global_ref, levels)
    when Ext_inductive.family_ref family global_ref
         && levels_equal levels expected_levels ->
      if List.length args <> param_count + index_count then
        error section offset Inductive_invalid
      else if domain_count < param_count then error section offset Inductive_invalid
      else
        let rec check_params param_index remaining_args =
          if param_index = param_count then Ok ()
          else
            match remaining_args with
            | [] -> error section offset Inductive_invalid
            | arg :: rest ->
                let expected_arg =
                  Ext_term.BVar (domain_count - 1 - param_index)
                in
                if arg = expected_arg then check_params (param_index + 1) rest
                else error section offset Inductive_invalid
        in
        check_params 0 args
  | _ -> error section offset Inductive_invalid

let check_constructor_result section offset decl_index delta param_count index_count
    domain_count result =
  let family =
    Ext_inductive.family ~decl_index ~universe_params:delta ~param_count
      ~index_count
  in
  check_constructor_result_for_family section offset family delta param_count
    index_count domain_count result

let check_constructor_universe_bounds section offset env delta universe_context
    param_count ind_sort domains =
  if Ext_level.normalize ind_sort = Ext_level.Zero then Ok ()
  else
    let fuel = ref max_fuel in
    let rec loop domain_index context remaining =
      match remaining with
      | [] -> Ok ()
      | domain :: rest ->
          bind
            (expect_sort ~section ~offset ~delta ~universe_context ~fuel env context
               domain)
            (fun field_level ->
              let next_context = push_assumption context domain in
              if domain_index < param_count then
                loop (domain_index + 1) next_context rest
              else
                match
                  Ext_universe.entails_level_le universe_context field_level ind_sort
                with
                | Error universe_error ->
                    error_of_universe_error section offset universe_error
                | Ok true -> loop (domain_index + 1) next_context rest
                | Ok false ->
                    error section offset Constructor_universe_bound_violation)
    in
    loop 0 empty_context domains

let check_constructor section offset env delta universe_context decl_index params
    indices ind_sort constructor =
  bind
    (expect_sort ~section ~offset ~delta ~universe_context env empty_context
       constructor.Ext_cert.constructor_ty)
    (fun _ ->
      let domains, result = peel_pi_domains constructor.Ext_cert.constructor_ty in
      let family =
        Ext_inductive.family ~decl_index ~universe_params:delta
          ~param_count:(List.length params) ~index_count:(List.length indices)
      in
      match Ext_inductive.check_constructor_domains env family domains with
      | Error Ext_inductive.Non_positive_occurrence ->
          error section offset Positivity_failure
      | Ok () ->
          bind (whnf ~section ~offset ~delta env empty_context result) (fun result ->
              bind
                (check_constructor_result section offset decl_index delta
                   (List.length params) (List.length indices) (List.length domains)
                   result)
                (fun () ->
                  check_constructor_universe_bounds section offset env delta
                    universe_context (List.length params) ind_sort domains)))

let rec check_constructors section offset env delta universe_context decl_index params
    indices ind_sort constructors =
  match constructors with
  | [] -> Ok ()
  | constructor :: rest ->
      bind
        (check_constructor section offset env delta universe_context decl_index params
           indices ind_sort constructor)
        (fun () ->
          check_constructors section offset env delta universe_context decl_index params
            indices ind_sort rest)

let bvar_for_abs section offset ctx_len abs_index =
  if abs_index < 0 || abs_index >= ctx_len then
    error section offset Inductive_invalid
  else Ok (Ext_term.BVar (ctx_len - 1 - abs_index))

let rec remap_bvars section offset term source_ctx_len target_ctx_len source_to_target =
  match term with
  | Ext_term.Sort _ | Ext_term.Const _ -> Ok term
  | Ext_term.BVar index ->
      if index < 0 then error section offset Inductive_invalid
      else if index < source_ctx_len then
        let source_abs = source_ctx_len - 1 - index in
        match list_nth_opt source_abs source_to_target with
        | Some target_abs -> bvar_for_abs section offset target_ctx_len target_abs
        | None -> error section offset Inductive_invalid
      else error section offset Inductive_invalid
  | Ext_term.App (fn, arg) ->
      bind
        (remap_bvars section offset fn source_ctx_len target_ctx_len
           source_to_target)
        (fun remapped_fn ->
          bind
            (remap_bvars section offset arg source_ctx_len target_ctx_len
               source_to_target)
            (fun remapped_arg -> Ok (Ext_term.App (remapped_fn, remapped_arg))))
  | Ext_term.Lam (ty, body) ->
      bind
        (remap_bvars section offset ty source_ctx_len target_ctx_len
           source_to_target)
        (fun remapped_ty ->
          bind
            (remap_bvars section offset body (source_ctx_len + 1)
               (target_ctx_len + 1) (source_to_target @ [ target_ctx_len ]))
            (fun remapped_body -> Ok (Ext_term.Lam (remapped_ty, remapped_body))))
  | Ext_term.Pi (ty, body) ->
      bind
        (remap_bvars section offset ty source_ctx_len target_ctx_len
           source_to_target)
        (fun remapped_ty ->
          bind
            (remap_bvars section offset body (source_ctx_len + 1)
               (target_ctx_len + 1) (source_to_target @ [ target_ctx_len ]))
            (fun remapped_body -> Ok (Ext_term.Pi (remapped_ty, remapped_body))))
  | Ext_term.Let (ty, value, body) ->
      bind
        (remap_bvars section offset ty source_ctx_len target_ctx_len
           source_to_target)
        (fun remapped_ty ->
          bind
            (remap_bvars section offset value source_ctx_len target_ctx_len
               source_to_target)
            (fun remapped_value ->
              bind
                (remap_bvars section offset body (source_ctx_len + 1)
                   (target_ctx_len + 1)
                   (source_to_target @ [ target_ctx_len ]))
                (fun remapped_body ->
                  Ok (Ext_term.Let (remapped_ty, remapped_value, remapped_body)))))

let rec mk_pi_from_domains domains body =
  match domains with
  | [] -> body
  | domain :: rest -> Ext_term.Pi (domain, mk_pi_from_domains rest body)

let expected_motive_level ind_sort recursor_universe_params decl_universe_params =
  if Ext_level.normalize ind_sort = Ext_level.Zero then Ext_level.Zero
  else
    let rec find_extra reversed =
      match reversed with
      | [] -> None
      | name :: rest ->
          if has_name name decl_universe_params then find_extra rest
          else Some name
    in
    match find_extra (List.rev recursor_universe_params) with
    | Some name -> Ext_level.Param name
    | None -> (
        match List.rev recursor_universe_params with
        | name :: _ -> Ext_level.Param name
        | [] -> ind_sort)

let inductive_target_expr_for_family section offset family delta param_count
    index_abs_start index_count ctx_len =
  let global_ref =
    match family.Ext_inductive.family_name with
    | None -> Ext_term.Local { decl_index = family.Ext_inductive.family_decl_index }
    | Some name ->
        Ext_term.LocalGenerated
          { decl_index = family.Ext_inductive.family_decl_index; name }
  in
  let head =
    Ext_term.Const (global_ref, universe_param_levels delta)
  in
  let rec collect_params param_abs args =
    if param_abs = param_count then Ok (List.rev args)
    else
      bind (bvar_for_abs section offset ctx_len param_abs) (fun arg ->
          collect_params (param_abs + 1) (arg :: args))
  in
  let rec collect_indices index args =
    if index = index_count then Ok (List.rev args)
    else
      bind
        (bvar_for_abs section offset ctx_len (index_abs_start + index))
        (fun arg -> collect_indices (index + 1) (arg :: args))
  in
  bind (collect_params 0 []) (fun params ->
      bind (collect_indices 0 []) (fun indices ->
          Ok (apply_args head (params @ indices))))

let inductive_target_expr section offset decl_index delta param_count
    index_abs_start index_count ctx_len =
  let family =
    Ext_inductive.family ~decl_index ~universe_params:delta ~param_count
      ~index_count
  in
  inductive_target_expr_for_family section offset family delta param_count
    index_abs_start index_count ctx_len

let motive_app section offset ctx_len motive_abs index_args target =
  bind (bvar_for_abs section offset ctx_len motive_abs) (fun motive ->
      Ok (apply_args motive (index_args @ [ target ])))

let motive_domain_expr_for_family section offset family delta params indices
    motive_level =
  let param_count = List.length params in
  let source_to_target = ref (List.init param_count (fun index -> index)) in
  let domains = ref [] in
  let rec add_indices index remaining =
    match remaining with
    | [] -> Ok ()
    | binder :: rest ->
        let source_ctx_len = param_count + index in
        let target_ctx_len = param_count + index in
        bind
          (remap_bvars section offset binder.Ext_cert.binder_ty source_ctx_len
             target_ctx_len !source_to_target)
          (fun ty ->
            domains := ty :: !domains;
            source_to_target := !source_to_target @ [ target_ctx_len ];
            add_indices (index + 1) rest)
  in
  bind (add_indices 0 indices) (fun () ->
      let index_count = List.length indices in
      bind
        (inductive_target_expr_for_family section offset family delta param_count
           param_count index_count (param_count + index_count))
        (fun target ->
          Ok
            (mk_pi_from_domains (List.rev !domains)
               (Ext_term.Pi (target, Ext_term.Sort motive_level)))))

let motive_domain_expr section offset decl_index delta params indices motive_level =
  let family =
    Ext_inductive.family ~decl_index ~universe_params:delta
      ~param_count:(List.length params) ~index_count:(List.length indices)
  in
  motive_domain_expr_for_family section offset family delta params indices
    motive_level

let constructor_result_index_args section offset family constructor_result =
  let head, args = collect_apps constructor_result in
  match head with
  | Ext_term.Const (global_ref, levels)
    when Ext_inductive.family_ref family global_ref
         && levels_equal levels (universe_param_levels family.Ext_inductive.family_universe_params)
         && List.length args
            = family.Ext_inductive.family_param_count
              + family.Ext_inductive.family_index_count ->
      Ok (drop family.Ext_inductive.family_param_count args)
  | _ -> error section offset Inductive_invalid

let direct_recursive_index_args section offset family domain ctx_len =
  let head, args = collect_apps domain in
  match head with
  | Ext_term.Const (global_ref, levels)
    when Ext_inductive.family_ref family global_ref
         && levels_equal levels
              (universe_param_levels
                 family.Ext_inductive.family_universe_params)
         && List.length args
            = family.Ext_inductive.family_param_count
              + family.Ext_inductive.family_index_count ->
      let rec check_params param_index remaining =
        if param_index = family.Ext_inductive.family_param_count then true
        else
          match remaining with
          | arg :: rest ->
              arg
              = Ext_term.BVar (ctx_len - 1 - param_index)
              && check_params (param_index + 1) rest
          | [] -> false
      in
      if
        check_params 0 args
        && List.for_all
             (fun arg ->
               not (Ext_inductive.contains_recursive_const family arg))
             args
      then Ok (drop family.Ext_inductive.family_param_count args)
      else error section offset Inductive_invalid
  | _ -> error section offset Inductive_invalid

let expected_minor_type section offset decl_index delta params indices constructor_index
    constructor =
  let param_count = List.length params in
  let index_count = List.length indices in
  let family =
    Ext_inductive.family ~decl_index ~universe_params:delta ~param_count
      ~index_count
  in
  let constructor_domains, constructor_result =
    peel_pi_domains constructor.Ext_cert.constructor_ty
  in
  if List.length constructor_domains < param_count then
    error section offset Inductive_invalid
  else
    bind
      (constructor_result_index_args section offset family constructor_result)
      (fun result_index_args ->
            let prefix_len = param_count + 1 + constructor_index in
            let motive_abs = param_count in
            let source_to_target = ref (List.init param_count (fun index -> index)) in
            let target_ctx_len = ref prefix_len in
            let expected_domains = ref [] in
            let field_abs = ref [] in
            let rec add_fields field_index remaining =
              match remaining with
              | [] -> Ok ()
              | field_domain :: rest ->
                  let source_ctx_len = param_count + field_index in
                  bind
                    (remap_bvars section offset field_domain source_ctx_len
                       !target_ctx_len !source_to_target)
                    (fun remapped_domain ->
                      expected_domains := remapped_domain :: !expected_domains;
                      source_to_target := !source_to_target @ [ !target_ctx_len ];
                      field_abs := !target_ctx_len :: !field_abs;
                      target_ctx_len := !target_ctx_len + 1;
                      match
                        direct_recursive_index_args section offset family
                          field_domain source_ctx_len
                      with
                      | Ok recursive_indices ->
                          let rec remap_indices remaining remapped =
                            match remaining with
                            | [] -> Ok (List.rev remapped)
                            | index_arg :: index_rest ->
                                bind
                                  (remap_bvars section offset index_arg
                                     source_ctx_len !target_ctx_len
                                     !source_to_target)
                                  (fun remapped_arg ->
                                    remap_indices index_rest
                                      (remapped_arg :: remapped))
                          in
                          bind (remap_indices recursive_indices [])
                            (fun recursive_indices ->
                        bind
                          (motive_app section offset !target_ctx_len motive_abs
                             recursive_indices (Ext_term.BVar 0))
                          (fun ih_domain ->
                            expected_domains := ih_domain :: !expected_domains;
                            target_ctx_len := !target_ctx_len + 1;
                            add_fields (field_index + 1) rest))
                      | Error _ -> add_fields (field_index + 1) rest)
            in
            bind (add_fields 0 (drop param_count constructor_domains)) (fun () ->
                let rec collect_params param_abs args =
                  if param_abs = param_count then Ok (List.rev args)
                  else
                    bind
                      (bvar_for_abs section offset !target_ctx_len param_abs)
                      (fun arg -> collect_params (param_abs + 1) (arg :: args))
                in
                let rec collect_fields remaining args =
                  match remaining with
                  | [] -> Ok (List.rev args)
                  | abs_index :: rest ->
                      bind
                        (bvar_for_abs section offset !target_ctx_len abs_index)
                        (fun arg -> collect_fields rest (arg :: args))
                in
                bind (collect_params 0 []) (fun param_args ->
                    bind (collect_fields (List.rev !field_abs) []) (fun field_args ->
                        let constructor_value =
                          apply_args
                            (Ext_term.Const
                               ( Ext_term.LocalGenerated
                                   {
                                     decl_index;
                                     name = constructor.Ext_cert.constructor_name;
                                   },
                                 universe_param_levels delta ))
                            (param_args @ field_args)
                        in
                        let rec remap_result_indices remaining remapped =
                          match remaining with
                          | [] -> Ok (List.rev remapped)
                          | index_arg :: rest ->
                              bind
                                (remap_bvars section offset index_arg
                                   (List.length constructor_domains)
                                   !target_ctx_len !source_to_target)
                                (fun remapped_arg ->
                                  remap_result_indices rest
                                    (remapped_arg :: remapped))
                        in
                        bind
                          (remap_result_indices result_index_args [])
                          (fun result_index_args ->
                        bind
                          (motive_app section offset !target_ctx_len motive_abs
                             result_index_args constructor_value)
                          (fun result ->
                            Ok
                              (mk_pi_from_domains
                                 (List.rev !expected_domains)
                                 result)))))))

let mutual_family decl_index delta (spec : Ext_cert.mutual_inductive_spec) =
  Ext_inductive.named_family ~name:spec.Ext_cert.mutual_name ~decl_index
    ~universe_params:delta ~param_count:(List.length spec.Ext_cert.mutual_params)
    ~index_count:(List.length spec.Ext_cert.mutual_indices)

let expected_mutual_minor_type section offset decl_index delta mutuals
    family_index constructor_index constructor =
  match list_nth_opt family_index mutuals with
  | None -> error section offset Inductive_invalid
  | Some owner ->
      let families = List.map (mutual_family decl_index delta) mutuals in
      let owner_family = mutual_family decl_index delta owner in
      let constructor_domains, constructor_result =
        peel_pi_domains constructor.Ext_cert.constructor_ty
      in
      let param_count = List.length owner.Ext_cert.mutual_params in
      if List.length constructor_domains < param_count then
        error section offset Inductive_invalid
      else
        bind
          (constructor_result_index_args section offset owner_family
             constructor_result)
          (fun result_index_args ->
            let prefix_len = param_count + List.length mutuals + constructor_index in
            let motive_abs_start = param_count in
            let source_to_target =
              ref (List.init param_count (fun index -> index))
            in
            let target_ctx_len = ref prefix_len in
            let expected_domains = ref [] in
            let field_abs = ref [] in
            let rec add_fields field_index remaining =
              match remaining with
              | [] -> Ok ()
              | field_domain :: rest ->
                  let source_ctx_len = param_count + field_index in
                  bind
                    (remap_bvars section offset field_domain source_ctx_len
                       !target_ctx_len !source_to_target)
                    (fun remapped_domain ->
                      expected_domains := remapped_domain :: !expected_domains;
                      source_to_target :=
                        !source_to_target @ [ !target_ctx_len ];
                      field_abs := !target_ctx_len :: !field_abs;
                      target_ctx_len := !target_ctx_len + 1;
                      match
                        Ext_inductive.direct_mutual_recursive_index_args families
                          field_domain source_ctx_len
                      with
                      | None -> add_fields (field_index + 1) rest
                      | Some (field_family_index, recursive_indices) ->
                          let rec remap_indices remaining remapped =
                            match remaining with
                            | [] -> Ok (List.rev remapped)
                            | index_arg :: index_rest ->
                                bind
                                  (remap_bvars section offset index_arg
                                     source_ctx_len !target_ctx_len
                                     !source_to_target)
                                  (fun remapped_arg ->
                                    remap_indices index_rest
                                      (remapped_arg :: remapped))
                          in
                          bind (remap_indices recursive_indices [])
                            (fun recursive_indices ->
                              bind
                                (motive_app section offset !target_ctx_len
                                   (motive_abs_start + field_family_index)
                                   recursive_indices (Ext_term.BVar 0))
                                (fun ih_domain ->
                                  expected_domains :=
                                    ih_domain :: !expected_domains;
                                  target_ctx_len := !target_ctx_len + 1;
                                  add_fields (field_index + 1) rest)))
            in
            bind
              (add_fields 0 (drop param_count constructor_domains))
              (fun () ->
                let rec collect_params param_abs args =
                  if param_abs = param_count then Ok (List.rev args)
                  else
                    bind
                      (bvar_for_abs section offset !target_ctx_len param_abs)
                      (fun arg ->
                        collect_params (param_abs + 1) (arg :: args))
                in
                let rec collect_fields remaining args =
                  match remaining with
                  | [] -> Ok (List.rev args)
                  | abs_index :: rest ->
                      bind
                        (bvar_for_abs section offset !target_ctx_len abs_index)
                        (fun arg -> collect_fields rest (arg :: args))
                in
                bind (collect_params 0 []) (fun param_args ->
                    bind
                      (collect_fields (List.rev !field_abs) [])
                      (fun field_args ->
                        let constructor_value =
                          apply_args
                            (Ext_term.Const
                               ( Ext_term.LocalGenerated
                                   {
                                     decl_index;
                                     name =
                                       constructor.Ext_cert.constructor_name;
                                   },
                                 universe_param_levels delta ))
                            (param_args @ field_args)
                        in
                        let rec remap_result_indices remaining remapped =
                          match remaining with
                          | [] -> Ok (List.rev remapped)
                          | index_arg :: rest ->
                              bind
                                (remap_bvars section offset index_arg
                                   (List.length constructor_domains)
                                   !target_ctx_len !source_to_target)
                                (fun remapped_arg ->
                                  remap_result_indices rest
                                    (remapped_arg :: remapped))
                        in
                        bind
                          (remap_result_indices result_index_args [])
                          (fun remapped_indices ->
                            bind
                              (motive_app section offset !target_ctx_len
                                 (motive_abs_start + family_index)
                                 remapped_indices constructor_value)
                              (fun result ->
                                Ok
                                  (mk_pi_from_domains
                                     (List.rev !expected_domains)
                                     result)))))))

let append_index_domains section offset params indices domains =
  let param_count = List.length params in
  let source_to_target = ref (List.init param_count (fun index -> index)) in
  let result = ref domains in
  let rec loop index remaining =
    match remaining with
    | [] -> Ok (List.rev (List.rev !result))
    | binder :: rest ->
        let source_ctx_len = param_count + index in
        let target_ctx_len = List.length !result in
        bind
          (remap_bvars section offset binder.Ext_cert.binder_ty source_ctx_len
             target_ctx_len !source_to_target)
          (fun ty ->
            result := !result @ [ ty ];
            source_to_target := !source_to_target @ [ target_ctx_len ];
            loop (index + 1) rest)
  in
  loop 0 indices

let expected_recursor_type section offset decl_index delta ind_params ind_indices
    ind_sort ind_constructors recursor =
  let param_count = List.length ind_params in
    let motive_level =
      expected_motive_level ind_sort recursor.Ext_cert.recursor_universe_params delta
    in
    let param_domains = List.map (fun param -> param.Ext_cert.binder_ty) ind_params in
    match
      motive_domain_expr section offset decl_index delta ind_params ind_indices
        motive_level
    with
    | Error err -> Error err
    | Ok motive_domain -> (
        let rec collect_minors constructor_index remaining minors =
          match remaining with
          | [] -> Ok (List.rev minors)
          | constructor :: rest ->
              bind
                (expected_minor_type section offset decl_index delta ind_params
                   ind_indices constructor_index constructor)
                (fun minor ->
                  collect_minors (constructor_index + 1) rest (minor :: minors))
        in
        match collect_minors 0 ind_constructors [] with
        | Error err -> Error err
        | Ok minor_domains -> (
            let domains = param_domains @ [ motive_domain ] @ minor_domains in
            let index_start = List.length domains in
            match append_index_domains section offset ind_params ind_indices domains with
            | Error err -> Error err
            | Ok domains -> (
                match
                  inductive_target_expr section offset decl_index delta param_count
                    index_start (List.length ind_indices) (List.length domains)
                with
                | Error err -> Error err
                | Ok major_domain ->
                let domains = domains @ [ major_domain ] in
                let rec collect_index_args index args =
                  if index = List.length ind_indices then Ok (List.rev args)
                  else
                    bind
                      (bvar_for_abs section offset (List.length domains)
                         (index_start + index))
                      (fun arg -> collect_index_args (index + 1) (arg :: args))
                in
                match
                  bvar_for_abs section offset (List.length domains)
                    recursor.Ext_cert.recursor_rules.major_index
                with
                | Error err -> Error err
                | Ok major ->
                    bind (collect_index_args 0 []) (fun index_args ->
                        bind
                          (motive_app section offset (List.length domains)
                             param_count index_args major)
                          (fun result ->
                            Ok (mk_pi_from_domains domains result))))))

let mutual_constructor_count mutuals =
  List.fold_left
    (fun count mutual ->
      count + List.length mutual.Ext_cert.mutual_constructors)
    0 mutuals

let expected_mutual_recursor_type section offset decl_index delta mutuals
    target_index recursor =
  match list_nth_opt target_index mutuals with
  | None -> error section offset Inductive_invalid
  | Some target ->
      let param_count = List.length target.Ext_cert.mutual_params in
      let param_domains =
        List.map
          (fun param -> param.Ext_cert.binder_ty)
          target.Ext_cert.mutual_params
      in
      let rec collect_motives remaining motives =
        match remaining with
        | [] -> Ok (List.rev motives)
        | family_spec :: rest ->
            let family = mutual_family decl_index delta family_spec in
            let motive_level =
              expected_motive_level family_spec.Ext_cert.mutual_sort
                recursor.Ext_cert.recursor_universe_params delta
            in
            bind
              (motive_domain_expr_for_family section offset family delta
                 family_spec.Ext_cert.mutual_params
                 family_spec.Ext_cert.mutual_indices motive_level)
              (fun motive -> collect_motives rest (motive :: motives))
      in
      let rec collect_family_minors family_index constructor_index remaining
          minors =
        match remaining with
        | [] -> Ok (List.rev minors)
        | family_spec :: rest ->
            let rec collect_constructors next_index constructors accumulated =
              match constructors with
              | [] ->
                  collect_family_minors (family_index + 1) next_index rest
                    accumulated
              | constructor :: constructor_rest ->
                  bind
                    (expected_mutual_minor_type section offset decl_index delta
                       mutuals family_index next_index constructor)
                    (fun minor ->
                      collect_constructors (next_index + 1) constructor_rest
                        (minor :: accumulated))
            in
            collect_constructors constructor_index
              family_spec.Ext_cert.mutual_constructors minors
      in
      bind (collect_motives mutuals []) (fun motives ->
          bind (collect_family_minors 0 0 mutuals []) (fun minor_domains ->
              let domains = param_domains @ motives @ minor_domains in
              let index_start = List.length domains in
              bind
                (append_index_domains section offset
                   target.Ext_cert.mutual_params
                   target.Ext_cert.mutual_indices domains)
                (fun domains ->
                  let family = mutual_family decl_index delta target in
                  bind
                    (inductive_target_expr_for_family section offset family delta
                       param_count index_start
                       (List.length target.Ext_cert.mutual_indices)
                       (List.length domains))
                    (fun major_domain ->
                      let domains = domains @ [ major_domain ] in
                      let rec collect_index_args index args =
                        if index = List.length target.Ext_cert.mutual_indices then
                          Ok (List.rev args)
                        else
                          bind
                            (bvar_for_abs section offset (List.length domains)
                               (index_start + index))
                            (fun arg ->
                              collect_index_args (index + 1) (arg :: args))
                      in
                      bind
                        (bvar_for_abs section offset (List.length domains)
                           recursor.Ext_cert.recursor_rules.major_index)
                        (fun major ->
                          bind (collect_index_args 0 []) (fun index_args ->
                              bind
                                (motive_app section offset
                                   (List.length domains)
                                   (param_count + target_index) index_args major)
                                (fun result ->
                                  Ok
                                    (mk_pi_from_domains domains result))))))))

let check_mutual_recursor_declaration section offset env decl_index delta
    universe_constraints mutuals target_index recursor =
  match list_nth_opt target_index mutuals with
  | None -> error section offset Inductive_invalid
  | Some target ->
      let expected_minor_start =
        List.length target.Ext_cert.mutual_params + List.length mutuals
      in
      let expected_major_index =
        expected_minor_start + mutual_constructor_count mutuals
        + List.length target.Ext_cert.mutual_indices
      in
      let domains, _ = peel_pi_domains recursor.Ext_cert.recursor_ty in
      if recursor.Ext_cert.recursor_rules.minor_start <> expected_minor_start then
        error section offset Inductive_invalid
      else if
        recursor.Ext_cert.recursor_rules.major_index <> expected_major_index
      then error section offset Inductive_invalid
      else if List.length domains <> expected_major_index + 1 then
        error section offset Inductive_invalid
      else
        match
          Ext_universe.create recursor.Ext_cert.recursor_universe_params
            universe_constraints
        with
        | Error universe_error ->
            error_of_universe_error section offset universe_error
        | Ok recursor_universe_context ->
            bind
              (expected_mutual_recursor_type section offset decl_index delta
                 mutuals target_index recursor)
              (fun expected_ty ->
                if recursor.Ext_cert.recursor_ty <> expected_ty then
                  error section offset Inductive_invalid
                else
                  bind
                    (expect_sort ~section ~offset
                       ~delta:recursor.Ext_cert.recursor_universe_params
                       ~universe_context:recursor_universe_context env empty_context
                       recursor.Ext_cert.recursor_ty)
                    (fun _ -> Ok ()))

let check_recursor_declaration section offset env decl_index delta
    universe_constraints ind_params ind_indices ind_sort ind_constructors recursor =
    let param_count = List.length ind_params in
    let constructor_count = List.length ind_constructors in
    let expected_minor_start = param_count + 1 in
    let expected_major_index =
      expected_minor_start + constructor_count + List.length ind_indices
    in
    let domains, _ = peel_pi_domains recursor.Ext_cert.recursor_ty in
    if recursor.Ext_cert.recursor_rules.minor_start <> expected_minor_start then
      error section offset Inductive_invalid
    else if
      recursor.Ext_cert.recursor_rules.major_index <> expected_major_index
    then error section offset Inductive_invalid
    else if List.length domains <> expected_major_index + 1 then
      error section offset Inductive_invalid
    else
      (match
         Ext_universe.create recursor.Ext_cert.recursor_universe_params
           universe_constraints
       with
      | Error universe_error ->
          error_of_universe_error section offset universe_error
      | Ok recursor_universe_context ->
          bind
            (expected_recursor_type section offset decl_index delta ind_params
               ind_indices ind_sort ind_constructors recursor)
            (fun expected_ty ->
              if recursor.Ext_cert.recursor_ty <> expected_ty then
                error section offset Inductive_invalid
              else
                bind
                  (expect_sort ~section ~offset
                     ~delta:recursor.Ext_cert.recursor_universe_params
                     ~universe_context:recursor_universe_context
                     env empty_context recursor.Ext_cert.recursor_ty)
                  (fun _ -> Ok ())))

let rec localize_imported_group_term import_index decl_interface_hash
    family_name generated_names synthetic_decl_index term =
  let localize_ref global_ref =
    match global_ref with
    | Ext_term.Imported
        {
          import_index = current_import_index;
          name;
          decl_interface_hash = current_hash;
        }
      when current_import_index = import_index
           && current_hash = decl_interface_hash ->
        if Ext_name.equal name family_name then
          Ext_term.Local { decl_index = synthetic_decl_index }
        else if List.exists (Ext_name.equal name) generated_names then
          Ext_term.LocalGenerated { decl_index = synthetic_decl_index; name }
        else global_ref
    | _ -> global_ref
  in
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> term
  | Ext_term.Const (global_ref, levels) ->
      Ext_term.Const (localize_ref global_ref, levels)
  | Ext_term.App (fn, arg) ->
      Ext_term.App
        ( localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index fn,
          localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index arg )
  | Ext_term.Lam (ty, body) ->
      Ext_term.Lam
        ( localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index ty,
          localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index body )
  | Ext_term.Pi (ty, body) ->
      Ext_term.Pi
        ( localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index ty,
          localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index body )
  | Ext_term.Let (ty, value, body) ->
      Ext_term.Let
        ( localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index ty,
          localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index value,
          localize_imported_group_term import_index decl_interface_hash
            family_name generated_names synthetic_decl_index body )

let public_exports_with_kind_and_hash kind decl_interface_hash exports =
  List.filter
    (fun (export : Ext_import_store.public_export) ->
      export.Ext_import_store.public_export_kind = kind
      && export.Ext_import_store.public_decl_interface_hash
         = decl_interface_hash)
    exports

type indexed_public_export =
  | Unique_public_export of Ext_import_store.public_export
  | Duplicate_public_export

let index_public_exports decl_interface_hash exports =
  let index = Hashtbl.create (List.length exports) in
  List.iter
    (fun (export : Ext_import_store.public_export) ->
      if
        export.Ext_import_store.public_decl_interface_hash
        = decl_interface_hash
      then
        let key =
          ( export.Ext_import_store.public_export_kind,
            export.Ext_import_store.public_export_name )
        in
        match Hashtbl.find_opt index key with
        | None -> Hashtbl.add index key (Unique_public_export export)
        | Some (Unique_public_export _) | Some Duplicate_public_export ->
            Hashtbl.replace index key Duplicate_public_export)
    exports;
  index

let unique_public_export kind name exports =
  match Hashtbl.find_opt exports (kind, name) with
  | Some (Unique_public_export export) -> Some export
  | None | Some Duplicate_public_export -> None

let rec localize_imported_mutual_group_term import_index decl_interface_hash
    localized_names synthetic_decl_index term =
  let localize_ref global_ref =
    match global_ref with
    | Ext_term.Imported
        {
          import_index = current_import_index;
          name;
          decl_interface_hash = current_hash;
        }
      when current_import_index = import_index
           && current_hash = decl_interface_hash
           && Hashtbl.mem localized_names name ->
        Ext_term.LocalGenerated { decl_index = synthetic_decl_index; name }
    | _ -> global_ref
  in
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> term
  | Ext_term.Const (global_ref, levels) ->
      Ext_term.Const (localize_ref global_ref, levels)
  | Ext_term.App (fn, arg) ->
      Ext_term.App
        ( localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index fn,
          localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index arg )
  | Ext_term.Lam (ty, body) ->
      Ext_term.Lam
        ( localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index ty,
          localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index body )
  | Ext_term.Pi (ty, body) ->
      Ext_term.Pi
        ( localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index ty,
          localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index body )
  | Ext_term.Let (ty, value, body) ->
      Ext_term.Let
        ( localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index ty,
          localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index value,
          localize_imported_mutual_group_term import_index decl_interface_hash
            localized_names synthetic_decl_index body )

let instantiate_imported_public_ty env import_index public_environment section
    offset (export : Ext_import_store.public_export) =
  match
    Ext_env.instantiate_public_term env import_index public_environment section
      offset export.Ext_import_store.public_ty
  with
  | Ok ty -> Ok ty
  | Error env_error -> error_of_env_error env_error

let reconstruct_imported_mutual_recursors env section offset import_index
    decl_interface_hash public_environment
    (group : Ext_import_store.public_inductive_group) =
  let exports = public_environment.Ext_import_store.public_exports in
  let export_index = index_public_exports decl_interface_hash exports in
  let layouts = group.Ext_import_store.public_group_families in
  let synthetic_decl_index = -1 in
  let family_names =
    List.map
      (fun layout -> layout.Ext_import_store.public_inductive_name)
      layouts
  in
  let generated_names =
    List.concat
      (List.map
         (fun layout ->
           layout.Ext_import_store.public_constructor_names
           @
           match layout.Ext_import_store.public_recursor_layout with
           | None -> []
           | Some recursor ->
               [ recursor.Ext_import_store.public_recursor_name ])
         layouts)
  in
  let localized_names =
    Hashtbl.create (List.length family_names + List.length generated_names)
  in
  List.iter (fun name -> Hashtbl.replace localized_names name ()) family_names;
  List.iter (fun name -> Hashtbl.replace localized_names name ()) generated_names;
  let localize term =
    localize_imported_mutual_group_term import_index decl_interface_hash
      localized_names synthetic_decl_index term
  in
  let rec build_families remaining accumulated =
    match remaining with
    | [] -> Ok (List.rev accumulated)
    | layout :: rest -> (
        match
          unique_public_export Ext_cert.Export_inductive
            layout.Ext_import_store.public_inductive_name export_index
        with
        | None -> Ok []
        | Some inductive ->
            bind
              (instantiate_imported_public_ty env import_index public_environment
                 section offset inductive)
              (fun family_ty ->
                let family_domains, family_result =
                  peel_pi_domains (localize family_ty)
                in
                match family_result with
                | Ext_term.Sort mutual_sort
                  when List.length family_domains
                       = layout.Ext_import_store.public_param_count
                         + layout.Ext_import_store.public_index_count ->
                    let rec build_constructors names constructors =
                      match names with
                      | [] -> Ok (List.rev constructors)
                      | name :: name_rest -> (
                          match
                            unique_public_export Ext_cert.Export_constructor name
                              export_index
                          with
                          | None -> Ok []
                          | Some constructor ->
                              bind
                                (instantiate_imported_public_ty env import_index
                                   public_environment section offset constructor)
                                (fun ty ->
                                  build_constructors name_rest
                                    ({
                                       Ext_cert.constructor_name = name;
                                       constructor_ty = localize ty;
                                     }
                                    :: constructors)))
                    in
                    bind
                      (build_constructors
                         layout.Ext_import_store.public_constructor_names [])
                      (fun mutual_constructors ->
                        if
                          List.length mutual_constructors
                          <> List.length
                               layout.Ext_import_store.public_constructor_names
                        then Ok []
                        else
                          let build_recursor =
                            match
                              layout.Ext_import_store.public_recursor_layout
                            with
                            | None -> Ok None
                            | Some recursor_layout -> (
                                match
                                  unique_public_export Ext_cert.Export_recursor
                                    recursor_layout.Ext_import_store
                                    .public_recursor_name export_index
                                with
                                | None -> Ok None
                                | Some recursor_export ->
                                    bind
                                      (instantiate_imported_public_ty env
                                         import_index public_environment section
                                         offset recursor_export)
                                      (fun ty ->
                                        Ok
                                          (Some
                                             {
                                               Ext_cert.recursor_name =
                                                 recursor_layout
                                                   .Ext_import_store
                                                   .public_recursor_name;
                                               recursor_universe_params =
                                                 recursor_export
                                                   .Ext_import_store
                                                   .public_universe_params;
                                               recursor_ty = localize ty;
                                               recursor_rules =
                                                 recursor_layout
                                                   .Ext_import_store
                                                   .public_recursor_rules;
                                             })))
                          in
                          bind build_recursor (fun mutual_recursor ->
                              match
                                ( layout.Ext_import_store.public_recursor_layout,
                                  mutual_recursor )
                              with
                              | Some _, None -> Ok []
                              | _ ->
                                  let params, indices =
                                    ( take
                                        layout.Ext_import_store.public_param_count
                                        family_domains,
                                      drop
                                        layout.Ext_import_store.public_param_count
                                        family_domains )
                                  in
                                  build_families rest
                                    ({
                                       Ext_cert.mutual_name =
                                         layout.Ext_import_store
                                         .public_inductive_name;
                                       mutual_params =
                                         List.map
                                           (fun binder_ty ->
                                             { Ext_cert.binder_ty })
                                           params;
                                       mutual_indices =
                                         List.map
                                           (fun binder_ty ->
                                             { Ext_cert.binder_ty })
                                           indices;
                                       mutual_sort;
                                       mutual_constructors;
                                       mutual_recursor;
                                     }
                                    :: accumulated)))
                | Ext_term.Sort _ | Ext_term.BVar _ | Ext_term.Const _
                | Ext_term.App _ | Ext_term.Lam _ | Ext_term.Pi _
                | Ext_term.Let _ -> Ok []))
  in
  bind (build_families layouts []) (fun mutuals ->
      match mutuals with
      | [] -> Ok None
      | first :: _ ->
          let shared =
            List.for_all
              (fun mutual ->
                mutual.Ext_cert.mutual_params = first.Ext_cert.mutual_params)
              mutuals
          in
          if (not shared) || List.length mutuals <> List.length layouts then
            Ok None
          else
            let universe_params =
              match
                unique_public_export Ext_cert.Export_inductive
                  first.Ext_cert.mutual_name export_index
              with
              | None -> []
              | Some export ->
                  export.Ext_import_store.public_universe_params
            in
            let rec validate target_index runtimes remaining =
              match remaining with
              | [] -> Ok (Some (List.rev runtimes))
              | mutual :: rest -> (
                  match mutual.Ext_cert.mutual_recursor with
                  | None -> Ok None
                  | Some recursor ->
                      let expected_minor_start =
                        List.length mutual.Ext_cert.mutual_params
                        + List.length mutuals
                      in
                      let expected_major_index =
                        expected_minor_start + mutual_constructor_count mutuals
                        + List.length mutual.Ext_cert.mutual_indices
                      in
                      if
                        recursor.Ext_cert.recursor_rules.minor_start
                        <> expected_minor_start
                        || recursor.Ext_cert.recursor_rules.major_index
                           <> expected_major_index
                      then Ok None
                      else
                        match
                          expected_mutual_recursor_type section offset
                            synthetic_decl_index universe_params mutuals
                            target_index recursor
                        with
                        | Error _ -> Ok None
                        | Ok expected_ty
                          when expected_ty = recursor.Ext_cert.recursor_ty ->
                            let runtime =
                              {
                                Ext_env.imported_mutual_import_index = import_index;
                                imported_mutual_decl_interface_hash =
                                  decl_interface_hash;
                                imported_mutual_synthetic_decl_index =
                                  synthetic_decl_index;
                                imported_mutual_universe_params = universe_params;
                                imported_mutual_families = mutuals;
                                imported_mutual_target_index = target_index;
                                imported_mutual_recursor = recursor;
                              }
                            in
                            validate (target_index + 1) (runtime :: runtimes)
                              rest
                        | Ok _ -> Ok None)
            in
            validate 0 [] mutuals)

let order_imported_constructors section offset fuel synthetic_decl_index
    universe_params params indices recursor_domains rules constructors =
  let rec choose constructor_index ordered remaining =
    match remaining with
    | [] -> Ok (Some (List.rev ordered))
    | _ -> (
        match
          list_nth_opt (rules.Ext_cert.minor_start + constructor_index)
            recursor_domains
        with
        | None -> Ok None
        | Some actual_minor ->
            let rec try_remaining before candidates =
              match candidates with
              | [] -> Ok None
              | constructor :: rest ->
                  bind (spend_fuel section offset fuel) (fun () ->
                      let expected =
                        expected_minor_type section offset synthetic_decl_index
                          universe_params params indices constructor_index
                          constructor
                      in
                      match expected with
                      | Ok expected_minor when expected_minor = actual_minor ->
                          let next_remaining = List.rev_append before rest in
                          bind
                            (choose (constructor_index + 1)
                               (constructor :: ordered) next_remaining)
                            (function
                              | Some _ as ordered -> Ok ordered
                              | None ->
                                  try_remaining (constructor :: before) rest)
                      | Ok _ | Error _ ->
                          try_remaining (constructor :: before) rest)
            in
            try_remaining [] remaining)
  in
  choose 0 [] constructors

let imported_mutual_reconstruction_cost public_environment
    (group : Ext_import_store.public_inductive_group) =
  let family_count =
    List.length group.Ext_import_store.public_group_families
  in
  let constructor_count =
    List.fold_left
      (fun count family ->
        count
        + List.length family.Ext_import_store.public_constructor_names)
      0 group.Ext_import_store.public_group_families
  in
  let export_count =
    List.length public_environment.Ext_import_store.public_exports
  in
  let construction_cost =
    capped_fuel_cost_add export_count
      (capped_fuel_cost_add family_count constructor_count)
  in
  let validation_width =
    capped_fuel_cost_add family_count (constructor_count + 1)
  in
  let validation_cost =
    capped_fuel_cost_mul family_count validation_width
  in
  capped_fuel_cost_add construction_cost validation_cost

let imported_mutual_runtime_named recursor_name runtimes =
  match
    List.find_opt
      (fun (runtime : Ext_env.imported_mutual_recursor_runtime) ->
        Ext_name.equal
          runtime.Ext_env.imported_mutual_recursor.Ext_cert.recursor_name
          recursor_name)
      runtimes
  with
  | None -> None
  | Some runtime -> Some (Ext_env.Imported_mutual runtime)

let cache_imported_mutual_runtimes env import_index decl_interface_hash
    runtimes =
  List.iter
    (fun (runtime : Ext_env.imported_mutual_recursor_runtime) ->
      Ext_env.cache_imported_recursor env import_index
        runtime.Ext_env.imported_mutual_recursor.Ext_cert.recursor_name
        decl_interface_hash (Some (Ext_env.Imported_mutual runtime)))
    runtimes

let reconstruct_imported_recursor_uncached env section offset fuel import_index
    recursor_name decl_interface_hash =
  match Ext_env.find_import import_index env.Ext_env.imports with
  | None -> Ok None
  | Some import ->
      let public_environment =
        import.Ext_import_store.resolved_public_environment
      in
      let mutual_groups =
        List.filter
          (fun group ->
            group.Ext_import_store.public_group_decl_interface_hash
              = decl_interface_hash
            && List.length group.Ext_import_store.public_group_families > 1)
          public_environment.Ext_import_store.public_inductive_groups
      in
      match mutual_groups with
      | [ group ] -> (
          match
            Ext_env.find_imported_mutual_block_cache env import_index
              decl_interface_hash
          with
          | Some runtimes ->
              Ok
                (match runtimes with
                | None -> None
                | Some runtimes ->
                    imported_mutual_runtime_named recursor_name runtimes)
          | None ->
              bind
                (spend_fuel_units section offset fuel
                   (imported_mutual_reconstruction_cost public_environment
                      group))
                (fun () ->
                  bind
                    (reconstruct_imported_mutual_recursors env section offset
                       import_index decl_interface_hash public_environment group)
                    (fun runtimes ->
                      Ext_env.cache_imported_mutual_block env import_index
                        decl_interface_hash runtimes;
                      (match runtimes with
                      | None -> ()
                      | Some runtimes ->
                          cache_imported_mutual_runtimes env import_index
                            decl_interface_hash runtimes);
                      Ok
                        (match runtimes with
                        | None -> None
                        | Some runtimes ->
                            imported_mutual_runtime_named recursor_name
                              runtimes))))
      | _ :: _ -> Ok None
      | [] ->
      let exports = public_environment.Ext_import_store.public_exports in
      let inductives =
        public_exports_with_kind_and_hash Ext_cert.Export_inductive
          decl_interface_hash exports
      in
      let recursors =
        public_exports_with_kind_and_hash Ext_cert.Export_recursor
          decl_interface_hash exports
      in
      let constructors =
        public_exports_with_kind_and_hash Ext_cert.Export_constructor
          decl_interface_hash exports
      in
      (match (inductives, recursors) with
      | [ inductive ], [ recursor_export ]
        when Ext_name.equal
               recursor_export.Ext_import_store.public_export_name
               recursor_name ->
          let synthetic_decl_index = -1 in
          let family_name =
            inductive.Ext_import_store.public_export_name
          in
          let generated_names =
            recursor_name
            :: List.map
                 (fun (export : Ext_import_store.public_export) ->
                   export.Ext_import_store.public_export_name)
                 constructors
          in
          bind
            (instantiate_imported_public_ty env import_index public_environment
               section offset inductive)
            (fun family_ty ->
              bind
                (instantiate_imported_public_ty env import_index
                   public_environment section offset recursor_export)
                (fun recursor_ty ->
                  let rec instantiate_constructors remaining accumulated =
                    match remaining with
                    | [] -> Ok (List.rev accumulated)
                    | export :: rest ->
                        bind
                          (instantiate_imported_public_ty env import_index
                             public_environment section offset export)
                          (fun ty ->
                            let localized_ty =
                              localize_imported_group_term import_index
                                decl_interface_hash family_name generated_names
                                synthetic_decl_index ty
                            in
                            instantiate_constructors rest
                              ({
                                 Ext_cert.constructor_name =
                                   export.Ext_import_store.public_export_name;
                                 constructor_ty = localized_ty;
                               }
                              :: accumulated))
                  in
                  bind (instantiate_constructors constructors [])
                    (fun localized_constructors ->
                      let localized_family_ty =
                        localize_imported_group_term import_index
                          decl_interface_hash family_name generated_names
                          synthetic_decl_index family_ty
                      in
                      let localized_recursor_ty =
                        localize_imported_group_term import_index
                          decl_interface_hash family_name generated_names
                          synthetic_decl_index recursor_ty
                      in
                      let family_domains, family_result =
                        peel_pi_domains localized_family_ty
                      in
                      let recursor_domains, _ =
                        peel_pi_domains localized_recursor_ty
                      in
                      match family_result with
                      | Ext_term.Sort ind_sort
                        when List.length recursor_domains
                             = List.length family_domains
                               + List.length localized_constructors + 2 ->
                          let rec try_param_count param_count =
                            if param_count > List.length family_domains then
                              Ok None
                            else
                              bind (spend_fuel section offset fuel) (fun () ->
                                  let params =
                                    List.map
                                      (fun binder_ty ->
                                        { Ext_cert.binder_ty })
                                      (take param_count family_domains)
                                  in
                                  let indices =
                                    List.map
                                      (fun binder_ty ->
                                        { Ext_cert.binder_ty })
                                      (drop param_count family_domains)
                                  in
                                  let rules =
                                    {
                                      Ext_cert.minor_start = param_count + 1;
                                      major_index =
                                        param_count + 1
                                        + List.length localized_constructors
                                        + List.length indices;
                                    }
                                  in
                                  let recursor =
                                    {
                                      Ext_cert.recursor_name;
                                      recursor_universe_params =
                                        recursor_export.Ext_import_store
                                        .public_universe_params;
                                      recursor_ty = localized_recursor_ty;
                                      recursor_rules = rules;
                                    }
                                  in
                                  bind
                                    (order_imported_constructors section offset
                                       fuel synthetic_decl_index
                                       inductive.Ext_import_store
                                       .public_universe_params params indices
                                       recursor_domains rules
                                       localized_constructors)
                                    (function
                                      | None ->
                                          try_param_count (param_count + 1)
                                      | Some ordered_constructors -> (
                                          match
                                            expected_recursor_type section offset
                                              synthetic_decl_index
                                              inductive.Ext_import_store
                                              .public_universe_params params
                                              indices ind_sort
                                              ordered_constructors recursor
                                          with
                                          | Ok expected_ty
                                            when expected_ty
                                                 = localized_recursor_ty ->
                                              Ok
                                                (Some
                                                   (Ext_env.Imported_single
                                                   {
                                                     imported_runtime_import_index =
                                                       import_index;
                                                     imported_runtime_decl_interface_hash =
                                                       decl_interface_hash;
                                                     imported_runtime_synthetic_decl_index =
                                                       synthetic_decl_index;
                                                     imported_runtime_universe_params =
                                                       inductive.Ext_import_store
                                                       .public_universe_params;
                                                     imported_runtime_params =
                                                       params;
                                                     imported_runtime_indices =
                                                       indices;
                                                     imported_runtime_constructors =
                                                       ordered_constructors;
                                                     imported_runtime_rules =
                                                       rules;
                                                   }))
                                          | Ok _ | Error _ ->
                                              try_param_count
                                                (param_count + 1))))
                          in
                          try_param_count 0
                      | Ext_term.Sort _ | Ext_term.BVar _ | Ext_term.Const _
                      | Ext_term.App _ | Ext_term.Lam _ | Ext_term.Pi _
                      | Ext_term.Let _ -> Ok None)))
      | _ -> Ok None)

let reconstruct_imported_recursor env section offset fuel import_index
    recursor_name decl_interface_hash =
  match
    Ext_env.find_imported_recursor_cache env import_index recursor_name
      decl_interface_hash
  with
  | Some runtime -> Ok runtime
  | None ->
      bind
        (reconstruct_imported_recursor_uncached env section offset fuel
           import_index recursor_name decl_interface_hash)
        (fun runtime ->
          Ext_env.cache_imported_recursor env import_index recursor_name
            decl_interface_hash runtime;
          Ok runtime)

let reduce_imported_mutual_recursor_iota env context section offset delta fuel
    args recursor_levels
    (runtime : Ext_env.imported_mutual_recursor_runtime) =
  let mutuals = runtime.imported_mutual_families in
  match list_nth_opt runtime.imported_mutual_target_index mutuals with
  | None -> Ok None
  | Some target ->
      let recursor = runtime.imported_mutual_recursor in
      let major_index = recursor.Ext_cert.recursor_rules.major_index in
      if List.length args <= major_index then Ok None
      else
        match list_nth_opt major_index args with
        | None -> Ok None
        | Some major ->
            bind
              (whnf_with_fuel env context section offset delta major fuel)
              (fun major_whnf ->
                let ctor_head, ctor_args = collect_apps major_whnf in
                match ctor_head with
                | Ext_term.Const
                    ( Ext_term.Imported
                        {
                          import_index = constructor_import_index;
                          name = constructor_name;
                          decl_interface_hash = constructor_hash;
                        },
                      _ )
                  when constructor_import_index
                       = runtime.imported_mutual_import_index
                       && constructor_hash
                          = runtime.imported_mutual_decl_interface_hash -> (
                    match
                      find_index
                        (fun constructor ->
                          Ext_name.equal
                            constructor.Ext_cert.constructor_name
                            constructor_name)
                        target.Ext_cert.mutual_constructors
                    with
                    | None -> Ok None
                    | Some constructor_index -> (
                        match
                          list_nth_opt constructor_index
                            target.Ext_cert.mutual_constructors
                        with
                        | None -> Ok None
                        | Some constructor ->
                            let constructor_offset =
                              List.fold_left
                                (fun count mutual ->
                                  count
                                  + List.length
                                      mutual.Ext_cert.mutual_constructors)
                                0
                                (take runtime.imported_mutual_target_index
                                   mutuals)
                            in
                            (match
                               list_nth_opt
                                 (recursor.Ext_cert.recursor_rules.minor_start
                                 + constructor_offset + constructor_index)
                                 args
                             with
                            | None -> Ok None
                            | Some minor ->
                                let domains, _ =
                                  peel_pi_domains
                                    constructor.Ext_cert.constructor_ty
                                in
                                let param_count =
                                  List.length target.Ext_cert.mutual_params
                                in
                                if List.length ctor_args < param_count then
                                  Ok None
                                else
                                  let field_domains =
                                    drop param_count domains
                                  in
                                  let field_args = drop param_count ctor_args in
                                  if
                                    List.length field_args
                                    < List.length field_domains
                                  then Ok None
                                  else
                                    let families =
                                      List.map
                                        (fun mutual ->
                                          Ext_inductive.named_family
                                            ~name:
                                              mutual.Ext_cert.mutual_name
                                            ~decl_index:
                                              runtime
                                                .imported_mutual_synthetic_decl_index
                                            ~universe_params:
                                              runtime
                                                .imported_mutual_universe_params
                                            ~param_count:
                                              (List.length
                                                 mutual.Ext_cert.mutual_params)
                                            ~index_count:
                                              (List.length
                                                 mutual.Ext_cert.mutual_indices))
                                        mutuals
                                    in
                                    let index_start =
                                      major_index
                                      - List.length
                                          target.Ext_cert.mutual_indices
                                    in
                                    let rec apply_fields field_index current
                                        remaining_args remaining_domains =
                                      match
                                        (remaining_args, remaining_domains)
                                      with
                                      | _, [] -> Ok current
                                      | ( field_arg :: rest_args,
                                          field_domain :: rest_domains ) ->
                                          let applied =
                                            Ext_term.App (current, field_arg)
                                          in
                                          (match
                                             Ext_inductive
                                             .direct_mutual_recursive_index_args
                                               families field_domain
                                               (param_count + field_index)
                                           with
                                          | None ->
                                              apply_fields (field_index + 1)
                                                applied rest_args rest_domains
                                          | Some
                                              ( field_family_index,
                                                recursive_indices ) -> (
                                              match
                                                list_nth_opt field_family_index
                                                  mutuals
                                              with
                                              | None -> Ok current
                                              | Some recursive_family -> (
                                                  match
                                                    recursive_family.Ext_cert
                                                    .mutual_recursor
                                                  with
                                                  | None -> Ok current
                                                  | Some recursive_recursor ->
                                                      let source_ctx_len =
                                                        param_count
                                                        + field_index
                                                      in
                                                      let source_args =
                                                        take source_ctx_len
                                                          ctor_args
                                                      in
                                                      let rec instantiate_indices
                                                          remaining accumulated =
                                                        match remaining with
                                                        | [] ->
                                                            Ok
                                                              (List.rev
                                                                 accumulated)
                                                        | index_arg :: rest ->
                                                            bind
                                                              (instantiate_constructor_args
                                                                 section offset
                                                                 index_arg
                                                                 source_args)
                                                              (fun instantiated ->
                                                                instantiate_indices
                                                                  rest
                                                                  (instantiated
                                                                  :: accumulated))
                                                      in
                                                      bind
                                                        (instantiate_indices
                                                           recursive_indices [])
                                                        (fun recursive_indices ->
                                                          let recursive_args =
                                                            take index_start
                                                              args
                                                            @ recursive_indices
                                                            @ [ field_arg ]
                                                          in
                                                          let recursive_call =
                                                            apply_args
                                                              (Ext_term.Const
                                                                 ( Ext_term
                                                                   .Imported
                                                                     {
                                                                       import_index =
                                                                         runtime
                                                                           .imported_mutual_import_index;
                                                                       name =
                                                                         recursive_recursor
                                                                           .Ext_cert
                                                                           .recursor_name;
                                                                       decl_interface_hash =
                                                                         runtime
                                                                           .imported_mutual_decl_interface_hash;
                                                                     },
                                                                   recursor_levels ))
                                                              recursive_args
                                                          in
                                                          apply_fields
                                                            (field_index + 1)
                                                            (Ext_term.App
                                                               ( applied,
                                                                 recursive_call ))
                                                            rest_args
                                                            rest_domains))))
                                      | [], _ :: _ -> Ok current
                                    in
                                    bind
                                      (apply_fields 0 minor field_args
                                         field_domains)
                                      (fun reduced ->
                                        Ok
                                          (Some
                                             (apply_args reduced
                                                (drop (major_index + 1) args)))))))
                | _ -> Ok None)

let reduce_imported_recursor_iota env context section offset delta term fuel =
  let head, args = collect_apps term in
  match head with
  | Ext_term.Const
      ( Ext_term.Imported
          { import_index; name = recursor_name; decl_interface_hash },
        recursor_levels ) ->
      bind
        (reconstruct_imported_recursor env section offset fuel import_index
           recursor_name decl_interface_hash)
        (function
          | None -> Ok None
          | Some (Ext_env.Imported_mutual runtime) ->
              reduce_imported_mutual_recursor_iota env context section offset
                delta fuel args recursor_levels runtime
          | Some (Ext_env.Imported_single runtime) ->
              let major_index =
                runtime.imported_runtime_rules.Ext_cert.major_index
              in
              if List.length args <= major_index then Ok None
              else
                match list_nth_opt major_index args with
                | None -> Ok None
                | Some major ->
                    bind
                      (whnf_with_fuel env context section offset delta major fuel)
                      (fun major_whnf ->
                        let ctor_head, ctor_args = collect_apps major_whnf in
                        match ctor_head with
                        | Ext_term.Const
                            ( Ext_term.Imported
                                {
                                  import_index = constructor_import_index;
                                  name = constructor_name;
                                  decl_interface_hash = constructor_hash;
                                },
                              _ )
                          when constructor_import_index
                               = runtime.imported_runtime_import_index
                               && constructor_hash
                                  = runtime
                                    .imported_runtime_decl_interface_hash -> (
                            match
                              find_index
                                (fun constructor ->
                                  Ext_name.equal
                                    constructor.Ext_cert.constructor_name
                                    constructor_name)
                                runtime.imported_runtime_constructors
                            with
                            | None -> Ok None
                            | Some constructor_index -> (
                                match
                                  ( list_nth_opt
                                      (runtime.imported_runtime_rules
                                         .Ext_cert.minor_start
                                      + constructor_index)
                                      args,
                                    list_nth_opt constructor_index
                                      runtime.imported_runtime_constructors )
                                with
                                | Some minor, Some constructor ->
                                    let domains, _ =
                                      peel_pi_domains
                                        constructor.Ext_cert.constructor_ty
                                    in
                                    let param_count =
                                      List.length
                                        runtime.imported_runtime_params
                                    in
                                    if List.length ctor_args < param_count then
                                      Ok None
                                    else
                                    let field_domains = drop param_count domains in
                                    let field_args = drop param_count ctor_args in
                                    if
                                      List.length field_args
                                      < List.length field_domains
                                    then Ok None
                                    else
                                      let family =
                                        Ext_inductive.family
                                          ~decl_index:
                                            runtime
                                              .imported_runtime_synthetic_decl_index
                                          ~universe_params:
                                            runtime
                                              .imported_runtime_universe_params
                                          ~param_count
                                          ~index_count:
                                            (List.length
                                               runtime
                                                 .imported_runtime_indices)
                                      in
                                      let index_start =
                                        major_index
                                        - List.length
                                            runtime.imported_runtime_indices
                                      in
                                      let rec apply_fields field_index current
                                          remaining_args remaining_domains =
                                        match
                                          (remaining_args, remaining_domains)
                                        with
                                        | _, [] -> Ok current
                                        | ( field_arg :: rest_args,
                                            field_domain :: rest_domains ) ->
                                            let applied =
                                              Ext_term.App
                                                (current, field_arg)
                                            in
                                            (match
                                               Ext_inductive
                                               .direct_recursive_index_args
                                                 family field_domain
                                                 (param_count + field_index)
                                             with
                                            | None ->
                                                apply_fields
                                                  (field_index + 1) applied
                                                  rest_args rest_domains
                                            | Some recursive_indices ->
                                                let source_ctx_len =
                                                  param_count + field_index
                                                in
                                                let source_args =
                                                  take source_ctx_len ctor_args
                                                in
                                                let rec instantiate_indices
                                                    remaining accumulated =
                                                  match remaining with
                                                  | [] ->
                                                      Ok
                                                        (List.rev accumulated)
                                                  | index_arg :: rest ->
                                                      bind
                                                        (instantiate_constructor_args
                                                           section offset
                                                           index_arg source_args)
                                                        (fun instantiated ->
                                                          instantiate_indices
                                                            rest
                                                            (instantiated
                                                            :: accumulated))
                                                in
                                                bind
                                                  (instantiate_indices
                                                     recursive_indices [])
                                                  (fun recursive_indices ->
                                                    let recursive_args =
                                                      take index_start args
                                                      @ recursive_indices
                                                      @ [ field_arg ]
                                                    in
                                                    let recursive_call =
                                                      apply_args
                                                        (Ext_term.Const
                                                           ( Ext_term.Imported
                                                               {
                                                                 import_index;
                                                                 name =
                                                                   recursor_name;
                                                                 decl_interface_hash;
                                                               },
                                                             recursor_levels ))
                                                        recursive_args
                                                    in
                                                    apply_fields
                                                      (field_index + 1)
                                                      (Ext_term.App
                                                         ( applied,
                                                           recursive_call ))
                                                      rest_args rest_domains))
                                        | [], _ :: _ -> Ok current
                                      in
                                      bind
                                        (apply_fields 0 minor field_args
                                           field_domains)
                                        (fun reduced ->
                                          Ok
                                            (Some
                                               (apply_args reduced
                                                  (drop (major_index + 1)
                                                     args))))
                                | _ -> Ok None))
                        | _ -> Ok None))
  | _ -> Ok None

let () = imported_recursor_iota_hook := reduce_imported_recursor_iota

let inductive_family_only_declaration (declaration : Ext_cert.declaration) =
  match declaration.Ext_cert.payload with
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
      {
        declaration with
        Ext_cert.payload =
          Ext_cert.InductiveDecl
            {
              decl_name;
              decl_universe_params;
              decl_universe_constraints;
              ind_params;
              ind_indices;
              ind_sort;
              ind_constructors = [];
              ind_recursor = None;
            };
      }
  | _ -> declaration

let inductive_without_recursor_declaration (declaration : Ext_cert.declaration) =
  match declaration.Ext_cert.payload with
  | Ext_cert.InductiveDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        ind_params;
        ind_indices;
        ind_sort;
        ind_constructors;
        _;
      } ->
      {
        declaration with
        Ext_cert.payload =
          Ext_cert.InductiveDecl
            {
              decl_name;
              decl_universe_params;
              decl_universe_constraints;
              ind_params;
              ind_indices;
              ind_sort;
              ind_constructors;
              ind_recursor = None;
            };
      }
  | _ -> declaration

let check_generated_constructor_interface section offset env decl_index delta
    decl_interface_hash constructor =
  let constructor_name = constructor.Ext_cert.constructor_name in
  bind
    (resolve_signature section offset env
       (Ext_term.LocalGenerated { decl_index; name = constructor_name }))
    (fun signature ->
      if not (Ext_name.equal signature.Ext_env.signature_name constructor_name)
      then error section offset Inductive_invalid
      else if
        signature.Ext_env.signature_decl_interface_hash
        <> Some decl_interface_hash
      then error section offset Inductive_invalid
      else if
        not (names_equal signature.Ext_env.signature_universe_params delta)
      then error section offset Inductive_invalid
      else if signature.Ext_env.signature_ty <> constructor.Ext_cert.constructor_ty
      then error section offset Inductive_invalid
      else
        match signature.Ext_env.signature_origin with
        | Ext_env.Local_generated { decl_index = origin_index; name }
          when origin_index = decl_index && Ext_name.equal name constructor_name ->
            Ok ()
        | _ -> error section offset Inductive_invalid)

let rec check_generated_constructor_interfaces section offset env decl_index delta
    decl_interface_hash constructors =
  match constructors with
  | [] -> Ok ()
  | constructor :: rest ->
      bind
        (check_generated_constructor_interface section offset env decl_index delta
           decl_interface_hash constructor)
        (fun () ->
          check_generated_constructor_interfaces section offset env decl_index delta
            decl_interface_hash rest)

let check_generated_recursor_interface section offset env decl_index
    decl_interface_hash recursor =
  let recursor_name = recursor.Ext_cert.recursor_name in
  bind
    (resolve_signature section offset env
       (Ext_term.LocalGenerated { decl_index; name = recursor_name }))
    (fun signature ->
      if not (Ext_name.equal signature.Ext_env.signature_name recursor_name)
      then error section offset Inductive_invalid
      else if
        signature.Ext_env.signature_decl_interface_hash
        <> Some decl_interface_hash
      then error section offset Inductive_invalid
      else if
        not
          (names_equal signature.Ext_env.signature_universe_params
             recursor.Ext_cert.recursor_universe_params)
      then error section offset Inductive_invalid
      else if signature.Ext_env.signature_ty <> recursor.Ext_cert.recursor_ty
      then error section offset Inductive_invalid
      else
        match signature.Ext_env.signature_origin with
        | Ext_env.Local_generated { decl_index = origin_index; name }
          when origin_index = decl_index && Ext_name.equal name recursor_name ->
            Ok ()
        | _ -> error section offset Inductive_invalid)

let ensure_mutual_names_unique section offset decl_name mutuals =
  let rec add_name seen name =
    if has_name name seen then Error seen else Ok (name :: seen)
  in
  let rec add_constructors seen constructors =
    match constructors with
    | [] -> Ok seen
    | constructor :: rest ->
        (match add_name seen constructor.Ext_cert.constructor_name with
        | Error _ -> error section offset Inductive_invalid
        | Ok next -> add_constructors next rest)
  in
  let rec loop seen remaining =
    match remaining with
    | [] -> Ok ()
    | mutual :: rest ->
        (match add_name seen mutual.Ext_cert.mutual_name with
        | Error _ -> error section offset Inductive_invalid
        | Ok seen ->
            bind
              (add_constructors seen mutual.Ext_cert.mutual_constructors)
              (fun seen ->
                match mutual.Ext_cert.mutual_recursor with
                | None -> loop seen rest
                | Some recursor ->
                    (match add_name seen recursor.Ext_cert.recursor_name with
                    | Error _ -> error section offset Inductive_invalid
                    | Ok seen -> loop seen rest)))
  in
  loop [ decl_name ] mutuals

let ensure_shared_mutual_params section offset mutuals =
  match mutuals with
  | [] -> error section offset Inductive_invalid
  | first :: rest ->
      let expected = first.Ext_cert.mutual_params in
      let rec loop remaining =
        match remaining with
        | [] -> Ok ()
        | mutual :: tail ->
            if mutual.Ext_cert.mutual_params = expected then loop tail
            else error section offset Inductive_invalid
      in
      loop rest

let map_mutual_inductives declaration map =
  match declaration.Ext_cert.payload with
  | Ext_cert.MutualInductiveBlockDecl
      {
        decl_name;
        decl_universe_params;
        decl_universe_constraints;
        mutual_inductives;
      } ->
      {
        declaration with
        Ext_cert.payload =
          Ext_cert.MutualInductiveBlockDecl
            {
              decl_name;
              decl_universe_params;
              decl_universe_constraints;
              mutual_inductives = List.map map mutual_inductives;
            };
      }
  | _ -> declaration

let mutual_families_only_declaration declaration =
  map_mutual_inductives declaration (fun mutual ->
      {
        mutual with
        Ext_cert.mutual_constructors = [];
        mutual_recursor = None;
      })

let mutual_without_recursors_declaration declaration =
  map_mutual_inductives declaration (fun mutual ->
      { mutual with Ext_cert.mutual_recursor = None })

let check_mutual_family_shapes section offset env delta universe_context mutuals =
  let rec loop remaining =
    match remaining with
    | [] -> Ok ()
    | mutual :: rest ->
        bind
          (ensure_level_wf section offset delta mutual.Ext_cert.mutual_sort)
          (fun () ->
            let family_ty =
              Ext_env.pi_of_binders
                (mutual.Ext_cert.mutual_params
                @ mutual.Ext_cert.mutual_indices)
                (Ext_term.Sort mutual.Ext_cert.mutual_sort)
            in
            bind
              (expect_sort ~section ~offset ~delta ~universe_context env
                 empty_context family_ty)
              (fun _ -> loop rest))
  in
  loop mutuals

let check_mutual_constructor section offset env decl_index delta
    universe_context families owner constructor =
  bind
    (expect_sort ~section ~offset ~delta ~universe_context env empty_context
       constructor.Ext_cert.constructor_ty)
    (fun _ ->
      let domains, result =
        peel_pi_domains constructor.Ext_cert.constructor_ty
      in
      let owner_family = mutual_family decl_index delta owner in
      match
        Ext_inductive.check_mutual_constructor_domains env owner_family families
          domains
      with
      | Error Ext_inductive.Non_positive_occurrence ->
          error section offset Positivity_failure
      | Ok () ->
          bind (whnf ~section ~offset ~delta env empty_context result)
            (fun result ->
              bind
                (check_constructor_result_for_family section offset owner_family
                   delta (List.length owner.Ext_cert.mutual_params)
                   (List.length owner.Ext_cert.mutual_indices)
                   (List.length domains) result)
                (fun () ->
                  check_constructor_universe_bounds section offset env delta
                    universe_context
                    (List.length owner.Ext_cert.mutual_params)
                    owner.Ext_cert.mutual_sort domains)))

let check_mutual_constructors section offset env decl_index delta
    universe_context mutuals =
  let families = List.map (mutual_family decl_index delta) mutuals in
  let rec check_family remaining =
    match remaining with
    | [] -> Ok ()
    | owner :: rest ->
        let rec check_members constructors =
          match constructors with
          | [] -> check_family rest
          | constructor :: tail ->
              bind
                (check_mutual_constructor section offset env decl_index delta
                   universe_context families owner constructor)
                (fun () -> check_members tail)
        in
        check_members owner.Ext_cert.mutual_constructors
  in
  check_family mutuals

let check_mutual_recursors section offset env decl_index delta
    universe_constraints mutuals =
  let rec loop target_index remaining =
    match remaining with
    | [] -> Ok ()
    | mutual :: rest ->
        (match mutual.Ext_cert.mutual_recursor with
        | None -> error section offset Inductive_invalid
        | Some recursor ->
            bind
              (check_mutual_recursor_declaration section offset env decl_index
                 delta universe_constraints mutuals target_index recursor)
              (fun () -> loop (target_index + 1) rest))
  in
  loop 0 mutuals

let check_generated_mutual_family_interface section offset env decl_index delta
    decl_interface_hash mutual =
  let family_name = mutual.Ext_cert.mutual_name in
  bind
    (resolve_signature section offset env
       (Ext_term.LocalGenerated { decl_index; name = family_name }))
    (fun signature ->
      let expected_ty =
        Ext_env.pi_of_binders
          (mutual.Ext_cert.mutual_params @ mutual.Ext_cert.mutual_indices)
          (Ext_term.Sort mutual.Ext_cert.mutual_sort)
      in
      if not (Ext_name.equal signature.Ext_env.signature_name family_name) then
        error section offset Inductive_invalid
      else if
        signature.Ext_env.signature_decl_interface_hash
        <> Some decl_interface_hash
      then error section offset Inductive_invalid
      else if
        not (names_equal signature.Ext_env.signature_universe_params delta)
      then error section offset Inductive_invalid
      else if signature.Ext_env.signature_ty <> expected_ty then
        error section offset Inductive_invalid
      else
        match signature.Ext_env.signature_origin with
        | Ext_env.Local_generated { decl_index = origin_index; name }
          when origin_index = decl_index && Ext_name.equal name family_name ->
            Ok ()
        | _ -> error section offset Inductive_invalid)

let check_generated_mutual_interfaces section offset env decl_index delta
    decl_interface_hash mutuals =
  let rec loop remaining =
    match remaining with
    | [] -> Ok ()
    | mutual :: rest ->
        bind
          (check_generated_mutual_family_interface section offset env decl_index
             delta decl_interface_hash mutual)
          (fun () ->
            bind
              (check_generated_constructor_interfaces section offset env
                 decl_index delta decl_interface_hash
                 mutual.Ext_cert.mutual_constructors)
              (fun () ->
                match mutual.Ext_cert.mutual_recursor with
                | None -> error section offset Inductive_invalid
                | Some recursor ->
                    bind
                      (check_generated_recursor_interface section offset env
                         decl_index decl_interface_hash recursor)
                      (fun () -> loop rest)))
  in
  loop mutuals

let check_mutual_inductive_declaration universe_context env
    (declaration : Ext_cert.declaration) =
  let section = Ext_bytes.Declarations in
  let offset = declaration.Ext_cert.offset in
  let decl_index = env.Ext_env.checked_declaration_count in
  let decl_interface_hash =
    declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
  in
  match declaration.Ext_cert.payload with
  | Ext_cert.MutualInductiveBlockDecl
      {
        decl_name;
        decl_universe_params = delta;
        decl_universe_constraints;
        mutual_inductives;
      } ->
      bind (ensure_shared_mutual_params section offset mutual_inductives)
        (fun () ->
          bind
            (ensure_mutual_names_unique section offset decl_name
               mutual_inductives)
            (fun () ->
              bind
                (add_checked_declaration env
                   (mutual_families_only_declaration declaration))
                (fun family_env ->
                  bind
                    (check_mutual_family_shapes section offset family_env delta
                       universe_context mutual_inductives)
                    (fun () ->
                      bind
                        (check_mutual_constructors section offset family_env
                           decl_index delta universe_context mutual_inductives)
                        (fun () ->
                          bind
                            (add_checked_declaration env
                               (mutual_without_recursors_declaration declaration))
                            (fun constructor_env ->
                              bind
                                (check_mutual_recursors section offset
                                   constructor_env decl_index delta
                                   decl_universe_constraints mutual_inductives)
                                (fun () ->
                                  bind
                                    (add_checked_declaration env declaration)
                                    (fun checked_env ->
                                      bind
                                        (check_generated_mutual_interfaces
                                           section offset checked_env decl_index
                                           delta decl_interface_hash
                                           mutual_inductives)
                                        (fun () -> Ok checked_env)))))))))
  | _ -> error section offset Unsupported_declaration

let check_inductive_declaration universe_context env
    (declaration : Ext_cert.declaration) =
  let section = Ext_bytes.Declarations in
  let offset = declaration.Ext_cert.offset in
  let decl_index = env.Ext_env.checked_declaration_count in
  let decl_interface_hash =
    declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
  in
  match declaration.Ext_cert.payload with
  | Ext_cert.InductiveDecl
      {
        decl_name;
        decl_universe_params = delta;
        decl_universe_constraints;
        ind_params;
        ind_indices;
        ind_sort;
        ind_constructors;
        ind_recursor;
        _;
      } ->
      let family_ty =
        Ext_env.pi_of_binders (ind_params @ ind_indices)
          (Ext_term.Sort ind_sort)
      in
      let family_declaration = inductive_family_only_declaration declaration in
      let constructor_declaration =
        inductive_without_recursor_declaration declaration
      in
      (match ensure_level_wf section offset delta ind_sort with
      | Error err -> Error err
      | Ok () -> (
          match
            ensure_constructor_names_unique section offset decl_name
              ind_constructors
          with
          | Error err -> Error err
          | Ok () -> (
              match
                expect_sort ~section ~offset ~delta ~universe_context env
                  empty_context family_ty
              with
              | Error err -> Error err
              | Ok _ -> (
                  match add_checked_declaration env family_declaration with
                  | Error err -> Error err
                  | Ok family_env -> (
                      match
                        check_constructors section offset family_env delta
                          universe_context decl_index ind_params ind_indices
                          ind_sort ind_constructors
                      with
                      | Error err -> Error err
                      | Ok () -> (
                          match
                            add_checked_declaration env constructor_declaration
                          with
                          | Error err -> Error err
                          | Ok constructor_env -> (
                              match
                                (match ind_recursor with
                                | None -> Ok ()
                                | Some recursor ->
                                    check_recursor_declaration section offset
                                      constructor_env decl_index delta
                                      decl_universe_constraints ind_params ind_indices
                                      ind_sort ind_constructors recursor)
                              with
                              | Error err -> Error err
                              | Ok () -> (
                                  match add_checked_declaration env declaration with
                                  | Error err -> Error err
                                  | Ok checked_env -> (
                                      match
                                        check_generated_constructor_interfaces
                                          section offset checked_env decl_index
                                          delta decl_interface_hash
                                          ind_constructors
                                      with
                                      | Error err -> Error err
                                      | Ok () -> (
                                          match ind_recursor with
                                          | None -> Ok checked_env
                                          | Some recursor -> (
                                              match
                                                check_generated_recursor_interface
                                                  section offset checked_env
                                                  decl_index decl_interface_hash
                                                  recursor
                                              with
                                              | Error err -> Error err
                                              | Ok () -> Ok checked_env)))))))))))
  | _ -> error section offset Unsupported_declaration

let check_declaration env (declaration : Ext_cert.declaration) =
  let section = Ext_bytes.Declarations in
  let offset = declaration.Ext_cert.offset in
  bind
    (check_dependencies section offset env declaration.Ext_cert.dependencies)
    (fun () ->
      let delta = Ext_env.declaration_universe_params declaration.Ext_cert.payload in
      let universe_constraints =
        declaration_universe_constraints declaration.Ext_cert.payload
      in
      match Ext_universe.create delta universe_constraints with
      | Error universe_error ->
          error_of_universe_error section offset universe_error
      | Ok universe_context ->
              match declaration.Ext_cert.payload with
              | Ext_cert.AxiomDecl { decl_ty; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta ~universe_context env
                       empty_context decl_ty)
                    (fun _ -> add_checked_declaration env declaration)
              | Ext_cert.DefDecl { decl_ty; decl_value; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta ~universe_context env
                       empty_context decl_ty)
                    (fun _ ->
                      bind
                        (check ~section ~offset ~delta ~universe_context env
                           empty_context decl_value decl_ty)
                        (fun () -> add_checked_declaration env declaration))
              | Ext_cert.TheoremDecl { decl_ty; decl_proof; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta ~universe_context env
                       empty_context decl_ty)
                    (fun _ ->
                      bind
                        (check ~section ~offset ~delta ~universe_context env
                           empty_context decl_proof decl_ty)
                        (fun () -> add_checked_declaration env declaration))
              | Ext_cert.InductiveDecl _ ->
                  check_inductive_declaration universe_context env declaration
              | Ext_cert.MutualInductiveBlockDecl _ ->
                  check_mutual_inductive_declaration universe_context env
                    declaration)

let check_declarations ?(env = Ext_env.empty) declarations =
  let rec loop current_env remaining =
    match remaining with
    | [] -> Ok current_env
    | declaration :: rest ->
        bind (check_declaration current_env declaration) (fun next_env ->
            loop next_env rest)
  in
  loop env declarations

let check_certificate env (certificate : Ext_cert.decoded_module) =
  check_declarations ~env certificate.Ext_cert.declaration_table
