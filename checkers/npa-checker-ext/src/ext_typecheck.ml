type check_result =
  | Type_checked
  | Type_check_not_implemented

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
  | Resource_limit -> "resource_limit"

let error_kind error =
  match error.reason with
  | Bad_universe_arity | Duplicate_universe_param | Unresolved_metavariable ->
      "universe_inconsistency"
  | Unknown_reference | Invalid_bvar | Expected_sort | Expected_function | Type_mismatch
  | Unsupported_declaration ->
      "type_mismatch"
  | Inductive_invalid -> "inductive_invalid"
  | Positivity_failure -> "positivity_failure"
  | Resource_limit -> "conversion_failure"

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

let global_ref_equal left right =
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
                            | None -> Ok app
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
                ind_indices <> []
                || not
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
                                          ~param_count ~index_count:0
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
                                            if
                                              Ext_inductive.direct_recursive_domain family
                                                field_domain
                                                (param_count + field_index)
                                            then
                                              let recursive_args =
                                                take major_index args
                                                @ [ field_arg ]
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
                                                rest_args rest_domains
                                            else
                                              loop (field_index + 1) applied
                                                rest_args rest_domains
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
          | _ -> Ok None))
  | _ -> Ok None

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
                  Ok (levels_equal lhs_levels rhs_levels && global_ref_equal lhs_ref rhs_ref)
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

let rec infer ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = []) env context
    term =
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
                Ok
                  (subst_levels_term signature.Ext_env.signature_universe_params levels
                     signature.Ext_env.signature_ty)))
  | Ext_term.Pi (ty, body) ->
      bind (expect_sort ~section ~offset ~delta env context ty) (fun domain_sort ->
          let body_context = push_assumption context ty in
          bind
            (expect_sort ~section ~offset ~delta env body_context body)
            (fun body_sort -> Ok (Ext_term.Sort (Ext_level.Imax (domain_sort, body_sort)))))
  | Ext_term.Lam (ty, body) ->
      bind (expect_sort ~section ~offset ~delta env context ty) (fun _ ->
          let body_context = push_assumption context ty in
          bind (infer ~section ~offset ~delta env body_context body) (fun body_ty ->
              Ok (Ext_term.Pi (ty, body_ty))))
  | Ext_term.App (fn, arg) ->
      bind (infer ~section ~offset ~delta env context fn) (fun fn_ty ->
          bind (whnf ~section ~offset ~delta env context fn_ty) (function
            | Ext_term.Pi (domain_ty, body_ty) ->
                bind (check ~section ~offset ~delta env context arg domain_ty) (fun () ->
                    instantiate section offset body_ty arg)
            | _ -> error section offset Expected_function))
  | Ext_term.Let (ty, value, body) ->
      bind (expect_sort ~section ~offset ~delta env context ty) (fun _ ->
          bind (check ~section ~offset ~delta env context value ty) (fun () ->
              let body_context = push_definition context ty value in
              bind (infer ~section ~offset ~delta env body_context body) (fun body_ty ->
                  instantiate section offset body_ty value)))

and check ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = []) env context term
    expected =
  match term with
  | Ext_term.Lam (ty, body) ->
      bind (whnf ~section ~offset ~delta env context expected) (function
        | Ext_term.Pi (expected_ty, expected_body) ->
            bind (expect_sort ~section ~offset ~delta env context ty) (fun _ ->
                bind (is_defeq ~section ~offset ~delta env context ty expected_ty)
                  (fun domain_equal ->
                    if not domain_equal then error section offset Type_mismatch
                    else
                      let body_context = push_assumption context ty in
                      check ~section ~offset ~delta env body_context body expected_body))
        | _ -> error section offset Type_mismatch)
  | _ ->
      bind (infer ~section ~offset ~delta env context term) (fun actual ->
          bind (is_defeq ~section ~offset ~delta env context actual expected) (fun equal ->
              if equal then Ok () else error section offset Type_mismatch))

and expect_sort ?(section = Ext_bytes.Declarations) ?(offset = 0) ?(delta = []) env context
    term =
  bind (infer ~section ~offset ~delta env context term) (fun ty ->
      bind (whnf ~section ~offset ~delta env context ty) (function
        | Ext_term.Sort level -> Ok level
        | _ -> error section offset Expected_sort))

let rec ensure_delta_wf section offset params =
  match params with
  | [] -> Ok ()
  | name :: rest ->
      if Ext_level.component_contains_universe_meta name then
        error section offset Unresolved_metavariable
      else ensure_delta_wf section offset rest

let declaration_universe_constraints payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_universe_constraints; _ }
  | Ext_cert.DefDecl { decl_universe_constraints; _ }
  | Ext_cert.TheoremDecl { decl_universe_constraints; _ }
  | Ext_cert.InductiveDecl { decl_universe_constraints; _ }
  | Ext_cert.MutualInductiveBlockDecl { decl_universe_constraints; _ } ->
      decl_universe_constraints

let rec ensure_constraints_wf section offset delta constraints =
  match constraints with
  | [] -> Ok ()
  | constraint_ :: rest ->
      bind
        (ensure_level_wf section offset delta constraint_.Ext_cert.constraint_lhs)
        (fun () ->
          bind
            (ensure_level_wf section offset delta
               constraint_.Ext_cert.constraint_rhs)
            (fun () -> ensure_constraints_wf section offset delta rest))

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

let check_constructor_result section offset decl_index delta param_count index_count
    domain_count result =
  let head, args = collect_apps result in
  let expected_ref = Ext_term.Local { decl_index } in
  let expected_levels = universe_param_levels delta in
  match head with
  | Ext_term.Const (global_ref, levels)
    when global_ref_equal global_ref expected_ref
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

let check_constructor section offset env delta decl_index params indices constructor =
  bind
    (expect_sort ~section ~offset ~delta env empty_context
       constructor.Ext_cert.constructor_ty)
    (fun _ ->
      let domains, result = peel_pi_domains constructor.Ext_cert.constructor_ty in
      let family =
        Ext_inductive.family ~decl_index ~universe_params:delta
          ~param_count:(List.length params) ~index_count:(List.length indices)
      in
      match Ext_inductive.check_constructor_domains family domains with
      | Error Ext_inductive.Non_positive_occurrence ->
          error section offset Positivity_failure
      | Ok () ->
          bind (whnf ~section ~offset ~delta env empty_context result) (fun result ->
              check_constructor_result section offset decl_index delta
                (List.length params) (List.length indices) (List.length domains)
                result))

let rec check_constructors section offset env delta decl_index params indices constructors =
  match constructors with
  | [] -> Ok ()
  | constructor :: rest ->
      bind
        (check_constructor section offset env delta decl_index params indices constructor)
        (fun () ->
          check_constructors section offset env delta decl_index params indices rest)

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

let inductive_target_expr section offset decl_index delta param_count ctx_len =
  let head =
    Ext_term.Const (Ext_term.Local { decl_index }, universe_param_levels delta)
  in
  let rec collect param_abs args =
    if param_abs = param_count then Ok (List.rev args)
    else
      bind (bvar_for_abs section offset ctx_len param_abs) (fun arg ->
          collect (param_abs + 1) (arg :: args))
  in
  bind (collect 0 []) (fun args -> Ok (apply_args head args))

let motive_app section offset ctx_len motive_abs target =
  bind (bvar_for_abs section offset ctx_len motive_abs) (fun motive ->
      Ok (Ext_term.App (motive, target)))

let motive_domain_expr section offset decl_index delta param_count motive_level =
  bind
    (inductive_target_expr section offset decl_index delta param_count param_count)
    (fun target -> Ok (Ext_term.Pi (target, Ext_term.Sort motive_level)))

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

let expected_minor_type section offset decl_index delta params indices constructor_index
    constructor =
  let param_count = List.length params in
  let index_count = List.length indices in
  if index_count <> 0 then error section offset Unsupported_declaration
  else
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
          if result_index_args <> [] then error section offset Unsupported_declaration
          else
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
                      if
                        Ext_inductive.direct_recursive_domain family field_domain
                          source_ctx_len
                      then
                        bind
                          (motive_app section offset !target_ctx_len motive_abs
                             (Ext_term.BVar 0))
                          (fun ih_domain ->
                            expected_domains := ih_domain :: !expected_domains;
                            target_ctx_len := !target_ctx_len + 1;
                            add_fields (field_index + 1) rest)
                      else add_fields (field_index + 1) rest)
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
                        bind
                          (motive_app section offset !target_ctx_len motive_abs
                             constructor_value)
                          (fun result ->
                            Ok
                              (mk_pi_from_domains
                                 (List.rev !expected_domains)
                                 result))))))

let expected_recursor_type section offset decl_index delta ind_params ind_indices
    ind_sort ind_constructors recursor =
  let param_count = List.length ind_params in
  if ind_indices <> [] then error section offset Unsupported_declaration
  else
    let motive_level =
      expected_motive_level ind_sort recursor.Ext_cert.recursor_universe_params delta
    in
    let param_domains = List.map (fun param -> param.Ext_cert.binder_ty) ind_params in
    match
      motive_domain_expr section offset decl_index delta param_count motive_level
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
            match
              inductive_target_expr section offset decl_index delta param_count
                (List.length domains)
            with
            | Error err -> Error err
            | Ok major_domain -> (
                let domains = domains @ [ major_domain ] in
                match
                  bvar_for_abs section offset (List.length domains)
                    recursor.Ext_cert.recursor_rules.major_index
                with
                | Error err -> Error err
                | Ok major -> (
                    match
                      motive_app section offset (List.length domains) param_count
                        major
                    with
                    | Error err -> Error err
                    | Ok result -> Ok (mk_pi_from_domains domains result)))))

let check_recursor_declaration section offset env decl_index delta ind_params ind_indices
    ind_sort ind_constructors recursor =
  if ind_indices <> [] then error section offset Unsupported_declaration
  else
    let param_count = List.length ind_params in
    let constructor_count = List.length ind_constructors in
    let expected_minor_start = param_count + 1 in
    let expected_major_index = expected_minor_start + constructor_count in
    let domains, _ = peel_pi_domains recursor.Ext_cert.recursor_ty in
    if recursor.Ext_cert.recursor_rules.minor_start <> expected_minor_start then
      error section offset Inductive_invalid
    else if
      recursor.Ext_cert.recursor_rules.major_index <> expected_major_index
    then error section offset Inductive_invalid
    else if List.length domains <> expected_major_index + 1 then
      error section offset Inductive_invalid
    else
      bind
        (ensure_delta_wf section offset recursor.Ext_cert.recursor_universe_params)
        (fun () ->
          bind
            (expected_recursor_type section offset decl_index delta ind_params
               ind_indices ind_sort ind_constructors recursor)
            (fun expected_ty ->
              if recursor.Ext_cert.recursor_ty <> expected_ty then
                error section offset Inductive_invalid
              else
                bind
                  (expect_sort ~section ~offset
                     ~delta:recursor.Ext_cert.recursor_universe_params env
                     empty_context recursor.Ext_cert.recursor_ty)
                  (fun _ -> Ok ())))

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

let check_inductive_declaration env (declaration : Ext_cert.declaration) =
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
                expect_sort ~section ~offset ~delta env empty_context family_ty
              with
              | Error err -> Error err
              | Ok _ -> (
                  match add_checked_declaration env family_declaration with
                  | Error err -> Error err
                  | Ok family_env -> (
                      match
                        check_constructors section offset family_env delta
                          decl_index ind_params ind_indices ind_constructors
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
                                      constructor_env decl_index delta ind_params
                                      ind_indices ind_sort ind_constructors
                                      recursor)
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
      bind (ensure_delta_wf section offset delta) (fun () ->
          bind
            (ensure_constraints_wf section offset delta
               (declaration_universe_constraints declaration.Ext_cert.payload))
            (fun () ->
              match declaration.Ext_cert.payload with
              | Ext_cert.AxiomDecl { decl_ty; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta env empty_context decl_ty)
                    (fun _ -> add_checked_declaration env declaration)
              | Ext_cert.DefDecl { decl_ty; decl_value; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta env empty_context decl_ty)
                    (fun _ ->
                      bind
                        (check ~section ~offset ~delta env empty_context decl_value
                           decl_ty)
                        (fun () -> add_checked_declaration env declaration))
              | Ext_cert.TheoremDecl { decl_ty; decl_proof; _ } ->
                  bind
                    (expect_sort ~section ~offset ~delta env empty_context decl_ty)
                    (fun _ ->
                      bind
                        (check ~section ~offset ~delta env empty_context decl_proof
                           decl_ty)
                        (fun () -> add_checked_declaration env declaration))
              | Ext_cert.InductiveDecl _ -> check_inductive_declaration env declaration
              | Ext_cert.MutualInductiveBlockDecl _ ->
                  error section offset Unsupported_declaration)))

let check_declarations ?(env = Ext_env.empty) declarations =
  let rec loop current_env remaining =
    match remaining with
    | [] -> Ok current_env
    | declaration :: rest ->
        bind (check_declaration current_env declaration) (fun next_env ->
            loop next_env rest)
  in
  loop env declarations

let check_certificate _env _certificate = Type_check_not_implemented
