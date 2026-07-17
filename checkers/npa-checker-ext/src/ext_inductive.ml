type positivity_error = Non_positive_occurrence

type family = {
  family_decl_index : int;
  family_name : Ext_name.t option;
  family_universe_params : Ext_name.t list;
  family_param_count : int;
  family_index_count : int;
}

let make_family name ~decl_index ~universe_params ~param_count ~index_count =
  {
    family_decl_index = decl_index;
    family_name = name;
    family_universe_params = universe_params;
    family_param_count = param_count;
    family_index_count = index_count;
  }

let family ~decl_index ~universe_params ~param_count ~index_count =
  make_family None ~decl_index ~universe_params ~param_count ~index_count

let named_family ~name ~decl_index ~universe_params ~param_count ~index_count =
  make_family (Some name) ~decl_index ~universe_params ~param_count ~index_count

let levels_equal lhs rhs =
  List.length lhs = List.length rhs
  && List.for_all2
       (fun left right -> Ext_level.normalize left = Ext_level.normalize right)
       lhs rhs

let family_ref family global_ref =
  match (family.family_name, global_ref) with
  | None, Ext_term.Local { decl_index } -> decl_index = family.family_decl_index
  | ( Some expected_name,
      Ext_term.LocalGenerated { decl_index; name } ) ->
      decl_index = family.family_decl_index && Ext_name.equal name expected_name
  | _ -> false

let rec find_family_index global_ref families =
  match families with
  | [] -> None
  | family :: rest ->
      if family_ref family global_ref then Some 0
      else
        (match find_family_index global_ref rest with
        | None -> None
        | Some index -> Some (index + 1))

let rec contains_any_recursive_const families term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> false
  | Ext_term.Const (global_ref, _) -> find_family_index global_ref families <> None
  | Ext_term.App (fn, arg) ->
      contains_any_recursive_const families fn
      || contains_any_recursive_const families arg
  | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
      contains_any_recursive_const families ty
      || contains_any_recursive_const families body
  | Ext_term.Let (ty, value, body) ->
      contains_any_recursive_const families ty
      || contains_any_recursive_const families value
      || contains_any_recursive_const families body

let collect_apps term =
  let rec loop current args =
    match current with
    | Ext_term.App (fn, arg) -> loop fn (arg :: args)
    | _ -> (current, args)
  in
  loop term []

let apply_args fn args =
  List.fold_left (fun current arg -> Ext_term.App (current, arg)) fn args

let approved_family_const decl_index level args =
  apply_args
    (Ext_term.Const (Ext_term.Local { decl_index }, [ level ]))
    args

let approved_list_decl decl_index universe_params universe_constraints params
    indices sort constructors =
  match universe_params with
  | [ universe_name ] ->
      let u = Ext_level.Param universe_name in
      let list_of args = approved_family_const decl_index u args in
      universe_constraints = []
      && params = [ { Ext_cert.binder_ty = Ext_term.Sort u } ]
      && indices = []
      && Ext_level.normalize sort = Ext_level.normalize u
      &&
      (match constructors with
      | [ nil; cons ] ->
          Ext_name.to_string nil.Ext_cert.constructor_name = "List.nil"
          && nil.Ext_cert.constructor_ty
             = Ext_term.Pi
                 (Ext_term.Sort u, list_of [ Ext_term.BVar 0 ])
          && Ext_name.to_string cons.Ext_cert.constructor_name = "List.cons"
          && cons.Ext_cert.constructor_ty
             = Ext_term.Pi
                 ( Ext_term.Sort u,
                   Ext_term.Pi
                     ( Ext_term.BVar 0,
                       Ext_term.Pi
                         ( list_of [ Ext_term.BVar 1 ],
                           list_of [ Ext_term.BVar 2 ] ) ) )
      | _ -> false)
  | _ -> false

let approved_option_decl decl_index universe_params universe_constraints params
    indices sort constructors =
  match universe_params with
  | [ universe_name ] ->
      let u = Ext_level.Param universe_name in
      let option_of args = approved_family_const decl_index u args in
      universe_constraints = []
      && params = [ { Ext_cert.binder_ty = Ext_term.Sort u } ]
      && indices = []
      && Ext_level.normalize sort = Ext_level.normalize u
      &&
      (match constructors with
      | [ none; some ] ->
          Ext_name.to_string none.Ext_cert.constructor_name = "Option.none"
          && none.Ext_cert.constructor_ty
             = Ext_term.Pi
                 (Ext_term.Sort u, option_of [ Ext_term.BVar 0 ])
          && Ext_name.to_string some.Ext_cert.constructor_name = "Option.some"
          && some.Ext_cert.constructor_ty
             = Ext_term.Pi
                 ( Ext_term.Sort u,
                   Ext_term.Pi
                     (Ext_term.BVar 0, option_of [ Ext_term.BVar 1 ]) )
      | _ -> false)
  | _ -> false

let approved_prod_decl decl_index universe_params universe_constraints params
    indices sort constructors =
  match universe_params with
  | [ universe_name ] ->
      let u = Ext_level.Param universe_name in
      let prod_of args = approved_family_const decl_index u args in
      universe_constraints = []
      && params
         = [
             { Ext_cert.binder_ty = Ext_term.Sort u };
             { Ext_cert.binder_ty = Ext_term.Sort u };
           ]
      && indices = []
      && Ext_level.normalize sort = Ext_level.normalize u
      &&
      (match constructors with
      | [ constructor ] ->
          Ext_name.to_string constructor.Ext_cert.constructor_name = "Prod.mk"
          && constructor.Ext_cert.constructor_ty
             = Ext_term.Pi
                 ( Ext_term.Sort u,
                   Ext_term.Pi
                     ( Ext_term.Sort u,
                       Ext_term.Pi
                         ( Ext_term.BVar 1,
                           Ext_term.Pi
                             ( Ext_term.BVar 1,
                               prod_of
                                 [ Ext_term.BVar 3; Ext_term.BVar 2 ] ) ) ) )
      | _ -> false)
  | _ -> false

let approved_nested_functor env global_ref arity =
  match global_ref with
  | Ext_term.Local { decl_index } -> (
      match
        Ext_env.find_local_declaration decl_index env.Ext_env.local_declarations
      with
      | Some
          {
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
                  _;
                };
            _;
          } -> (
          match (Ext_name.to_string decl_name, arity) with
          | "List", 1 ->
              approved_list_decl decl_index decl_universe_params
                decl_universe_constraints ind_params ind_indices ind_sort
                ind_constructors
          | "Option", 1 ->
              approved_option_decl decl_index decl_universe_params
                decl_universe_constraints ind_params ind_indices ind_sort
                ind_constructors
          | "Prod", 2 ->
              approved_prod_decl decl_index decl_universe_params
                decl_universe_constraints ind_params ind_indices ind_sort
                ind_constructors
          | _ -> false)
      | _ -> false)
  | Ext_term.Builtin _ | Ext_term.Imported _ | Ext_term.LocalGenerated _ ->
      false

let rec contains_recursive_const family term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> false
  | Ext_term.Const (global_ref, _) -> family_ref family global_ref
  | Ext_term.App (fn, arg) ->
      contains_recursive_const family fn || contains_recursive_const family arg
  | Ext_term.Lam (ty, body) | Ext_term.Pi (ty, body) ->
      contains_recursive_const family ty || contains_recursive_const family body
  | Ext_term.Let (ty, value, body) ->
      contains_recursive_const family ty
      || contains_recursive_const family value
      || contains_recursive_const family body

let bvar_for_abs ctx_len abs_index =
  if abs_index < 0 || abs_index >= ctx_len then None
  else Some (Ext_term.BVar (ctx_len - 1 - abs_index))

let rec drop count values =
  if count <= 0 then values
  else
    match values with
    | [] -> []
    | _ :: rest -> drop (count - 1) rest

let direct_recursive_index_args family domain ctx_len =
  let head, args = collect_apps domain in
  match head with
  | Ext_term.Const (global_ref, levels)
    when family_ref family global_ref
         && levels_equal levels
              (List.map
                 (fun name -> Ext_level.Param name)
                 family.family_universe_params)
         && List.length args
            = family.family_param_count + family.family_index_count ->
      let rec check_params param_index remaining =
        if param_index = family.family_param_count then true
        else
          match (bvar_for_abs ctx_len param_index, remaining) with
          | Some expected, arg :: rest when arg = expected ->
              check_params (param_index + 1) rest
          | _ -> false
      in
      if
        check_params 0 args
        && List.for_all
             (fun arg -> not (contains_recursive_const family arg))
             args
      then Some (drop family.family_param_count args)
      else None
  | _ -> None

let direct_recursive_domain family domain ctx_len =
  direct_recursive_index_args family domain ctx_len <> None

let direct_mutual_recursive_index_args families domain ctx_len =
  let head, args = collect_apps domain in
  match head with
  | Ext_term.Const (global_ref, levels) -> (
      match find_family_index global_ref families with
      | None -> None
      | Some family_index -> (
          match List.nth_opt families family_index with
          | None -> None
          | Some family ->
              if
                levels_equal levels
                  (List.map
                     (fun name -> Ext_level.Param name)
                     family.family_universe_params)
                && List.length args
                   = family.family_param_count + family.family_index_count
              then
                let rec check_params param_index remaining =
                  if param_index = family.family_param_count then true
                  else
                    match (bvar_for_abs ctx_len param_index, remaining) with
                    | Some expected, arg :: rest when arg = expected ->
                        check_params (param_index + 1) rest
                    | _ -> false
                in
                if
                  check_params 0 args
                  && List.for_all
                       (fun arg -> not (contains_any_recursive_const families arg))
                       args
                then
                  Some
                    ( family_index,
                      drop family.family_param_count args )
                else None
              else None))
  | _ -> None

let rec recursive_occurrences_strictly_positive env family domain ctx_len =
  if direct_recursive_domain family domain ctx_len then true
  else
    match domain with
    | Ext_term.Sort _ | Ext_term.BVar _ -> true
    | Ext_term.Const (global_ref, _) -> not (family_ref family global_ref)
    | Ext_term.App _ ->
        let head, args = collect_apps domain in
        (match head with
        | Ext_term.Const (global_ref, _)
          when approved_nested_functor env global_ref (List.length args) ->
            List.for_all
              (fun arg ->
                recursive_occurrences_strictly_positive env family arg ctx_len)
              args
        | _ -> not (contains_recursive_const family domain))
    | Ext_term.Pi (ty, body) ->
        (not (contains_recursive_const family ty))
        && recursive_occurrences_strictly_positive env family body (ctx_len + 1)
    | Ext_term.Lam _ | Ext_term.Let _ ->
        not (contains_recursive_const family domain)

let check_domain_positive env family domain_index domain =
  if
    contains_recursive_const family domain
    && (domain_index < family.family_param_count
       || not
            (recursive_occurrences_strictly_positive env family domain
               domain_index))
  then Error Non_positive_occurrence
  else Ok ()

let check_constructor_domains env family domains =
  let rec loop domain_index remaining =
    match remaining with
    | [] -> Ok ()
    | domain :: rest -> (
        match check_domain_positive env family domain_index domain with
        | Error err -> Error err
        | Ok () -> loop (domain_index + 1) rest)
  in
  loop 0 domains

let rec mutual_occurrences_strictly_positive env families domain ctx_len =
  if direct_mutual_recursive_index_args families domain ctx_len <> None then true
  else
    match domain with
    | Ext_term.Sort _ | Ext_term.BVar _ -> true
    | Ext_term.Const (global_ref, _) ->
        find_family_index global_ref families = None
    | Ext_term.App _ ->
        let head, args = collect_apps domain in
        (match head with
        | Ext_term.Const (global_ref, _)
          when approved_nested_functor env global_ref (List.length args) ->
            List.for_all
              (fun arg ->
                mutual_occurrences_strictly_positive env families arg ctx_len)
              args
        | _ -> not (contains_any_recursive_const families domain))
    | Ext_term.Pi (ty, body) ->
        (not (contains_any_recursive_const families ty))
        && mutual_occurrences_strictly_positive env families body (ctx_len + 1)
    | Ext_term.Lam _ | Ext_term.Let _ ->
        not (contains_any_recursive_const families domain)

let check_mutual_constructor_domains env owner families domains =
  let rec loop domain_index remaining =
    match remaining with
    | [] -> Ok ()
    | domain :: rest ->
        if
          contains_any_recursive_const families domain
          &&
          (domain_index < owner.family_param_count
          || not
               (mutual_occurrences_strictly_positive env families domain
                  domain_index))
        then Error Non_positive_occurrence
        else loop (domain_index + 1) rest
  in
  loop 0 domains
