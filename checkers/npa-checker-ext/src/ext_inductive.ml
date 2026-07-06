type check_result =
  | Inductive_checked
  | Inductive_not_implemented

type positivity_error = Non_positive_occurrence

type family = {
  family_decl_index : int;
  family_universe_params : Ext_name.t list;
  family_param_count : int;
  family_index_count : int;
}

let check_block _env = Inductive_not_implemented

let family ~decl_index ~universe_params ~param_count ~index_count =
  {
    family_decl_index = decl_index;
    family_universe_params = universe_params;
    family_param_count = param_count;
    family_index_count = index_count;
  }

let levels_equal lhs rhs =
  List.length lhs = List.length rhs
  && List.for_all2
       (fun left right -> Ext_level.normalize left = Ext_level.normalize right)
       lhs rhs

let family_ref family global_ref =
  match global_ref with
  | Ext_term.Local { decl_index } -> decl_index = family.family_decl_index
  | _ -> false

let collect_apps term =
  let rec loop current args =
    match current with
    | Ext_term.App (fn, arg) -> loop fn (arg :: args)
    | _ -> (current, args)
  in
  loop term []

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

let direct_recursive_domain family domain ctx_len =
  let head, args = collect_apps domain in
  match head with
  | Ext_term.Const (global_ref, levels)
    when family_ref family global_ref
         && levels_equal levels
              (List.map (fun name -> Ext_level.Param name) family.family_universe_params)
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
      check_params 0 args
      && not (List.exists (contains_recursive_const family) args)
  | _ -> false

let rec recursive_occurrences_strictly_positive family domain ctx_len =
  if direct_recursive_domain family domain ctx_len then true
  else
    match domain with
    | Ext_term.Sort _ | Ext_term.BVar _ -> true
    | Ext_term.Const (global_ref, _) -> not (family_ref family global_ref)
    | Ext_term.App _ ->
        not (contains_recursive_const family domain)
    | Ext_term.Pi (ty, body) ->
        (not (contains_recursive_const family ty))
        && recursive_occurrences_strictly_positive family body (ctx_len + 1)
    | Ext_term.Lam _ | Ext_term.Let _ ->
        not (contains_recursive_const family domain)

let check_domain_positive family domain_index domain =
  if
    contains_recursive_const family domain
    && (domain_index < family.family_param_count
       || not
            (recursive_occurrences_strictly_positive family domain domain_index))
  then Error Non_positive_occurrence
  else Ok ()

let check_constructor_domains family domains =
  let rec loop domain_index remaining =
    match remaining with
    | [] -> Ok ()
    | domain :: rest -> (
        match check_domain_positive family domain_index domain with
        | Error err -> Error err
        | Ok () -> loop (domain_index + 1) rest)
  in
  loop 0 domains
