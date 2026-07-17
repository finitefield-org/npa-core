type error_reason =
  | Noncanonical_universe_params
  | Duplicate_universe_param
  | Unresolved_metavariable
  | Unknown_universe_param
  | Noncanonical_universe_constraints
  | Duplicate_universe_constraint
  | Unsupported_universe_constraint
  | Unsatisfiable_universe_constraints
  | Universe_constraint_violation
  | Resource_limit

type error = { reason : error_reason }

type atom_base =
  | Atom_zero
  | Atom_param of Ext_name.t

type atom = {
  atom_base : atom_base;
  atom_offset : int;
}

type context = {
  params : Ext_name.t list;
  constraints : Ext_cert.universe_constraint list;
  closure : int option array array;
}

let max_context_nodes = 65

let max_atom_inequalities = 1_024

let error reason = Error { reason }

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let rec contains_name name names =
  match names with
  | [] -> false
  | current :: rest -> Ext_name.equal current name || contains_name name rest

let compare_name lhs rhs =
  String.compare (Ext_name.to_string lhs) (Ext_name.to_string rhs)

let validate_params params =
  if List.length params + 1 > max_context_nodes then error Resource_limit
  else
    let rec loop previous seen remaining =
      match remaining with
      | [] -> Ok ()
      | name :: rest ->
          if Ext_level.component_contains_universe_meta name then
            error Unresolved_metavariable
          else if contains_name name seen then error Duplicate_universe_param
          else
            (match previous with
            | Some previous when compare_name previous name >= 0 ->
                error Noncanonical_universe_params
            | _ -> loop (Some name) (name :: seen) rest)
    in
    loop None [] params

let rec ensure_level_wf params level =
  match level with
  | Ext_level.Zero -> Ok ()
  | Ext_level.Succ inner -> ensure_level_wf params inner
  | Ext_level.Max (lhs, rhs) | Ext_level.Imax (lhs, rhs) ->
      bind (ensure_level_wf params lhs) (fun () -> ensure_level_wf params rhs)
  | Ext_level.Param name ->
      if Ext_level.component_contains_universe_meta name then
        error Unresolved_metavariable
      else if contains_name name params then Ok ()
      else error Unknown_universe_param

let ensure_canonical_level params level =
  bind (ensure_level_wf params level) (fun () ->
      if Ext_level.normalize level = level then Ok ()
      else error Noncanonical_universe_constraints)

let compare_relation lhs rhs =
  match (lhs, rhs) with
  | Ext_cert.Le, Ext_cert.Le | Ext_cert.Eq, Ext_cert.Eq -> 0
  | Ext_cert.Le, Ext_cert.Eq -> -1
  | Ext_cert.Eq, Ext_cert.Le -> 1

let compare_constraint lhs rhs =
  let compared =
    Ext_level.compare_level lhs.Ext_cert.constraint_lhs
      rhs.Ext_cert.constraint_lhs
  in
  if compared <> 0 then compared
  else
    let compared =
      compare_relation lhs.Ext_cert.constraint_relation
        rhs.Ext_cert.constraint_relation
    in
    if compared <> 0 then compared
    else
      Ext_level.compare_level lhs.Ext_cert.constraint_rhs
        rhs.Ext_cert.constraint_rhs

let validate_constraints params constraints =
  let rec validate_levels remaining =
    match remaining with
    | [] -> Ok ()
    | constraint_ :: rest ->
        bind
          (ensure_canonical_level params constraint_.Ext_cert.constraint_lhs)
          (fun () ->
            bind
              (ensure_canonical_level params constraint_.Ext_cert.constraint_rhs)
              (fun () -> validate_levels rest))
  in
  bind (validate_levels constraints) (fun () ->
      let rec validate_order previous remaining =
        match remaining with
        | [] -> Ok ()
        | constraint_ :: rest ->
            (match previous with
            | Some previous ->
                let compared = compare_constraint previous constraint_ in
                if compared = 0 then error Duplicate_universe_constraint
                else if compared > 0 then error Noncanonical_universe_constraints
                else validate_order (Some constraint_) rest
            | None -> validate_order (Some constraint_) rest)
      in
      validate_order None constraints)

let compare_atom_base lhs rhs =
  match (lhs, rhs) with
  | Atom_zero, Atom_zero -> 0
  | Atom_zero, Atom_param _ -> -1
  | Atom_param _, Atom_zero -> 1
  | Atom_param lhs, Atom_param rhs -> compare_name lhs rhs

let compare_atom lhs rhs =
  let compared = compare_atom_base lhs.atom_base rhs.atom_base in
  if compared <> 0 then compared else compare lhs.atom_offset rhs.atom_offset

let rec decompose_atom normalized =
  match normalized with
  | Ext_level.Zero -> Ok { atom_base = Atom_zero; atom_offset = 0 }
  | Ext_level.Param name ->
      Ok { atom_base = Atom_param name; atom_offset = 0 }
  | Ext_level.Succ inner ->
      bind (decompose_atom inner) (fun atom ->
          if atom.atom_offset = max_int then error Unsupported_universe_constraint
          else Ok { atom with atom_offset = atom.atom_offset + 1 })
  | Ext_level.Max _ | Ext_level.Imax _ -> error Unsupported_universe_constraint

let sort_unique_atoms atoms =
  let sorted = List.sort compare_atom atoms in
  let rec deduplicate previous remaining result =
    match remaining with
    | [] -> List.rev result
    | atom :: rest ->
        (match previous with
        | Some previous when compare_atom previous atom = 0 ->
            deduplicate (Some previous) rest result
        | _ -> deduplicate (Some atom) rest (atom :: result))
  in
  deduplicate None sorted []

let rec decompose_level level =
  match Ext_level.normalize level with
  | Ext_level.Max (lhs, rhs) ->
      bind (decompose_level lhs) (fun lhs_atoms ->
          bind (decompose_level rhs) (fun rhs_atoms ->
              Ok (sort_unique_atoms (lhs_atoms @ rhs_atoms))))
  | normalized -> bind (decompose_atom normalized) (fun atom -> Ok [ atom ])

let param_index params name =
  let rec loop index remaining =
    match remaining with
    | [] -> None
    | current :: rest ->
        if Ext_name.equal current name then Some (index + 1)
        else loop (index + 1) rest
  in
  loop 0 params

let atom_index params atom =
  match atom.atom_base with
  | Atom_zero -> Ok 0
  | Atom_param name -> (
      match param_index params name with
      | Some index -> Ok index
      | None -> error Unknown_universe_param)

let add_edge closure from_index to_index weight =
  match closure.(from_index).(to_index) with
  | Some old when old <= weight -> ()
  | _ -> closure.(from_index).(to_index) <- Some weight

let checked_add lhs rhs =
  if rhs > 0 && lhs > max_int - rhs then None
  else if rhs < 0 && (rhs = min_int || lhs < min_int - rhs) then None
  else Some (lhs + rhs)

let decompose_le_constraint lhs rhs =
  let lhs = Ext_level.normalize lhs in
  let rhs = Ext_level.normalize rhs in
  if lhs = rhs then Ok []
  else
    bind (decompose_level lhs) (fun lhs_atoms ->
        bind (decompose_level rhs) (function
          | [ rhs_atom ] -> Ok (List.map (fun lhs_atom -> (lhs_atom, rhs_atom)) lhs_atoms)
          | _ -> error Unsupported_universe_constraint))

let decompose_constraint constraint_ =
  let lhs = constraint_.Ext_cert.constraint_lhs in
  let rhs = constraint_.Ext_cert.constraint_rhs in
  match constraint_.Ext_cert.constraint_relation with
  | Ext_cert.Le -> decompose_le_constraint lhs rhs
  | Ext_cert.Eq ->
      if Ext_level.normalize lhs = Ext_level.normalize rhs then Ok []
      else
        bind (decompose_le_constraint lhs rhs) (fun forward ->
            bind (decompose_le_constraint rhs lhs) (fun backward ->
                Ok (forward @ backward)))

let close closure =
  let length = Array.length closure in
  let overflow = ref false in
  for k = 0 to length - 1 do
    for i = 0 to length - 1 do
      match closure.(i).(k) with
      | None -> ()
      | Some ik ->
          for j = 0 to length - 1 do
            match closure.(k).(j) with
            | None -> ()
            | Some kj -> (
                match checked_add ik kj with
                | None -> overflow := true
                | Some candidate -> add_edge closure i j candidate)
          done
    done
  done;
  let rec check index =
    if !overflow then error Resource_limit
    else if index = length then Ok ()
    else
      match closure.(index).(index) with
      | Some bound when bound < 0 -> error Unsatisfiable_universe_constraints
      | _ -> check (index + 1)
  in
  check 0

let create params constraints =
  bind (validate_params params) (fun () ->
      bind (validate_constraints params constraints) (fun () ->
          let node_count = List.length params + 1 in
          let closure = Array.make_matrix node_count node_count None in
          for index = 0 to node_count - 1 do
            closure.(index).(index) <- Some 0
          done;
          for index = 1 to node_count - 1 do
            closure.(index).(0) <- Some 0
          done;
          let edge_count = ref (List.length params) in
          let rec add_constraints remaining =
            match remaining with
            | [] -> Ok ()
            | constraint_ :: rest ->
                bind (decompose_constraint constraint_) (fun inequalities ->
                    if
                      List.length inequalities
                      > max_atom_inequalities - !edge_count
                    then error Resource_limit
                    else (
                      edge_count := !edge_count + List.length inequalities;
                      let rec add_inequalities remaining =
                        match remaining with
                        | [] -> Ok ()
                        | (lhs, rhs) :: rest ->
                            bind (atom_index params rhs) (fun from_index ->
                                bind (atom_index params lhs) (fun to_index ->
                                    add_edge closure from_index to_index
                                      (rhs.atom_offset - lhs.atom_offset);
                                    add_inequalities rest))
                      in
                      bind (add_inequalities inequalities) (fun () ->
                          add_constraints rest)))
          in
          bind (add_constraints constraints) (fun () ->
              bind (close closure) (fun () ->
                  Ok { params; constraints; closure }))))

let empty =
  { params = []; constraints = []; closure = [| [| Some 0 |] |] }

let entails_level_le context lhs rhs =
  bind (ensure_level_wf context.params lhs) (fun () ->
      bind (ensure_level_wf context.params rhs) (fun () ->
          let lhs = Ext_level.normalize lhs in
          let rhs = Ext_level.normalize rhs in
          if lhs = rhs then Ok true
          else
            bind (decompose_level lhs) (fun lhs_atoms ->
                bind (decompose_level rhs) (fun rhs_atoms ->
                    let lhs_count = List.length lhs_atoms in
                    let rhs_count = List.length rhs_atoms in
                    if
                      rhs_count <> 0
                      && lhs_count > max_atom_inequalities / rhs_count
                    then error Resource_limit
                    else
                      let rec all_lhs remaining =
                        match remaining with
                        | [] -> Ok true
                        | lhs_atom :: rest ->
                            bind (atom_index context.params lhs_atom) (fun to_index ->
                                let rec any_rhs remaining =
                                  match remaining with
                                  | [] -> Ok false
                                  | rhs_atom :: rest ->
                                      bind (atom_index context.params rhs_atom)
                                        (fun from_index ->
                                          let required_bound =
                                            rhs_atom.atom_offset - lhs_atom.atom_offset
                                          in
                                          match context.closure.(from_index).(to_index) with
                                          | Some actual when actual <= required_bound ->
                                              Ok true
                                          | _ -> any_rhs rest)
                                in
                                bind (any_rhs rhs_atoms) (fun witnessed ->
                                    if witnessed then all_lhs rest else Ok false))
                      in
                      all_lhs lhs_atoms))))

let rec substitute_level params levels level =
  match level with
  | Ext_level.Zero -> Ext_level.Zero
  | Ext_level.Succ inner ->
      Ext_level.normalize (Ext_level.Succ (substitute_level params levels inner))
  | Ext_level.Max (lhs, rhs) ->
      Ext_level.normalize
        (Ext_level.Max
           (substitute_level params levels lhs, substitute_level params levels rhs))
  | Ext_level.Imax (lhs, rhs) ->
      Ext_level.normalize
        (Ext_level.Imax
           (substitute_level params levels lhs, substitute_level params levels rhs))
  | Ext_level.Param name ->
      let rec find remaining_params remaining_levels =
        match (remaining_params, remaining_levels) with
        | param :: params, level :: levels ->
            if Ext_name.equal param name then level else find params levels
        | _ -> Ext_level.Param name
      in
      find params levels

let substitute_constraints params levels constraints =
  if List.length params <> List.length levels then error Unsupported_universe_constraint
  else
    Ok
      (List.map
         (fun constraint_ ->
           {
             Ext_cert.constraint_lhs =
               substitute_level params levels constraint_.Ext_cert.constraint_lhs;
             constraint_relation = constraint_.Ext_cert.constraint_relation;
             constraint_rhs =
               substitute_level params levels constraint_.Ext_cert.constraint_rhs;
           })
         constraints)

let entails_constraints context constraints =
  let rec loop remaining =
    match remaining with
    | [] -> Ok ()
    | constraint_ :: rest ->
        let lhs = constraint_.Ext_cert.constraint_lhs in
        let rhs = constraint_.Ext_cert.constraint_rhs in
        let entailed =
          match constraint_.Ext_cert.constraint_relation with
          | Ext_cert.Le -> entails_level_le context lhs rhs
          | Ext_cert.Eq ->
              bind (entails_level_le context lhs rhs) (fun forward ->
                  if not forward then Ok false
                  else entails_level_le context rhs lhs)
        in
        bind entailed (fun entailed ->
            if entailed then loop rest else error Universe_constraint_violation)
  in
  loop constraints
