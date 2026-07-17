type public_export = {
  public_export_name : Ext_name.t;
  public_export_kind : Ext_cert.export_kind;
  public_decl_interface_hash : Ext_hash.digest;
  public_axiom_dependencies : Ext_cert.axiom_ref list;
  public_universe_params : Ext_name.t list;
  public_universe_constraints : Ext_cert.universe_constraint list;
  public_ty : Ext_term.t;
  public_body : Ext_term.t option;
}

type public_recursor_layout = {
  public_recursor_name : Ext_name.t;
  public_recursor_rules : Ext_cert.recursor_rules;
}

type public_inductive_layout = {
  public_inductive_name : Ext_name.t;
  public_param_count : int;
  public_index_count : int;
  public_constructor_names : Ext_name.t list;
  public_recursor_layout : public_recursor_layout option;
}

type public_inductive_group = {
  public_group_decl_interface_hash : Ext_hash.digest;
  public_group_families : public_inductive_layout list;
}

type public_environment = {
  public_imports : Ext_import.entry list;
  public_exports : public_export list;
  public_module_axioms : Ext_cert.axiom_ref list;
  public_core_features : Ext_feature.feature_report_entry list;
  public_inductive_groups : public_inductive_group list;
}

(* Public interfaces use a fixed sentinel for references to the imported module itself. *)
let public_self_import_index = 1_073_741_823

type module_entry = {
  import_entry : Ext_import.entry;
  axiom_report_hash : Ext_hash.digest;
  public_environment : public_environment;
  checked_by_ext_checker : bool;
}

type store = module_entry list

type trust_mode =
  | Normal
  | High_trust

type checker_policy = { trust_mode : trust_mode }

let normal_policy = { trust_mode = Normal }

let high_trust_policy = { trust_mode = High_trust }

type resolved_import = {
  resolved_module_name : Ext_name.t;
  resolved_export_hash : Ext_hash.digest;
  resolved_certificate_hash : Ext_hash.digest option;
  resolved_public_environment : public_environment;
}

type import_environment = { resolved_imports : resolved_import list }

type hash_mismatch = {
  hash_mismatch_kind : string;
  hash_mismatch_section : string;
  hash_mismatch_offset : int;
}

type load_error =
  | Import_dir_unavailable
  | Source_or_replay_input_rejected
  | Certificate_decode_error of Ext_bytes.decode_error
  | Certificate_hash_mismatch of hash_mismatch
  | Duplicate_import_binding of {
      duplicate_module_name : Ext_name.t;
      duplicate_export_hash : Ext_hash.digest;
      duplicate_offset : int;
    }

type resolve_error_reason =
  | Missing_import
  | Import_export_hash_mismatch
  | Import_certificate_hash_mismatch
  | Missing_import_certificate_hash
  | Unchecked_import
  | Duplicate_import

type resolve_error = {
  resolve_reason : resolve_error_reason;
  resolve_offset : int;
}

let empty = []

let entries store = store

let import_environment_empty = { resolved_imports = [] }

let import_environment_imports environment = environment.resolved_imports

let import_environment_public_exports environment =
  List.concat
    (List.map
       (fun import -> import.resolved_public_environment.public_exports)
       environment.resolved_imports)

let import_environment_module_axioms environment =
  List.concat
    (List.map
       (fun import -> import.resolved_public_environment.public_module_axioms)
       environment.resolved_imports)

let bind result f =
  match result with
  | Error err -> Error err
  | Ok value -> f value

let rec map_result f values =
  match values with
  | [] -> Ok []
  | value :: rest ->
      bind (f value) (fun mapped ->
          bind (map_result f rest) (fun mapped_rest -> Ok (mapped :: mapped_rest)))

let map_option_result f value =
  match value with
  | None -> Ok None
  | Some value -> bind (f value) (fun mapped -> Ok (Some mapped))

let has_suffix text suffix =
  let text_len = String.length text in
  let suffix_len = String.length suffix in
  text_len >= suffix_len
  && String.sub text (text_len - suffix_len) suffix_len = suffix

let is_source_or_replay_path path =
  let path_len = String.length path in
  let is_separator char = char = '/' || (Sys.win32 && char = '\\') in
  let matches_component start finish =
    let length = finish - start in
    if length <= 0 then false
    else
      let component = String.sub path start length in
      has_suffix component ".npa" || component = "replay.json"
  in
  let rec loop start index =
    if index = path_len then matches_component start index
    else if is_separator path.[index] then
      matches_component start index || loop (index + 1) (index + 1)
    else loop start (index + 1)
  in
  loop 0 0

let is_npcert_path path = has_suffix path ".npcert"

let sorted_unique paths =
  let rec loop remaining previous unique =
    match remaining with
    | [] -> List.rev unique
    | path :: rest ->
        if previous = Some path then loop rest previous unique
        else loop rest (Some path) (path :: unique)
  in
  loop (List.sort String.compare paths) None []

let max_import_candidates = 4_096
let max_import_directory_depth = 128
let max_import_directory_entries = 16_384

let close_descriptor descriptor =
  try Unix.close descriptor with Unix.Unix_error _ -> ()

let certificate_resource_limit offset =
  Error
    (Certificate_decode_error
       {
         Ext_bytes.section = Ext_bytes.Full_certificate;
         offset = max 0 offset;
         reason = Ext_bytes.Resource_limit;
       })

let read_binary_descriptor_with_limit descriptor max_bytes =
  let effective_limit = min max_bytes Ext_bytes.max_certificate_bytes in
  let finish result =
    close_descriptor descriptor;
    result
  in
  if effective_limit < 0 then finish (certificate_resource_limit effective_limit)
  else
    try
      let stat = Unix.fstat descriptor in
      if stat.Unix.st_kind <> Unix.S_REG then
        finish (Error Import_dir_unavailable)
      else if stat.Unix.st_size > effective_limit then
        finish (certificate_resource_limit effective_limit)
      else
        let chunk = Bytes.create (min 65_536 (effective_limit + 1)) in
        let contents = Buffer.create (min stat.Unix.st_size effective_limit) in
        let rec read total =
          if total > effective_limit then
            finish (certificate_resource_limit effective_limit)
          else
            let remaining = effective_limit + 1 - total in
            let count =
              Unix.read descriptor chunk 0 (min (Bytes.length chunk) remaining)
            in
            if count = 0 then finish (Ok (Buffer.contents contents))
            else (
              Buffer.add_subbytes contents chunk 0 count;
              read (total + count))
        in
        read 0
    with Unix.Unix_error _ -> finish (Error Import_dir_unavailable)

type collected_certificate = {
  collected_path : string;
  collected_bytes : string option;
}

let collect_certificates ?max_candidate_bytes import_dir =
  if is_source_or_replay_path import_dir then Error Source_or_replay_input_rejected
  else
    let resource_limit section =
      Error
        (Certificate_decode_error
           { Ext_bytes.section; offset = 0; reason = Ext_bytes.Resource_limit })
    in
    let visited_entries = ref 0 in
    let candidate_count = ref 0 in
    let total_bytes = ref 0 in
    let collected = ref [] in
    let read_directory_entries descriptor =
      let remaining = max_import_directory_entries - !visited_entries in
      try
        let entries = Ext_unix.read_dir_names_bounded descriptor remaining in
        visited_entries := !visited_entries + List.length entries;
        Ok (List.sort String.compare entries)
      with
      | Unix.Unix_error (Unix.EOVERFLOW, _, _) ->
          resource_limit Ext_bytes.Imports
      | Unix.Unix_error _ -> Error Import_dir_unavailable
    in
    let rec collect_dir depth dir descriptor =
      let finish result =
        close_descriptor descriptor;
        result
      in
      if depth > max_import_directory_depth then
        finish (resource_limit Ext_bytes.Import_store)
      else
        match read_directory_entries descriptor with
        | Error error -> finish (Error error)
        | Ok entries ->
          let rec loop remaining =
            match remaining with
            | [] -> finish (Ok ())
            | name :: rest ->
                let path = Filename.concat dir name in
                if is_source_or_replay_path path then loop rest
                else
                  match
                    try Ok (Ext_unix.path_kind_at_nofollow descriptor name) with
                    | Unix.Unix_error _ -> Error `Unavailable
                  with
                  | Error `Unavailable -> finish (Error Import_dir_unavailable)
                  | Ok Ext_unix.Symlink | Ok Ext_unix.Other -> loop rest
                  | Ok Ext_unix.Directory -> (
                      match
                        try Ok (Ext_unix.openat_nofollow descriptor name true) with
                        | Unix.Unix_error (Unix.ELOOP, _, _) -> Error `Symlink
                        | Unix.Unix_error _ -> Error `Unavailable
                      with
                      | Error `Symlink -> loop rest
                      | Error `Unavailable -> finish (Error Import_dir_unavailable)
                      | Ok child -> (
                          match collect_dir (depth + 1) path child with
                          | Error error -> finish (Error error)
                          | Ok () -> loop rest))
                  | Ok Ext_unix.Regular ->
                      if not (is_npcert_path path) then loop rest
                      else
                        (match
                           try Ok (Ext_unix.openat_nofollow descriptor name false) with
                           | Unix.Unix_error (Unix.ELOOP, _, _) -> Error `Symlink
                           | Unix.Unix_error _ -> Error `Unavailable
                         with
                        | Error `Symlink -> loop rest
                        | Error `Unavailable -> finish (Error Import_dir_unavailable)
                        | Ok child ->
                          if !candidate_count >= max_import_candidates then (
                            close_descriptor child;
                            finish (resource_limit Ext_bytes.Imports))
                          else (
                            candidate_count := !candidate_count + 1;
                            match max_candidate_bytes with
                            | None ->
                                close_descriptor child;
                                collected :=
                                  { collected_path = path; collected_bytes = None }
                                  :: !collected;
                                loop rest
                            | Some max_bytes -> (
                                let remaining_bytes = max_bytes - !total_bytes in
                                match
                                  read_binary_descriptor_with_limit child remaining_bytes
                                with
                                | Error error -> finish (Error error)
                                | Ok bytes ->
                                    total_bytes := !total_bytes + String.length bytes;
                                    collected :=
                                      {
                                        collected_path = path;
                                        collected_bytes = Some bytes;
                                    }
                                    :: !collected;
                                    loop rest)))
          in
          loop entries
    in
    match
      try Ok (Ext_unix.open_path_nofollow import_dir true) with
      | Unix.Unix_error (Unix.ELOOP, _, _) -> Error `Symlink
      | Unix.Unix_error _ -> Error `Unavailable
    with
    | Error `Symlink -> Error Source_or_replay_input_rejected
    | Error `Unavailable -> Error Import_dir_unavailable
    | Ok root -> (
        match collect_dir 1 import_dir root with
        | Error error -> Error error
        | Ok _ -> Ok (List.rev !collected))

let collect_cert_paths import_dir =
  bind (collect_certificates import_dir) (fun certificates ->
      Ok
        (sorted_unique
           (List.map
              (fun certificate -> certificate.collected_path)
              certificates)))

let collect_certificate_bytes_with_limit import_dir max_candidate_bytes =
  bind
    (collect_certificates ~max_candidate_bytes import_dir)
    (fun certificates ->
      let rec bytes remaining collected =
        match remaining with
        | [] -> Ok (List.rev collected)
        | { collected_bytes = Some value; _ } :: rest ->
            bytes rest (value :: collected)
        | { collected_bytes = None; _ } :: _ -> Error Import_dir_unavailable
      in
      bytes certificates [])

let read_binary_file_with_limit path max_bytes =
  try
    let descriptor = Ext_unix.open_path_nofollow path false in
    read_binary_descriptor_with_limit descriptor max_bytes
  with
  | Unix.Unix_error (Unix.ELOOP, _, _) -> Error Source_or_replay_input_rejected
  | Unix.Unix_error _ -> Error Import_dir_unavailable

let read_binary_file path =
  read_binary_file_with_limit path Ext_bytes.max_certificate_bytes

let import_hash_mismatch kind section offset =
  { hash_mismatch_kind = kind; hash_mismatch_section = section; hash_mismatch_offset = offset }

let declaration_hash_error mismatch =
  Certificate_hash_mismatch
    (import_hash_mismatch
       (Ext_canonical.declaration_hash_mismatch_kind_code
          mismatch.Ext_canonical.mismatch_kind)
       "declarations" mismatch.Ext_canonical.mismatch_offset)

let module_hash_error mismatch =
  Certificate_hash_mismatch
    (import_hash_mismatch
       (Ext_canonical.module_hash_role_kind_code
          mismatch.Ext_canonical.module_mismatch_role)
       "hashes" mismatch.Ext_canonical.module_mismatch_offset)

let declaration_at section offset (declarations : Ext_cert.declaration list) decl_index =
  if decl_index < 0 || decl_index >= List.length declarations then
    Ext_bytes.error section offset Ext_bytes.Dangling_reference
  else Ok (List.nth declarations decl_index)

let imported_self_ref name decl_interface_hash =
  Ext_term.Imported
    { import_index = public_self_import_index; name; decl_interface_hash }

let public_global_ref section offset declarations global_ref =
  match global_ref with
  | Ext_term.Builtin _ | Ext_term.Imported _ -> Ok global_ref
  | Ext_term.Local { decl_index } ->
      bind (declaration_at section offset declarations decl_index) (fun declaration ->
          Ok
            (imported_self_ref declaration.Ext_cert.name
               declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash))
  | Ext_term.LocalGenerated { decl_index; name } ->
      bind (declaration_at section offset declarations decl_index) (fun declaration ->
          Ok
            (imported_self_ref name
               declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash))

let rec public_term section offset declarations term =
  match term with
  | Ext_term.Sort _ | Ext_term.BVar _ -> Ok term
  | Ext_term.Const (global_ref, levels) ->
      bind (public_global_ref section offset declarations global_ref) (fun public_ref ->
          Ok (Ext_term.Const (public_ref, levels)))
  | Ext_term.App (fn, arg) ->
      bind (public_term section offset declarations fn) (fun public_fn ->
          bind (public_term section offset declarations arg) (fun public_arg ->
              Ok (Ext_term.App (public_fn, public_arg))))
  | Ext_term.Lam (ty, body) ->
      bind (public_term section offset declarations ty) (fun public_ty ->
          bind (public_term section offset declarations body) (fun public_body ->
              Ok (Ext_term.Lam (public_ty, public_body))))
  | Ext_term.Pi (ty, body) ->
      bind (public_term section offset declarations ty) (fun public_ty ->
          bind (public_term section offset declarations body) (fun public_body ->
              Ok (Ext_term.Pi (public_ty, public_body))))
  | Ext_term.Let (ty, value, body) ->
      bind (public_term section offset declarations ty) (fun public_ty ->
          bind (public_term section offset declarations value) (fun public_value ->
              bind (public_term section offset declarations body) (fun public_body ->
                  Ok (Ext_term.Let (public_ty, public_value, public_body)))))

let public_axiom_ref section offset declarations axiom =
  match axiom.Ext_cert.axiom_global_ref with
  | Ext_term.Local _ | Ext_term.LocalGenerated _ ->
      bind
        (public_global_ref section offset declarations axiom.Ext_cert.axiom_global_ref)
        (fun _ ->
          Ok
            {
              axiom with
              Ext_cert.axiom_global_ref =
                imported_self_ref axiom.Ext_cert.axiom_name
                  axiom.Ext_cert.axiom_decl_interface_hash;
            })
  | _ ->
      bind
        (public_global_ref section offset declarations axiom.Ext_cert.axiom_global_ref)
        (fun public_ref ->
          Ok { axiom with Ext_cert.axiom_global_ref = public_ref })

let declaration_constraints payload =
  match payload with
  | Ext_cert.AxiomDecl { decl_universe_constraints; _ }
  | Ext_cert.DefDecl { decl_universe_constraints; _ }
  | Ext_cert.TheoremDecl { decl_universe_constraints; _ }
  | Ext_cert.InductiveDecl { decl_universe_constraints; _ }
  | Ext_cert.MutualInductiveBlockDecl { decl_universe_constraints; _ } ->
      decl_universe_constraints

let rec export_owner_constraints (declarations : Ext_cert.declaration list)
    (export : Ext_cert.export_entry) =
  match declarations with
  | [] -> []
  | declaration :: rest ->
      if
        declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash
        = export.Ext_cert.export_decl_interface_hash
      then declaration_constraints declaration.Ext_cert.payload
      else export_owner_constraints rest export

let public_export_of_export version declarations export =
  let owner_constraints = export_owner_constraints declarations export in
  if version = Ext_cert.Legacy && owner_constraints <> [] then
    Ext_bytes.error Ext_bytes.Export_block export.Ext_cert.export_offset
      Ext_bytes.Constrained_export_requires_format_upgrade
  else
    bind
      (public_term Ext_bytes.Export_block export.Ext_cert.export_offset declarations
         export.Ext_cert.export_ty)
    (fun public_ty ->
      bind
        (map_option_result
           (public_term Ext_bytes.Export_block export.Ext_cert.export_offset declarations)
           export.Ext_cert.export_body)
        (fun public_body ->
          bind
            (map_result
               (public_axiom_ref Ext_bytes.Export_block export.Ext_cert.export_offset
                  declarations)
               export.Ext_cert.export_axiom_dependencies)
            (fun public_axiom_dependencies ->
              Ok
                {
                  public_export_name = export.Ext_cert.export_name;
                  public_export_kind = export.Ext_cert.export_kind;
                  public_decl_interface_hash = export.Ext_cert.export_decl_interface_hash;
                  public_axiom_dependencies;
                  public_universe_params = export.Ext_cert.export_universe_params;
                  public_universe_constraints =
                    export.Ext_cert.export_universe_constraints;
                  public_ty;
                  public_body;
                })))

let public_environment_of_decoded decoded =
  let recursor_layout = function
    | None -> None
    | Some recursor ->
        Some
          {
            public_recursor_name = recursor.Ext_cert.recursor_name;
            public_recursor_rules = recursor.Ext_cert.recursor_rules;
          }
  in
  let family_layout name params indices constructors recursor =
    {
      public_inductive_name = name;
      public_param_count = List.length params;
      public_index_count = List.length indices;
      public_constructor_names =
        List.map
          (fun constructor -> constructor.Ext_cert.constructor_name)
          constructors;
      public_recursor_layout = recursor_layout recursor;
    }
  in
  let rec collect_groups declarations groups =
    match declarations with
    | [] -> List.rev groups
    | declaration :: rest ->
        let families =
          match declaration.Ext_cert.payload with
          | Ext_cert.InductiveDecl
              {
                decl_name;
                ind_params;
                ind_indices;
                ind_constructors;
                ind_recursor;
                _;
              } ->
              [
                family_layout decl_name ind_params ind_indices ind_constructors
                  ind_recursor;
              ]
          | Ext_cert.MutualInductiveBlockDecl { mutual_inductives; _ } ->
              List.map
                (fun mutual ->
                  family_layout mutual.Ext_cert.mutual_name
                    mutual.Ext_cert.mutual_params mutual.Ext_cert.mutual_indices
                    mutual.Ext_cert.mutual_constructors
                    mutual.Ext_cert.mutual_recursor)
                mutual_inductives
          | Ext_cert.AxiomDecl _ | Ext_cert.DefDecl _ | Ext_cert.TheoremDecl _ ->
              []
        in
        let groups =
          if families = [] then groups
          else
            {
              public_group_decl_interface_hash =
                declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash;
              public_group_families = families;
            }
            :: groups
        in
        collect_groups rest groups
  in
  bind
    (map_result
       (public_export_of_export decoded.Ext_cert.header.Ext_cert.version
          decoded.Ext_cert.declaration_table)
       decoded.Ext_cert.export_block)
    (fun public_exports ->
      bind
        (map_result
           (public_axiom_ref Ext_bytes.Axiom_report
              decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
              decoded.Ext_cert.declaration_table)
           decoded.Ext_cert.axiom_report.Ext_cert.module_axioms)
        (fun public_module_axioms ->
          Ok
            {
              public_imports =
                List.map
                  (fun import -> import.Ext_cert.import_entry)
                  decoded.Ext_cert.imports;
              public_exports;
              public_module_axioms;
              public_core_features = decoded.Ext_cert.axiom_report.Ext_cert.core_features;
              public_inductive_groups =
                collect_groups decoded.Ext_cert.declaration_table [];
            }))

let module_entry_of_decoded decoded =
  bind (public_environment_of_decoded decoded) (fun public_environment ->
      Ok
        {
          import_entry =
            {
              Ext_import.module_name = decoded.Ext_cert.header.Ext_cert.module_name;
              export_hash = decoded.Ext_cert.hashes.Ext_cert.export_hash;
              certificate_hash = Some decoded.Ext_cert.hashes.Ext_cert.certificate_hash;
            };
          axiom_report_hash = decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash;
          public_environment;
          checked_by_ext_checker = false;
        })

let module_entry_from_source_free_certificate bytes =
  if String.length bytes > Ext_bytes.max_certificate_bytes then
    Error
      (Certificate_decode_error
         {
           Ext_bytes.section = Ext_bytes.Full_certificate;
           offset = Ext_bytes.max_certificate_bytes;
           reason = Ext_bytes.Resource_limit;
         })
  else match Ext_cert.read_module (Ext_bytes.of_string bytes) with
  | Error err -> Error (Certificate_decode_error err)
  | Ok (decoded, _next) -> (
      match Ext_canonical.verify_canonical_bytes bytes decoded with
      | Error err -> Error (Certificate_decode_error err)
      | Ok () -> (
      match Ext_canonical.verify_declaration_hashes decoded with
      | Error err -> Error (Certificate_decode_error err)
      | Ok Ext_canonical.Declaration_hashes_ok -> (
          match Ext_canonical.verify_module_hashes bytes decoded with
          | Error err -> Error (Certificate_decode_error err)
          | Ok Ext_canonical.Module_hashes_ok -> (
              match module_entry_of_decoded decoded with
              | Error err -> Error (Certificate_decode_error err)
              | Ok entry -> Ok entry)
          | Ok (Ext_canonical.Module_hash_mismatch mismatch) ->
              Error (module_hash_error mismatch))
      | Ok (Ext_canonical.Declaration_hash_mismatch mismatch) ->
          Error (declaration_hash_error mismatch)))

let duplicate_binding first second offset =
  if
    Ext_name.equal first.import_entry.Ext_import.module_name
      second.import_entry.Ext_import.module_name
    && first.import_entry.Ext_import.export_hash = second.import_entry.Ext_import.export_hash
  then
    Some
      (Duplicate_import_binding
         {
           duplicate_module_name = second.import_entry.Ext_import.module_name;
           duplicate_export_hash = second.import_entry.Ext_import.export_hash;
           duplicate_offset = offset;
         })
  else None

let validate_unique entries =
  let rec outer index seen remaining =
    match remaining with
    | [] -> Ok entries
    | entry :: rest -> (
        let rec inner prior =
          match prior with
          | [] -> Ok ()
          | existing :: prior_rest -> (
              match duplicate_binding existing entry index with
              | Some err -> Error err
              | None -> inner prior_rest)
        in
        match inner seen with
        | Error err -> Error err
        | Ok () -> outer (index + 1) (entry :: seen) rest)
  in
  outer 0 [] entries

let from_source_free_certificates certificates =
  let rec loop remaining decoded =
    match remaining with
    | [] -> validate_unique (List.rev decoded)
    | bytes :: rest ->
        bind (module_entry_from_source_free_certificate bytes) (fun entry ->
            loop rest (entry :: decoded))
  in
  loop certificates []

let load_import_dir import_dir =
  bind
    (collect_certificate_bytes_with_limit import_dir Ext_bytes.max_certificate_bytes)
    from_source_free_certificates

let same_module entry requested =
  Ext_name.equal entry.import_entry.Ext_import.module_name requested.Ext_import.module_name

let same_export entry requested =
  entry.import_entry.Ext_import.export_hash = requested.Ext_import.export_hash

let resolve_error_kind error =
  match error.resolve_reason with
  | Missing_import
  | Missing_import_certificate_hash
  | Unchecked_import
  | Duplicate_import ->
      "import_not_found"
  | Import_export_hash_mismatch
  | Import_certificate_hash_mismatch ->
      "import_hash_mismatch"

let resolve_error_reason_code reason =
  match reason with
  | Missing_import -> "missing_import"
  | Import_export_hash_mismatch -> "import_export_hash_mismatch"
  | Import_certificate_hash_mismatch -> "import_certificate_hash_mismatch"
  | Missing_import_certificate_hash -> "missing_import_certificate_hash"
  | Unchecked_import -> "unchecked_import"
  | Duplicate_import -> "duplicate_import"

let resolve_normal ?(offset = 0) store requested =
  let same_module_entries = List.filter (fun entry -> same_module entry requested) store in
  match same_module_entries with
  | [] -> Error { resolve_reason = Missing_import; resolve_offset = offset }
  | _ -> (
      let same_export_entries =
        List.filter (fun entry -> same_export entry requested) same_module_entries
      in
      match same_export_entries with
      | [] -> Error { resolve_reason = Import_export_hash_mismatch; resolve_offset = offset }
      | [ entry ] -> (
          match requested.Ext_import.certificate_hash with
          | None -> Ok entry
          | Some certificate_hash -> (
              match entry.import_entry.Ext_import.certificate_hash with
              | Some actual when actual = certificate_hash -> Ok entry
              | _ ->
                  Error
                    {
                      resolve_reason = Import_certificate_hash_mismatch;
                      resolve_offset = offset;
                    }))
      | _ -> Error { resolve_reason = Duplicate_import; resolve_offset = offset })

let enforce_high_trust_import ~offset requested entry =
  match requested.Ext_import.certificate_hash with
  | None ->
      Error { resolve_reason = Missing_import_certificate_hash; resolve_offset = offset }
  | Some certificate_hash -> (
      match entry.import_entry.Ext_import.certificate_hash with
      | Some actual when actual = certificate_hash ->
          if entry.checked_by_ext_checker then Ok entry
          else Error { resolve_reason = Unchecked_import; resolve_offset = offset }
      | _ ->
          Error
            {
              resolve_reason = Import_certificate_hash_mismatch;
              resolve_offset = offset;
            })

let resolve ?(policy = normal_policy) ?(offset = 0) store requested =
  bind (resolve_normal ~offset store requested) (fun entry ->
      match policy.trust_mode with
      | Normal -> Ok entry
      | High_trust -> enforce_high_trust_import ~offset requested entry)

let resolved_import_of_module_entry entry =
  {
    resolved_module_name = entry.import_entry.Ext_import.module_name;
    resolved_export_hash = entry.import_entry.Ext_import.export_hash;
    resolved_certificate_hash = entry.import_entry.Ext_import.certificate_hash;
    resolved_public_environment = entry.public_environment;
  }

let build_import_environment ?(policy = normal_policy) store decoded =
  let rec loop remaining resolved =
    match remaining with
    | [] -> Ok { resolved_imports = List.rev resolved }
    | requested :: rest ->
        bind
          (resolve ~policy ~offset:requested.Ext_cert.import_offset store
             requested.Ext_cert.import_entry)
          (fun entry ->
            loop rest (resolved_import_of_module_entry entry :: resolved))
  in
  loop decoded.Ext_cert.imports []
