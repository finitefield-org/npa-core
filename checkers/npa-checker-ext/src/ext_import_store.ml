type public_export = {
  public_export_name : Ext_name.t;
  public_export_kind : Ext_cert.export_kind;
  public_decl_interface_hash : Ext_hash.digest;
  public_axiom_dependencies : Ext_cert.axiom_ref list;
  public_universe_params : Ext_name.t list;
  public_ty : Ext_term.t;
  public_body : Ext_term.t option;
}

type public_environment = {
  public_imports : Ext_import.entry list;
  public_exports : public_export list;
  public_module_axioms : Ext_cert.axiom_ref list;
  public_core_features : Ext_feature.feature_report_entry list;
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

let is_source_or_replay_path path =
  has_suffix path ".npa" || contains_substring path ".npa/"
  || contains_substring path ".npa\\" || has_suffix path "replay.json"
  || contains_substring path "/replay.json" || contains_substring path "\\replay.json"

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

let is_directory path =
  try Sys.is_directory path with Sys_error _ -> false

let collect_cert_paths import_dir =
  if is_source_or_replay_path import_dir then Error Source_or_replay_input_rejected
  else if not (is_directory import_dir) then Error Import_dir_unavailable
  else
    let rec collect_dir dir paths =
      let entries =
        try Ok (Array.to_list (Sys.readdir dir))
        with Sys_error _ -> Error Import_dir_unavailable
      in
      bind entries (fun entries ->
          let rec loop remaining paths =
            match remaining with
            | [] -> Ok paths
            | name :: rest ->
                let path = Filename.concat dir name in
                if is_source_or_replay_path path then loop rest paths
                else if is_directory path then
                  bind (collect_dir path paths) (fun paths -> loop rest paths)
                else if is_npcert_path path then loop rest (path :: paths)
                else loop rest paths
          in
          loop entries paths)
    in
    bind (collect_dir import_dir []) (fun paths -> Ok (sorted_unique paths))

let read_binary_file path =
  try
    let channel = open_in_bin path in
    let length = in_channel_length channel in
    let contents = really_input_string channel length in
    close_in channel;
    Ok contents
  with Sys_error _ -> Error Import_dir_unavailable

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

let public_export_of_export declarations export =
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
                  public_ty;
                  public_body;
                })))

let public_environment_of_decoded decoded =
  bind
    (map_result
       (public_export_of_export decoded.Ext_cert.declaration_table)
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
  match Ext_cert.read_module (Ext_bytes.of_string bytes) with
  | Error err -> Error (Certificate_decode_error err)
  | Ok (decoded, _next) -> (
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
          Error (declaration_hash_error mismatch))

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

let from_checked_modules modules =
  let mark_checked_by_ext_checker entry = { entry with checked_by_ext_checker = true } in
  validate_unique (List.map mark_checked_by_ext_checker modules)

let load_import_dir import_dir =
  bind (collect_cert_paths import_dir) (fun paths ->
      let rec read_all remaining bytes =
        match remaining with
        | [] -> from_source_free_certificates (List.rev bytes)
        | path :: rest ->
            bind (read_binary_file path) (fun contents ->
                read_all rest (contents :: bytes))
      in
      read_all paths [])

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
