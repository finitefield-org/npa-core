type phase_error =
  | Decode_error of Ext_bytes.decode_error
  | Declaration_hash_mismatch of Ext_canonical.declaration_hash_mismatch
  | Module_hash_mismatch of Ext_canonical.module_hash_mismatch
  | Unsupported_feature of Ext_feature.feature_report_entry
  | Import_error of Ext_import_store.resolve_error
  | Type_error of Ext_typecheck.error
  | Axiom_report_error of Ext_axiom.error
  | Axiom_policy_error of Ext_axiom.policy_check_error

type semantically_checked = {
  certificate_bytes : string;
  decoded : Ext_cert.decoded_module;
  import_environment : Ext_import_store.import_environment;
  checked_environment : Ext_env.t;
  public_environment : Ext_import_store.public_environment;
}

type normal_trust = Normal_trust
type high_trust = High_trust
type 'trust checked = { semantic : semantically_checked }

let bind result f =
  match result with
  | Ok value -> f value
  | Error error -> Error error

let max_certificate_bytes = Ext_bytes.max_certificate_bytes

let resource_error section offset =
  Error
    (Decode_error
       { Ext_bytes.section; offset; reason = Ext_bytes.Resource_limit })

let decode bytes =
  if String.length bytes > max_certificate_bytes then
    resource_error Ext_bytes.Full_certificate max_certificate_bytes
  else
    match Ext_cert.read_module (Ext_bytes.of_string bytes) with
    | Error error -> Error (Decode_error error)
    | Ok (decoded, _) -> Ok decoded

let canonical bytes decoded =
  match Ext_canonical.verify_canonical_bytes bytes decoded with
  | Ok () -> Ok ()
  | Error error -> Error (Decode_error error)

let declaration_hashes decoded =
  match Ext_canonical.verify_declaration_hashes decoded with
  | Error error -> Error (Decode_error error)
  | Ok Ext_canonical.Declaration_hashes_ok -> Ok ()
  | Ok (Ext_canonical.Declaration_hash_mismatch mismatch) ->
      Error (Declaration_hash_mismatch mismatch)

let module_hashes bytes decoded =
  match Ext_canonical.verify_module_hashes bytes decoded with
  | Error error -> Error (Decode_error error)
  | Ok Ext_canonical.Module_hashes_ok -> Ok ()
  | Ok (Ext_canonical.Module_hash_mismatch mismatch) ->
      Error (Module_hash_mismatch mismatch)

let features decoded =
  match
    Ext_feature.check_first_release_report
      decoded.Ext_cert.axiom_report.Ext_cert.core_features
  with
  | Ext_feature.Feature_policy_ok -> Ok ()
  | Ext_feature.Unsupported_core_feature feature ->
      Error (Unsupported_feature feature)

let imports trust_mode store decoded =
  let policy = { Ext_import_store.trust_mode } in
  match Ext_import_store.build_import_environment ~policy store decoded with
  | Ok environment -> Ok environment
  | Error error -> Error (Import_error error)

let typecheck import_environment decoded =
  let initial = Ext_env.of_imports import_environment in
  match Ext_typecheck.check_certificate initial decoded with
  | Ok environment -> Ok environment
  | Error error -> Error (Type_error error)

let axiom_report import_environment decoded =
  match Ext_axiom.verify_axiom_report import_environment decoded with
  | Ok () -> Ok ()
  | Error error -> Error (Axiom_report_error error)

let public_environment decoded =
  match Ext_import_store.public_environment_of_decoded decoded with
  | Ok environment -> Ok environment
  | Error error -> Error (Decode_error error)

let check_semantics ?(trust_mode = Ext_import_store.Normal) store bytes =
  bind (decode bytes) (fun decoded ->
      bind (canonical bytes decoded) (fun () ->
          bind (declaration_hashes decoded) (fun () ->
              bind (module_hashes bytes decoded) (fun () ->
                  bind (features decoded) (fun () ->
                      bind (imports trust_mode store decoded)
                        (fun import_environment ->
                          bind (typecheck import_environment decoded)
                            (fun checked_environment ->
                              bind (axiom_report import_environment decoded)
                                (fun () ->
                                  bind (public_environment decoded)
                                    (fun public_environment ->
                                      Ok
                                        {
                                          certificate_bytes = bytes;
                                          decoded;
                                          import_environment;
                                          checked_environment;
                                          public_environment;
                                        })))))))))

let enforce_policy policy semantic =
  match
    Ext_axiom.enforce_axiom_policy semantic.import_environment semantic.decoded
      policy
  with
  | Ok () -> Ok { semantic }
  | Error error -> Error (Axiom_policy_error error)

let check_with_store trust_mode store policy bytes =
  bind (check_semantics ~trust_mode store bytes) (enforce_policy policy)

let check_normal store policy bytes =
  (check_with_store Ext_import_store.Normal store policy bytes :
    (normal_trust checked, phase_error) result)

let module_name checked =
  checked.semantic.decoded.Ext_cert.header.Ext_cert.module_name

let export_hash checked =
  checked.semantic.decoded.Ext_cert.hashes.Ext_cert.export_hash

let certificate_hash checked =
  checked.semantic.decoded.Ext_cert.hashes.Ext_cert.certificate_hash

let axiom_report_hash checked =
  checked.semantic.decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash

let declarations_checked checked =
  checked.semantic.checked_environment.Ext_env.checked_declaration_count

let imported_recursor_cache_size checked =
  Hashtbl.length
    checked.semantic.checked_environment.Ext_env.imported_recursor_cache

let imported_mutual_block_cache_size checked =
  Hashtbl.length
    checked.semantic.checked_environment.Ext_env.imported_mutual_block_cache

let imported_mutual_runtimes_share_families checked =
  let families_by_block = Hashtbl.create 8 in
  let shared = ref true in
  Hashtbl.iter
    (fun _ runtime ->
        match runtime with
        | Some (Ext_env.Imported_mutual mutual) ->
            let key =
              ( mutual.Ext_env.imported_mutual_import_index,
                mutual.Ext_env.imported_mutual_decl_interface_hash )
            in
            let families = mutual.Ext_env.imported_mutual_families in
            (match Hashtbl.find_opt families_by_block key with
            | None -> Hashtbl.add families_by_block key families
            | Some first -> if families != first then shared := false)
        | None | Some (Ext_env.Imported_single _) -> ())
    checked.semantic.checked_environment.Ext_env.imported_recursor_cache;
  !shared

let module_entry (checked : high_trust checked) =
  let decoded = checked.semantic.decoded in
  {
    Ext_import_store.import_entry =
      {
        Ext_import.module_name = decoded.Ext_cert.header.Ext_cert.module_name;
        export_hash = decoded.Ext_cert.hashes.Ext_cert.export_hash;
        certificate_hash = Some decoded.Ext_cert.hashes.Ext_cert.certificate_hash;
      };
    axiom_report_hash = decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash;
    public_environment = checked.semantic.public_environment;
    checked_by_ext_checker = true;
  }

let check_high_trust checked_imports policy bytes =
  let store = List.map module_entry checked_imports in
  let policy =
    {
      policy with
      Ext_axiom.deny_sorry = true;
      deny_custom_axioms = true;
    }
  in
  (check_with_store Ext_import_store.High_trust store policy bytes :
    (high_trust checked, phase_error) result)
