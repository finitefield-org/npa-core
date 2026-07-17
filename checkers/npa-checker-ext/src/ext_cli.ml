type cli_result = {
  stdout : string;
  stderr : string;
  code : int;
}

type options = {
  cert : string option;
  import_dir : string option;
  policy : string option;
  policy_hash : string option;
  output : string option;
}

type 'a parse_result =
  | Parsed of 'a
  | Parse_error of string

let empty_options =
  {
    cert = None;
    import_dir = None;
    policy = None;
    policy_hash = None;
    output = None;
  }

let ok stdout = { stdout; stderr = ""; code = 0 }

let rejected stdout = { stdout; stderr = ""; code = 1 }

let internal_failure stdout = { stdout; stderr = ""; code = 2 }

let cli_error message = { stdout = ""; stderr = "npa-checker-ext: " ^ message ^ "\n"; code = 2 }

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

let starts_with text prefix =
  let text_len = String.length text in
  let prefix_len = String.length prefix in
  text_len >= prefix_len && String.sub text 0 prefix_len = prefix

let is_lower_hex text start =
  let rec loop index =
    if index >= String.length text then true
    else
      match text.[index] with
      | '0' .. '9' | 'a' .. 'f' -> loop (index + 1)
      | _ -> false
  in
  loop start

let is_wire_hash value =
  String.length value = 71 && starts_with value "sha256:"
  && is_lower_hex value 7

let is_source_path value =
  has_suffix value ".npa" || contains_substring value ".npa/" || contains_substring value ".npa\\"

let reject_source_path flag value =
  if is_source_path value then Some (flag ^ " must not point to .npa source")
  else None

let require_certificate_path flag value =
  match reject_source_path flag value with
  | Some message -> Some message
  | None ->
      if flag = "--cert" && not (has_suffix value ".npcert") then
        Some "--cert must point to a .npcert certificate"
      else None

let set_once flag current value update =
  match current with
  | Some _ -> Parse_error ("duplicate " ^ flag)
  | None -> (
      if starts_with value "--" then Parse_error ("missing value for " ^ flag)
      else (
        match require_certificate_path flag value with
        | Some message -> Parse_error message
        | None -> Parsed (update value)))

let rec parse args options =
  match args with
  | [] -> Parsed options
  | "--cert" :: value :: rest -> (
      match set_once "--cert" options.cert value (fun cert -> { options with cert = Some cert }) with
      | Parse_error message -> Parse_error message
      | Parsed next_options -> parse rest next_options)
  | "--cert" :: [] -> Parse_error "missing value for --cert"
  | "--import-dir" :: value :: rest -> (
      match
        set_once "--import-dir" options.import_dir value (fun import_dir ->
            { options with import_dir = Some import_dir })
      with
      | Parse_error message -> Parse_error message
      | Parsed next_options -> parse rest next_options)
  | "--import-dir" :: [] -> Parse_error "missing value for --import-dir"
  | "--policy" :: value :: rest -> (
      match
        set_once "--policy" options.policy value (fun policy -> { options with policy = Some policy })
      with
      | Parse_error message -> Parse_error message
      | Parsed next_options -> parse rest next_options)
  | "--policy" :: [] -> Parse_error "missing value for --policy"
  | "--policy-hash" :: value :: rest -> (
      match options.policy_hash with
      | Some _ -> Parse_error "duplicate --policy-hash"
      | None ->
          if starts_with value "--" then
            Parse_error "missing value for --policy-hash"
          else if not (is_wire_hash value) then
            Parse_error "--policy-hash must be sha256:<lower-hex>"
          else
            parse rest { options with policy_hash = Some value })
  | "--policy-hash" :: [] -> Parse_error "missing value for --policy-hash"
  | "--output" :: value :: rest -> (
      match options.output with
      | Some _ -> Parse_error "duplicate --output"
      | None ->
          if starts_with value "--" then Parse_error "missing value for --output"
          else if value <> "json" then Parse_error "--output must be json"
          else parse rest { options with output = Some value })
  | "--output" :: [] -> Parse_error "missing value for --output"
  | flag :: _ when has_suffix flag ".npa" -> Parse_error "positional .npa source input is forbidden"
  | flag :: _ when String.length flag > 0 && flag.[0] = '-' -> Parse_error ("unknown flag " ^ flag)
  | _ :: _ -> Parse_error "positional input is forbidden"

let missing_required options =
  if options.cert = None then Some "missing required --cert"
  else if options.import_dir = None then Some "missing required --import-dir"
  else if options.policy = None then Some "missing required --policy"
  else if options.policy_hash = None then Some "missing required --policy-hash"
  else if options.output = None then Some "missing required --output"
  else None

type raw_context = {
  module_name : string option;
  certificate_hash : string option;
}

let empty_context = { module_name = None; certificate_hash = None }

let context_of_decoded decoded =
  {
    module_name =
      Some
        (Ext_name.to_string decoded.Ext_cert.header.Ext_cert.module_name);
    certificate_hash =
      Some
        (Ext_result.wire_hash
           decoded.Ext_cert.hashes.Ext_cert.certificate_hash);
  }

let context_of_hash_bound_trailer bytes =
  let reader = Ext_bytes.of_string bytes in
  match Ext_cert.read_header reader with
  | Error _ -> empty_context
  | Ok (header, after_header) ->
      let byte_length = String.length bytes in
      if
        byte_length - Ext_bytes.offset after_header
        < Ext_cert.module_hash_trailer_len
      then empty_context
      else
        let certificate_hash_length = 32 in
        let certificate_hash_offset =
          byte_length - certificate_hash_length
        in
        let certificate_hash =
          String.sub bytes certificate_hash_offset certificate_hash_length
        in
        let expected_hash =
          Ext_canonical.hash_with_domain
            (Ext_canonical.module_certificate_domain
               header.Ext_cert.version)
            (String.sub bytes 0 certificate_hash_offset)
        in
        if certificate_hash <> expected_hash then empty_context
        else
          {
            module_name =
              Some
                (Ext_name.to_string header.Ext_cert.module_name);
            certificate_hash =
              Some (Ext_result.wire_hash certificate_hash);
          }

let context_of_bytes bytes =
  if String.length bytes > Ext_bytes.max_certificate_bytes then empty_context
  else
    (* Raw identity is diagnostic context, not proof evidence. Decode the wire
       sections without canonical/resource validation so later validation
       failures retain their parsed header and trailer. If structural decoding
       itself fails, accept a trailer only when its certificate hash binds the
       exact preceding bytes under the version selected by the valid header. *)
    match Ext_cert.read_module_sections (Ext_bytes.of_string bytes) with
    | Ok (decoded, next) when Ext_bytes.remaining next = 0 ->
        context_of_decoded decoded
    | Ok _ -> empty_context
    | Error _ -> context_of_hash_bound_trailer bytes

let render_error context error =
  Ext_result.render_failed ?module_name:context.module_name
    ?certificate_hash:context.certificate_hash error

let phase_error context = function
  | Ext_checker.Decode_error error ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:(Ext_bytes.reason_code error.Ext_bytes.reason)
           ~section:(Ext_bytes.section_name error.Ext_bytes.section)
           ~offset:error.Ext_bytes.offset
           (Ext_result.decode_error_kind error))
  | Ext_checker.Declaration_hash_mismatch mismatch ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:
             (Ext_canonical.declaration_hash_role_reason_code
                mismatch.Ext_canonical.mismatch_role)
           ~section:"declarations" ~offset:mismatch.Ext_canonical.mismatch_offset
           ~expected_hash:(Ext_result.wire_hash mismatch.Ext_canonical.expected_hash)
           ~actual_hash:(Ext_result.wire_hash mismatch.Ext_canonical.actual_hash)
           (Ext_canonical.declaration_hash_mismatch_kind_code
              mismatch.Ext_canonical.mismatch_kind))
  | Ext_checker.Module_hash_mismatch mismatch ->
      let kind =
        Ext_canonical.module_hash_role_kind_code
          mismatch.Ext_canonical.module_mismatch_role
      in
      render_error context
        (Ext_result.checker_error ~reason_code:kind ~section:"hashes"
           ~offset:mismatch.Ext_canonical.module_mismatch_offset
           ~expected_hash:
             (Ext_result.wire_hash mismatch.Ext_canonical.module_expected_hash)
           ~actual_hash:
             (Ext_result.wire_hash mismatch.Ext_canonical.module_actual_hash)
           kind)
  | Ext_checker.Unsupported_feature feature ->
      render_error context
        (Ext_result.checker_error ~reason_code:"unsupported_core_feature"
           ~section:"core_features" ?offset:feature.Ext_feature.offset
           "unsupported_core_feature")
  | Ext_checker.Import_error error ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:
             (Ext_import_store.resolve_error_reason_code
                error.Ext_import_store.resolve_reason)
           ~section:"imports" ~offset:error.Ext_import_store.resolve_offset
           (Ext_import_store.resolve_error_kind error))
  | Ext_checker.Type_error error ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:(Ext_typecheck.error_reason_code error.Ext_typecheck.reason)
           ~section:(Ext_bytes.section_name error.Ext_typecheck.section)
           ~offset:error.Ext_typecheck.offset
           (Ext_typecheck.error_kind error))
  | Ext_checker.Axiom_report_error error ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:(Ext_axiom.error_reason_code error)
           ~section:(Ext_bytes.section_name error.Ext_axiom.section)
           ~offset:error.Ext_axiom.offset (Ext_axiom.error_kind error))
  | Ext_checker.Axiom_policy_error error ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:(Ext_axiom.policy_check_error_reason_code error)
           ~section:(Ext_bytes.section_name error.Ext_axiom.policy_section)
           ~offset:error.Ext_axiom.policy_offset
           (Ext_axiom.policy_check_error_kind error))

let graph_error context error =
  let kind =
    match error.Ext_session.reason with
    | Ext_session.Export_hash_mismatch
    | Ext_session.Certificate_hash_mismatch ->
        "import_hash_mismatch"
    | Ext_session.Missing_import | Ext_session.Missing_certificate_hash
    | Ext_session.Duplicate_import | Ext_session.Import_cycle
    | Ext_session.Resource_limit ->
        "import_not_found"
  in
  render_error context
    (Ext_result.checker_error
       ~reason_code:(Ext_session.graph_reason_code error.Ext_session.reason)
       ~section:"imports" ~offset:error.Ext_session.offset kind)

let load_error context = function
  | Ext_import_store.Import_dir_unavailable ->
      render_error context
        (Ext_result.checker_error ~reason_code:"missing_import"
           ~section:"imports" ~offset:0 "import_not_found")
  | Ext_import_store.Source_or_replay_input_rejected ->
      render_error context
        (Ext_result.checker_error ~reason_code:"source_input_forbidden"
           ~section:"imports" ~offset:0 "certificate_decode_error")
  | Ext_import_store.Certificate_decode_error error ->
      phase_error context (Ext_checker.Decode_error error)
  | Ext_import_store.Certificate_hash_mismatch mismatch ->
      render_error context
        (Ext_result.checker_error
           ~reason_code:mismatch.Ext_import_store.hash_mismatch_kind
           ~section:mismatch.Ext_import_store.hash_mismatch_section
           ~offset:mismatch.Ext_import_store.hash_mismatch_offset
           mismatch.Ext_import_store.hash_mismatch_kind)
  | Ext_import_store.Duplicate_import_binding { duplicate_offset; _ } ->
      render_error context
        (Ext_result.checker_error ~reason_code:"duplicate_import"
           ~section:"imports" ~offset:duplicate_offset "import_not_found")

let session_error context = function
  | Ext_session.Load_error error -> load_error context error
  | Ext_session.Check_error error -> phase_error context error
  | Ext_session.Graph_error error -> graph_error context error

let policy_input_error context =
  render_error context
    (Ext_result.checker_error ~reason_code:"request_axiom_policy_invalid"
       ~section:"policy" ~offset:0 "policy_input_error")

let certificate_input_error () =
  Ext_result.render_failed
    (Ext_result.checker_error ~reason_code:"certificate_input_unavailable"
       ~section:"certificate" ~offset:0 "certificate_decode_error")

let internal_error context =
  render_error context
    (Ext_result.checker_error ~reason_code:"checker_reported_internal_error"
       ~section:"checker" ~offset:0 "checker_internal_error")

let checked_result checked =
  Ext_result.render_checked
    ~module_name:(Ext_name.to_string (Ext_checker.module_name checked))
    ~certificate_hash:(Ext_result.wire_hash (Ext_checker.certificate_hash checked))
    ~export_hash:(Ext_result.wire_hash (Ext_checker.export_hash checked))
    ~axiom_report_hash:
      (Ext_result.wire_hash (Ext_checker.axiom_report_hash checked))

let check options =
  match
    (options.cert, options.import_dir, options.policy, options.policy_hash)
  with
  | Some cert_path, Some import_dir, Some policy_path, Some policy_hash -> (
      match Ext_import_store.read_binary_file cert_path with
      | Error (Ext_import_store.Certificate_decode_error error) ->
          rejected (phase_error empty_context (Ext_checker.Decode_error error))
      | Error _ -> rejected (certificate_input_error ())
      | Ok certificate_bytes ->
          let context = context_of_bytes certificate_bytes in
          (match Ext_import_store.read_binary_file policy_path with
          | Error _ -> rejected (policy_input_error context)
          | Ok policy_bytes -> (
              if
                Ext_hash.sha256_prefixed_hex_of_string policy_bytes
                <> policy_hash
              then rejected (policy_input_error context)
              else
                match Ext_axiom.parse_policy_toml policy_bytes with
                | Error _ -> rejected (policy_input_error context)
                | Ok policy -> (
                    try
                      match
                        Ext_session.check_high_trust import_dir policy
                          certificate_bytes
                      with
                      | Ok session -> ok (checked_result session.Ext_session.leaf)
                      | Error error -> rejected (session_error context error)
                    with _ -> internal_failure (internal_error context)))))
  | _ -> cli_error "missing required checker input"

let run args =
  match args with
  | [ "--version" ] -> ok Ext_result.version_text
  | _ when List.mem "--version" args -> cli_error "--version must be used alone"
  | _ -> (
      match parse args empty_options with
      | Parse_error message -> cli_error message
      | Parsed options -> (
          match missing_required options with
          | Some message -> cli_error message
          | None ->
              (try check options
               with _ -> internal_failure (internal_error empty_context))))
