let schema = "npa.independent-checker.checker_raw_result.v1"

let checker_id = "npa-checker-ext"

let checker_version = "0.2.0"

let certificate_format = "NPA-CERT-0.2.0"

let core_spec = "NPA-Core-0.2.0"

let implementation_profile = "ocaml-clean-room"

let project_directory = "checkers/npa-checker-ext/"

let cli_contract = "m0-04:first-release-cli"

let feature_policy_contract = "m0-05:first-release-empty-core-feature-set"

let checker_identity_manifest_signature_required = false

let build_identity_inputs sha256_source_identity =
  [
    "checker_id:" ^ checker_id;
    "checker_version:" ^ checker_version;
    "certificate_format:" ^ certificate_format;
    "core_spec:" ^ core_spec;
    "implementation_profile:" ^ implementation_profile;
    "project_directory:" ^ project_directory;
    "cli_contract:" ^ cli_contract;
    "feature_policy_contract:" ^ feature_policy_contract;
    "vendored_sha256_source_identity:" ^ sha256_source_identity;
  ]

let checker_build_material_for_sha256_source_identity sha256_source_identity =
  String.concat "\000" (build_identity_inputs sha256_source_identity)

let checker_build_hash_for_sha256_source_identity sha256_source_identity =
  Ext_hash.sha256_prefixed_hex_of_string
    (checker_build_material_for_sha256_source_identity sha256_source_identity)

let checker_build_hash =
  checker_build_hash_for_sha256_source_identity Ext_hash.vendored_sha256_source_identity

let version_text =
  String.concat "\n"
    [
      checker_id ^ " " ^ checker_version;
      "checker_build_hash " ^ checker_build_hash;
      "certificate_format " ^ certificate_format;
      "core_spec " ^ core_spec;
      "implementation_profile " ^ implementation_profile;
      "project_directory " ^ project_directory;
      "feature_policy_contract " ^ feature_policy_contract;
      "vendored_sha256_source_identity " ^ Ext_hash.vendored_sha256_source_identity;
      "checker_identity_manifest_signature_required "
      ^ string_of_bool checker_identity_manifest_signature_required;
    ]
  ^ "\n"

type checker_error = {
  kind : string;
  reason_code : string option;
  declaration : string option;
  core_path : string list option;
  section : string option;
  offset : int option;
  expected_hash : string option;
  actual_hash : string option;
}

let checker_error ?reason_code ?declaration ?core_path ?section ?offset
    ?expected_hash ?actual_hash kind =
  {
    kind;
    reason_code;
    declaration;
    core_path;
    section;
    offset;
    expected_hash;
    actual_hash;
  }

let json_escape text =
  let buffer = Buffer.create (String.length text) in
  String.iter
    (fun ch ->
      match ch with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\b' -> Buffer.add_string buffer "\\b"
      | '\012' -> Buffer.add_string buffer "\\f"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | _ ->
          let code = Char.code ch in
          if code < 0x20 then Buffer.add_string buffer (Printf.sprintf "\\u%04x" code)
          else Buffer.add_char buffer ch)
    text;
  Buffer.contents buffer

let json_string text = "\"" ^ json_escape text ^ "\""

let render_error error =
  let fields =
    [ "\"kind\": " ^ json_string error.kind ]
    @ (match error.reason_code with
      | None -> []
      | Some reason -> [ "\"reason_code\": " ^ json_string reason ])
    @ (match error.declaration with
      | None -> []
      | Some declaration ->
          [ "\"declaration\": " ^ json_string declaration ])
    @ (match error.core_path with
      | None -> []
      | Some path ->
          [
            "\"core_path\": ["
            ^ String.concat ", " (List.map json_string path)
            ^ "]";
          ])
    @ (match error.section with
      | None -> []
      | Some section -> [ "\"section\": " ^ json_string section ])
    @
    (match error.offset with
    | None -> []
    | Some offset -> [ "\"offset\": " ^ string_of_int offset ])
    @ (match error.expected_hash with
      | None -> []
      | Some hash -> [ "\"expected_hash\": " ^ json_string hash ])
    @ (match error.actual_hash with
      | None -> []
      | Some hash -> [ "\"actual_hash\": " ^ json_string hash ])
  in
  "{\n    " ^ String.concat ",\n    " fields ^ "\n  }"

let wire_hash hash = "sha256:" ^ Ext_sha256.to_hex (Bytes.of_string hash)

let identity_fields status =
  "  \"schema\": " ^ json_string schema ^ ",\n"
  ^ "  \"checker_id\": " ^ json_string checker_id ^ ",\n"
  ^ "  \"checker_version\": " ^ json_string checker_version ^ ",\n"
  ^ "  \"checker_build_hash\": " ^ json_string checker_build_hash ^ ",\n"
  ^ "  \"status\": " ^ json_string status

let render_failed ?module_name ?certificate_hash error =
  let context =
    (match module_name with
    | None -> ""
    | Some name -> ",\n  \"module\": " ^ json_string name)
    ^
    match certificate_hash with
    | None -> ""
    | Some hash -> ",\n  \"certificate_hash\": " ^ json_string hash
  in
  "{\n" ^ identity_fields "failed" ^ context ^ ",\n"
  ^ "  \"error\": " ^ render_error error ^ "\n}\n"

let render_checked ~module_name ~certificate_hash ~export_hash
    ~axiom_report_hash =
  "{\n" ^ identity_fields "checked"
  ^ ",\n  \"module\": " ^ json_string module_name
  ^ ",\n  \"certificate_hash\": " ^ json_string certificate_hash
  ^ ",\n  \"export_hash\": " ^ json_string export_hash
  ^ ",\n  \"axiom_report_hash\": " ^ json_string axiom_report_hash
  ^ "\n}\n"

let unsupported_core_feature ?offset _feature =
  render_failed
    (checker_error ~reason_code:"unsupported_core_feature"
       ~section:"core_features" ?offset "unsupported_core_feature")

let decode_failure ~kind ~reason_code ~section ~offset =
  render_failed
    (checker_error ~reason_code ~section ~offset kind)

let hash_mismatch_failure ~kind ~reason_code ~section ~offset =
  render_failed
    (checker_error ~reason_code ~section ~offset kind)

let import_failure ~kind ~reason_code ~section ~offset =
  render_failed
    (checker_error ~reason_code ~section ~offset kind)

let axiom_report_failure ~section ~offset =
  render_failed
    (checker_error ~reason_code:"axiom_report_mismatch" ~section ~offset
       "axiom_report_mismatch")

let axiom_policy_failure ~reason_code ~section ~offset =
  render_failed
    (checker_error ~reason_code ~section ~offset "forbidden_axiom")

let decode_error_kind error =
  match error.Ext_bytes.reason with
  | Ext_bytes.Noncanonical_uvar
  | Ext_bytes.Invalid_utf8
  | Ext_bytes.Empty_name
  | Ext_bytes.Empty_name_component
  | Ext_bytes.Dotted_name_component
  | Ext_bytes.Invalid_name_component
  | Ext_bytes.Duplicate_name
  | Ext_bytes.Duplicate_declaration
  | Ext_bytes.Non_normalized_level
  | Ext_bytes.Non_normalized_term
  | Ext_bytes.Noncanonical_order
  | Ext_bytes.Unused_table_entry ->
      "noncanonical_encoding"
  | Ext_bytes.Constrained_export_requires_format_upgrade ->
      "unsupported_schema_version"
  | Ext_bytes.Unexpected_eof
  | Ext_bytes.Uvar_overflow
  | Ext_bytes.Length_overflow
  | Ext_bytes.Format_mismatch
  | Ext_bytes.Core_spec_mismatch
  | Ext_bytes.Unknown_tag _
  | Ext_bytes.Dangling_reference
  | Ext_bytes.Trailing_bytes
  | Ext_bytes.Unresolved_metavariable
  | Ext_bytes.Resource_limit ->
      "certificate_decode_error"

let decode_error error =
  decode_failure ~kind:(decode_error_kind error)
    ~reason_code:(Ext_bytes.reason_code error.Ext_bytes.reason)
    ~section:(Ext_bytes.section_name error.Ext_bytes.section) ~offset:error.Ext_bytes.offset
