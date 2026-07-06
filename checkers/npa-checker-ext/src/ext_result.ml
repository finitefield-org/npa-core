let schema = "npa.independent-checker.checker_raw_result.v1"

let checker_id = "npa-checker-ext"

let checker_version = "0.1.0"

let certificate_format = "NPA-CERT-0.1"

let core_spec = "NPA-Core-0.1"

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
  section : string option;
  offset : int option;
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
    @ (match error.section with
      | None -> []
      | Some section -> [ "\"section\": " ^ json_string section ])
    @
    (match error.offset with
    | None -> []
    | Some offset -> [ "\"offset\": " ^ string_of_int offset ])
  in
  "{\n    " ^ String.concat ",\n    " fields ^ "\n  }"

let render_failed error =
  "{\n"
  ^ "  \"schema\": " ^ json_string schema ^ ",\n"
  ^ "  \"checker_id\": " ^ json_string checker_id ^ ",\n"
  ^ "  \"checker_version\": " ^ json_string checker_version ^ ",\n"
  ^ "  \"checker_build_hash\": " ^ json_string checker_build_hash ^ ",\n"
  ^ "  \"status\": \"failed\",\n"
  ^ "  \"error\": " ^ render_error error ^ "\n"
  ^ "}\n"

let skeleton_failure () =
  render_failed
    {
      kind = "checker_internal_error";
      reason_code = Some "checker_reported_internal_error";
      section = Some "skeleton";
      offset = Some 0;
    }

let unsupported_core_feature ?offset _feature =
  render_failed
    {
      kind = "unsupported_core_feature";
      reason_code = Some "unsupported_core_feature";
      section = Some "core_features";
      offset;
    }

let decode_failure ~kind ~reason_code ~section ~offset =
  render_failed
    {
      kind;
      reason_code = Some reason_code;
      section = Some section;
      offset = Some offset;
    }

let hash_mismatch_failure ~kind ~reason_code ~section ~offset =
  render_failed
    {
      kind;
      reason_code = Some reason_code;
      section = Some section;
      offset = Some offset;
    }

let import_failure ~kind ~reason_code ~section ~offset =
  render_failed
    {
      kind;
      reason_code = Some reason_code;
      section = Some section;
      offset = Some offset;
    }

let axiom_report_failure ~section ~offset =
  render_failed
    {
      kind = "axiom_report_mismatch";
      reason_code = Some "axiom_report_mismatch";
      section = Some section;
      offset = Some offset;
    }

let axiom_policy_failure ~reason_code ~section ~offset =
  render_failed
    {
      kind = "forbidden_axiom";
      reason_code = Some reason_code;
      section = Some section;
      offset = Some offset;
    }

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
  | Ext_bytes.Unexpected_eof
  | Ext_bytes.Uvar_overflow
  | Ext_bytes.Length_overflow
  | Ext_bytes.Format_mismatch
  | Ext_bytes.Core_spec_mismatch
  | Ext_bytes.Unknown_tag _
  | Ext_bytes.Dangling_reference
  | Ext_bytes.Trailing_bytes
  | Ext_bytes.Unresolved_metavariable ->
      "certificate_decode_error"

let decode_error error =
  decode_failure ~kind:(decode_error_kind error)
    ~reason_code:(Ext_bytes.reason_code error.Ext_bytes.reason)
    ~section:(Ext_bytes.section_name error.Ext_bytes.section) ~offset:error.Ext_bytes.offset
