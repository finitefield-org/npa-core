let assert_equal label expected actual =
  if expected <> actual then
    failwith
      (label ^ ": expected " ^ String.escaped expected ^ " but got "
     ^ String.escaped actual)

let assert_int_equal label expected actual =
  if expected <> actual then
    failwith
      (label ^ ": expected " ^ string_of_int expected ^ " but got " ^ string_of_int actual)

let assert_int64_equal label expected actual =
  if expected <> actual then
    failwith
      (label ^ ": expected " ^ Int64.to_string expected ^ " but got " ^ Int64.to_string actual)

let assert_bool label value = if not value then failwith (label ^ ": expected true")

let assert_ok label result =
  match result with
  | Ok value -> value
  | Error error ->
      failwith
        (label ^ ": unexpected error " ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)

let contains text needle =
  let text_len = String.length text in
  let needle_len = String.length needle in
  let rec loop index =
    if index + needle_len > text_len then false
    else if String.sub text index needle_len = needle then true
    else loop (index + 1)
  in
  needle_len = 0 || loop 0

let assert_contains label needle text =
  if not (contains text needle) then
    failwith (label ^ ": missing " ^ String.escaped needle ^ " in " ^ String.escaped text)

let assert_cli_error label expected args =
  let result = Ext_cli.run args in
  assert_int_equal (label ^ " exit") 2 result.code;
  assert_equal (label ^ " stdout") "" result.stdout;
  assert_equal (label ^ " stderr") ("npa-checker-ext: " ^ expected ^ "\n") result.stderr

let bytes_of_codes codes =
  let bytes = Bytes.create (List.length codes) in
  List.iteri (fun index code -> Bytes.set bytes index (Char.chr code)) codes;
  bytes

let string_of_codes codes = Bytes.to_string (bytes_of_codes codes)

let mutate_byte text offset =
  if offset < 0 || offset >= String.length text then
    failwith ("cannot mutate byte at offset " ^ string_of_int offset);
  let bytes = Bytes.of_string text in
  let original = Char.code (Bytes.get bytes offset) in
  Bytes.set bytes offset (Char.chr (original lxor 0x01));
  Bytes.to_string bytes

let split_tabs line =
  let length = String.length line in
  let rec loop start fields =
    try
      let index = String.index_from line start '\t' in
      loop (index + 1) (String.sub line start (index - start) :: fields)
    with Not_found -> List.rev (String.sub line start (length - start) :: fields)
  in
  loop 0 []

let root_dir () =
  try Sys.getenv "NPA_CHECKER_EXT_ROOT"
  with Not_found -> Filename.concat (Sys.getcwd ()) "checkers/npa-checker-ext"

let boundary_input length =
  let bytes = Bytes.create length in
  for index = 0 to length - 1 do
    Bytes.set bytes index (Char.chr (((index * 17) + 31) land 0xff))
  done;
  bytes

let vector_input source label length =
  match (source, label) with
  | "standard", "empty" -> Bytes.empty
  | "standard", "abc" -> Bytes.of_string "abc"
  | "standard", "long-standard" ->
      Bytes.of_string "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
  | "standard", "million-a" -> Bytes.make 1_000_000 'a'
  | "boundary", _ -> boundary_input length
  | "rust-sha2", "build-identity-domain" ->
      Bytes.of_string
        "npa-checker-ext\000checker-build\000vendored-sha256-source:v1\000NPA-CERT-0.1\000NPA-Core-0.1"
  | "rust-sha2", "level-zero-domain" -> Bytes.of_string "npa.hash.domain\000level\000zero"
  | "rust-sha2", "term-sort-zero-domain" ->
      Bytes.of_string "npa.hash.domain\000term\000sort\000zero"
  | "rust-sha2", "binary-all-bytes" ->
      let bytes = Bytes.create 256 in
      for index = 0 to 255 do
        Bytes.set bytes index (Char.chr index)
      done;
      bytes
  | "rust-sha2", "newline-path-bytes" ->
      Bytes.of_string "npa-checker-ext\000newline-bytes\000path/with/backslash\\name\nline\r\n"
  | _ -> failwith ("unknown sha256 vector " ^ source ^ ":" ^ label)

let chunk_sizes = [| 1; 2; 3; 5; 8; 13; 21; 34; 55; 64 |]

let digest_streaming bytes =
  let state = Ext_sha256.create () in
  let offset = ref 0 in
  let chunk_index = ref 0 in
  while !offset < Bytes.length bytes do
    let chunk_size = chunk_sizes.(!chunk_index mod Array.length chunk_sizes) in
    let take = min chunk_size (Bytes.length bytes - !offset) in
    Ext_sha256.update_subbytes state bytes !offset take;
    offset := !offset + take;
    incr chunk_index
  done;
  Ext_sha256.finalize state

let assert_sha256 label bytes expected_hex =
  let digest = Ext_sha256.digest_bytes bytes in
  assert_int_equal (label ^ " raw length") 32 (Bytes.length digest);
  assert_equal (label ^ " one-shot hex") expected_hex (Ext_sha256.to_hex digest);
  assert_equal (label ^ " prefixed hex") ("sha256:" ^ expected_hex)
    (Ext_hash.sha256_prefixed_hex_of_bytes bytes);
  assert_equal (label ^ " streaming hex") expected_hex
    (Ext_sha256.to_hex (digest_streaming bytes))

let run_sha256_tests () =
  let path = Filename.concat (root_dir ()) "test/golden/sha256_vectors.tsv" in
  let channel = open_in path in
  let count = ref 0 in
  (try
     while true do
       let line = input_line channel in
       if String.length line > 0 && line.[0] <> '#' then
         match split_tabs line with
         | [ source; label; length_text; expected_hex ] ->
             let length = int_of_string length_text in
             let bytes = vector_input source label length in
             assert_int_equal (label ^ " vector length") length (Bytes.length bytes);
             assert_sha256 (source ^ ":" ^ label) bytes expected_hex;
             incr count
         | _ -> failwith ("malformed sha256 vector line: " ^ line)
     done
   with End_of_file -> close_in channel);
  assert_int_equal "sha256 vector count" 18 !count;
  let expected_build_hash =
    Ext_result.checker_build_hash_for_sha256_source_identity Ext_sha256.source_identity
  in
  assert_equal "checker build hash uses vendored sha256 source identity" expected_build_hash
    Ext_result.checker_build_hash;
  assert_bool "checker build hash is not placeholder"
    (Ext_result.checker_build_hash
    <> "sha256:0000000000000000000000000000000000000000000000000000000000000000");
  assert_bool "checker build hash changes with vendored sha256 identity"
    (Ext_result.checker_build_hash
    <> Ext_result.checker_build_hash_for_sha256_source_identity
         "vendored-sha256-source:test-change")

let run_cli_tests () =
  let zero_hash = "sha256:" ^ String.make 64 '0' in
  let version = Ext_cli.run [ "--version" ] in
  let expected_version =
    "npa-checker-ext 0.2.0\n"
    ^ "checker_build_hash " ^ Ext_result.checker_build_hash ^ "\n"
    ^ "certificate_format NPA-CERT-0.2.0\n"
    ^ "core_spec NPA-Core-0.2.0\n"
    ^ "implementation_profile ocaml-clean-room\n"
    ^ "project_directory checkers/npa-checker-ext/\n"
    ^ "feature_policy_contract m0-05:first-release-empty-core-feature-set\n"
    ^ "vendored_sha256_source_identity vendored-sha256-source:v1\n"
    ^ "checker_identity_manifest_signature_required false\n"
  in
  assert_int_equal "version exit" 0 version.code;
  assert_equal "version exact stdout" expected_version version.stdout;
  assert_equal "version stderr" "" version.stderr;

  assert_cli_error "no args" "missing required --cert" [];
  assert_cli_error "version mixed" "--version must be used alone" [ "--version"; "--output"; "json" ];
  assert_cli_error "source cert path" "--cert must not point to .npa source"
    [ "--cert"; "example.npa"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--output"; "json" ];
  assert_cli_error "source policy path" "--policy must not point to .npa source"
    [ "--cert"; "example.npcert"; "--import-dir"; "imports"; "--policy"; "policy.npa"; "--output"; "json" ];
  assert_cli_error "source import dir" "--import-dir must not point to .npa source"
    [ "--cert"; "example.npcert"; "--import-dir"; "src/module.npa/imports"; "--policy"; "policy.toml"; "--output"; "json" ];
  assert_cli_error "bad output" "--output must be json"
    [ "--cert"; "example.npcert"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--output"; "pretty" ];
  assert_cli_error "bad policy hash" "--policy-hash must be sha256:<lower-hex>"
    [ "--cert"; "example.npcert"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--policy-hash"; "sha256:BAD"; "--output"; "json" ];
  assert_cli_error "duplicate cert" "duplicate --cert"
    [
      "--cert";
      "a.npcert";
      "--cert";
      "b.npcert";
      "--import-dir";
      "imports";
      "--policy";
      "policy.toml";
      "--output";
      "json";
    ];
  assert_cli_error "missing cert value" "missing value for --cert"
    [ "--cert"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--output"; "json" ];
  assert_cli_error "missing output value" "missing value for --output"
    [ "--cert"; "example.npcert"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--output"; "--policy" ];
  assert_cli_error "unknown flag" "unknown flag --audit-bundle" [ "--audit-bundle"; "bundle" ];
  assert_cli_error "positional source" "positional .npa source input is forbidden" [ "example.npa" ];
  assert_cli_error "positional input" "positional input is forbidden" [ "example.npcert" ];
  assert_cli_error "missing policy hash" "missing required --policy-hash"
    [ "--cert"; "example.npcert"; "--import-dir"; "imports"; "--policy"; "policy.toml"; "--output"; "json" ];

  let check_shape =
    Ext_cli.run
      [
        "--cert";
        "example.npcert";
        "--import-dir";
        "imports";
        "--policy";
        "policy.toml";
        "--policy-hash";
        zero_hash;
        "--output";
        "json";
      ]
  in
  assert_int_equal "check shape exit" 1 check_shape.code;
  assert_equal "check shape stderr" "" check_shape.stderr;
  assert_contains "check shape schema" "\"schema\": \"npa.independent-checker.checker_raw_result.v1\""
    check_shape.stdout;
  assert_contains "check shape status" "\"status\": \"failed\"" check_shape.stdout;
  assert_contains "check shape error" "\"kind\": \"certificate_decode_error\""
    check_shape.stdout;
  assert_contains "check shape reason"
    "\"reason_code\": \"certificate_input_unavailable\"" check_shape.stdout

let assert_feature_policy_rejects_unsupported feature offset expected_kind =
  assert_bool (feature ^ " is not supported in first release")
    (not (Ext_feature.is_supported_first_release feature));
  assert_equal (feature ^ " fixture expected kind") "unsupported_core_feature" expected_kind;
  let report = [ { Ext_feature.feature; offset = Some offset } ] in
  match Ext_feature.raw_result_for_first_release_report report with
  | None -> failwith (feature ^ ": expected unsupported_core_feature raw result")
  | Some raw ->
      assert_contains (feature ^ " failed status") "\"status\": \"failed\"" raw;
      assert_contains (feature ^ " unsupported kind")
        ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (feature ^ " unsupported reason")
        ("\"reason_code\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (feature ^ " section") "\"section\": \"core_features\"" raw;
      assert_contains (feature ^ " offset") ("\"offset\": " ^ string_of_int offset) raw

let run_feature_policy_fixture_tests () =
  let path = Filename.concat (root_dir ()) "test/fixtures/feature_policy.tsv" in
  let channel = open_in path in
  let count = ref 0 in
  (try
     while true do
       let line = input_line channel in
       if String.length line > 0 && line.[0] <> '#' then
         match split_tabs line with
         | [ feature; offset_text; expected_kind ] ->
             assert_feature_policy_rejects_unsupported feature (int_of_string offset_text)
               expected_kind;
             incr count
         | _ -> failwith ("malformed feature policy fixture line: " ^ line)
     done
   with End_of_file -> close_in channel);
  assert_int_equal "feature policy fixture count" 3 !count

let run_feature_policy_tests () =
  assert_equal "feature policy input shape"
    "canonical-certificate-feature-report-only" Ext_feature.policy_input_shape;
  assert_bool "first-release supported core features are empty"
    (Ext_feature.supported_core_features = []);
  (match Ext_feature.check_first_release_report [] with
  | Ext_feature.Feature_policy_ok -> ()
  | Ext_feature.Unsupported_core_feature _ ->
      failwith "empty MVP feature report must not be rejected");
  assert_bool "empty MVP report has no raw failure"
    (Ext_feature.raw_result_for_first_release_report [] = None);
  run_feature_policy_fixture_tests ()

let decode_error_raw_result error =
  Ext_result.decode_error error

let assert_decode_error label expected_kind expected_reason expected_section expected_offset result =
  match result with
  | Ok _ -> failwith (label ^ ": expected decode error")
  | Error error ->
      assert_equal (label ^ " stable kind") expected_kind (Ext_result.decode_error_kind error);
      assert_equal (label ^ " reason") (Ext_bytes.reason_code expected_reason)
        (Ext_bytes.reason_code error.Ext_bytes.reason);
      assert_equal (label ^ " section") (Ext_bytes.section_name expected_section)
        (Ext_bytes.section_name error.Ext_bytes.section);
      assert_int_equal (label ^ " offset") expected_offset error.Ext_bytes.offset;
      let raw = decode_error_raw_result error in
      assert_contains (label ^ " raw kind") ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ Ext_bytes.reason_code expected_reason ^ "\"")
        raw;
      assert_contains (label ^ " raw section")
        ("\"section\": \"" ^ Ext_bytes.section_name expected_section ^ "\"")
        raw;
      assert_contains (label ^ " raw offset") ("\"offset\": " ^ string_of_int expected_offset)
        raw

let assert_read_uvar label codes expected offset =
  let reader = Ext_bytes.of_bytes (bytes_of_codes codes) in
  match Ext_bytes.read_uvar Ext_bytes.Imports reader with
  | Error error ->
      failwith
        (label ^ ": unexpected decode error " ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (actual, next) ->
      assert_int64_equal (label ^ " value") expected actual;
      assert_int_equal (label ^ " offset") offset (Ext_bytes.offset next);
      assert_int_equal (label ^ " original offset") 0 (Ext_bytes.offset reader)

let run_decoder_bytes_tests () =
  let mutable_input = Bytes.of_string "ab" in
  let reader = Ext_bytes.of_bytes mutable_input in
  Bytes.set mutable_input 0 'z';
  (match Ext_bytes.read_byte Ext_bytes.Full_certificate reader with
  | Error error ->
      failwith
        ("immutable reader byte: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (byte, next) ->
      assert_int_equal "immutable reader copied input" (Char.code 'a') byte;
      assert_int_equal "immutable reader original offset" 0 (Ext_bytes.offset reader);
      assert_int_equal "immutable reader next offset" 1 (Ext_bytes.offset next));

  (match Ext_bytes.take Ext_bytes.Full_certificate 2 (Ext_bytes.of_string "abcd") with
  | Error error ->
      failwith ("take: unexpected decode error " ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (taken, next) ->
      assert_equal "take bytes" "ab" taken;
      assert_int_equal "take offset" 2 (Ext_bytes.offset next);
      assert_int_equal "take remaining" 2 (Ext_bytes.remaining next));

  assert_read_uvar "uvar zero" [ 0x00 ] 0L 1;
  assert_read_uvar "uvar one-byte max" [ 0x7f ] 127L 1;
  assert_read_uvar "uvar 128" [ 0x80; 0x01 ] 128L 2;
  assert_read_uvar "uvar 300" [ 0xac; 0x02 ] 300L 2;
  assert_read_uvar "uvar u64 max"
    [ 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x01 ]
    Int64.minus_one 10;

  assert_decode_error "empty input" "certificate_decode_error"
    Ext_bytes.Unexpected_eof Ext_bytes.Full_certificate 0
    (Ext_bytes.read_byte Ext_bytes.Full_certificate Ext_bytes.empty);
  assert_decode_error "noncanonical zero" "noncanonical_encoding"
    Ext_bytes.Noncanonical_uvar Ext_bytes.Imports 1
    (Ext_bytes.read_uvar Ext_bytes.Imports (Ext_bytes.of_bytes (bytes_of_codes [ 0x80; 0x00 ])));
  assert_decode_error "overlong one" "noncanonical_encoding"
    Ext_bytes.Noncanonical_uvar Ext_bytes.Imports 1
    (Ext_bytes.read_uvar Ext_bytes.Imports (Ext_bytes.of_bytes (bytes_of_codes [ 0x81; 0x00 ])));
  assert_decode_error "uvar eof after continuation" "certificate_decode_error"
    Ext_bytes.Unexpected_eof Ext_bytes.Imports 1
    (Ext_bytes.read_uvar Ext_bytes.Imports (Ext_bytes.of_bytes (bytes_of_codes [ 0x80 ])));
  assert_decode_error "take eof" "certificate_decode_error" Ext_bytes.Unexpected_eof
    Ext_bytes.Full_certificate 1
    (Ext_bytes.take Ext_bytes.Full_certificate 2 (Ext_bytes.of_string "a"));
  assert_decode_error "uvar overflow" "certificate_decode_error" Ext_bytes.Uvar_overflow
    Ext_bytes.Imports 9
    (Ext_bytes.read_uvar Ext_bytes.Imports
       (Ext_bytes.of_bytes
          (bytes_of_codes
             [ 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x02 ])));
  let usize_overflow = Ext_bytes.encode_uvar (Int64.add (Int64.of_int max_int) 1L) in
  assert_decode_error "usize overflow" "certificate_decode_error" Ext_bytes.Length_overflow
    Ext_bytes.Imports (String.length usize_overflow - 1)
    (Ext_bytes.read_usize Ext_bytes.Imports (Ext_bytes.of_string usize_overflow));
  let too_many_imports = Ext_bytes.encode_uvar 4_097L in
  assert_decode_error "import count resource limit" "certificate_decode_error"
    Ext_bytes.Resource_limit Ext_bytes.Imports 0
    (Ext_bytes.read_count Ext_bytes.Imports
       (Ext_bytes.of_string too_many_imports));
  let too_many_terms = Ext_bytes.encode_uvar 100_001L in
  assert_decode_error "term count resource limit" "certificate_decode_error"
    Ext_bytes.Resource_limit Ext_bytes.Term_table 0
    (Ext_bytes.read_count Ext_bytes.Term_table
       (Ext_bytes.of_string too_many_terms))

let encode_uvar_int value = Ext_bytes.encode_uvar (Int64.of_int value)

let encode_string text = encode_uvar_int (String.length text) ^ text

let encode_raw_string text = encode_uvar_int (String.length text) ^ text

let encode_name components =
  encode_uvar_int (List.length components) ^ String.concat "" (List.map encode_string components)

let make_name components =
  match Ext_name.of_components components with
  | None -> failwith "test fixture constructed an invalid name"
  | Some name -> name

let make_unchecked_name components = components

let one_byte code = String.make 1 (Char.chr code)

let hash_bytes fill = String.make 32 (Char.chr fill)

let encode_level_zero = one_byte 0x00

let encode_level_succ inner = one_byte 0x01 ^ encode_uvar_int inner

let encode_level_max lhs rhs = one_byte 0x02 ^ encode_uvar_int lhs ^ encode_uvar_int rhs

let encode_level_imax lhs rhs = one_byte 0x03 ^ encode_uvar_int lhs ^ encode_uvar_int rhs

let encode_level_param name_id = one_byte 0x04 ^ encode_uvar_int name_id

let encode_term_sort level_id = one_byte 0x00 ^ encode_uvar_int level_id

let encode_term_bvar index = one_byte 0x01 ^ encode_uvar_int index

let encode_term_const global_ref levels =
  one_byte 0x02 ^ global_ref ^ encode_uvar_int (List.length levels)
  ^ String.concat "" (List.map encode_uvar_int levels)

let encode_term_app fn arg = one_byte 0x03 ^ encode_uvar_int fn ^ encode_uvar_int arg

let encode_term_lam ty body = one_byte 0x04 ^ encode_uvar_int ty ^ encode_uvar_int body

let encode_term_pi ty body = one_byte 0x05 ^ encode_uvar_int ty ^ encode_uvar_int body

let encode_term_let ty value body =
  one_byte 0x06 ^ encode_uvar_int ty ^ encode_uvar_int value ^ encode_uvar_int body

let encode_global_builtin name_id hash = one_byte 0x03 ^ encode_uvar_int name_id ^ hash

let encode_global_imported import_index name_id hash =
  one_byte 0x00 ^ encode_uvar_int import_index ^ encode_uvar_int name_id ^ hash

let encode_global_local decl_index = one_byte 0x01 ^ encode_uvar_int decl_index

let encode_usize_vec values =
  encode_uvar_int (List.length values) ^ String.concat "" (List.map encode_uvar_int values)

let encode_option payload =
  match payload with
  | None -> one_byte 0x00
  | Some value -> one_byte 0x01 ^ value

let encode_option_usize value =
  match value with
  | None -> encode_option None
  | Some value -> encode_option (Some (encode_uvar_int value))

let encode_option_hash value = encode_option value

let encode_reducibility reducibility =
  match reducibility with
  | `Reducible -> one_byte 0x00
  | `Opaque -> one_byte 0x01

let encode_opacity_opaque = one_byte 0x00

let encode_imports imports =
  encode_uvar_int (List.length imports)
  ^ String.concat ""
      (List.map
         (fun (module_components, export_hash, certificate_hash) ->
           encode_name module_components ^ export_hash ^ encode_option_hash certificate_hash)
         imports)

let encode_name_table names =
  encode_uvar_int (List.length names) ^ String.concat "" (List.map encode_name names)

let encode_level_table entries = encode_uvar_int (List.length entries) ^ String.concat "" entries

let encode_term_table entries = encode_uvar_int (List.length entries) ^ String.concat "" entries

let encode_dependency_entries entries =
  encode_uvar_int (List.length entries)
  ^ String.concat ""
      (List.map
         (fun (global_ref, decl_interface_hash) -> global_ref ^ decl_interface_hash)
         entries)

let encode_axiom_refs refs =
  encode_uvar_int (List.length refs)
  ^ String.concat ""
      (List.map
         (fun (global_ref, name_id, decl_interface_hash) ->
           global_ref ^ encode_uvar_int name_id ^ decl_interface_hash)
         refs)

let encode_axiom_decl_payload name_id universe_params ty =
  one_byte 0x00 ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ encode_uvar_int ty

let encode_universe_constraints constraints =
  encode_uvar_int (List.length constraints)
  ^ String.concat ""
      (List.map
         (fun (lhs, relation_tag, rhs) ->
           encode_uvar_int lhs ^ one_byte relation_tag ^ encode_uvar_int rhs)
         constraints)

let encode_constrained_axiom_decl_payload name_id universe_params constraints ty =
  one_byte 0x10 ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ encode_universe_constraints constraints ^ encode_uvar_int ty

let encode_def_decl_payload tag name_id universe_params ?(constraints = None) ty value
    reducibility =
  one_byte tag ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ (match constraints with
    | None -> ""
    | Some constraints -> encode_universe_constraints constraints)
  ^ encode_uvar_int ty ^ encode_uvar_int value ^ encode_reducibility reducibility

let encode_theorem_decl_payload tag name_id universe_params ?(constraints = None) ty proof =
  one_byte tag ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ (match constraints with
    | None -> ""
    | Some constraints -> encode_universe_constraints constraints)
  ^ encode_uvar_int ty ^ encode_uvar_int proof ^ encode_opacity_opaque

let encode_binder_types term_ids =
  encode_uvar_int (List.length term_ids) ^ String.concat "" (List.map encode_uvar_int term_ids)

let encode_constructor_specs constructors =
  encode_uvar_int (List.length constructors)
  ^ String.concat ""
      (List.map
         (fun (name_id, ty) -> encode_uvar_int name_id ^ encode_uvar_int ty)
         constructors)

let encode_recursor_spec spec =
  match spec with
  | None -> one_byte 0x00
  | Some (name_id, universe_params, ty, minor_start, major_index) ->
      one_byte 0x01 ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
      ^ encode_uvar_int ty ^ encode_uvar_int minor_start ^ encode_uvar_int major_index

let encode_inductive_decl_payload tag name_id universe_params ?(constraints = None) params
    indices sort constructors recursor =
  one_byte tag ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ (match constraints with
    | None -> ""
    | Some constraints -> encode_universe_constraints constraints)
  ^ encode_binder_types params ^ encode_binder_types indices ^ encode_uvar_int sort
  ^ encode_constructor_specs constructors ^ encode_recursor_spec recursor

let encode_mutual_inductive_spec name_id params indices sort constructors recursor =
  encode_uvar_int name_id ^ encode_binder_types params ^ encode_binder_types indices
  ^ encode_uvar_int sort ^ encode_constructor_specs constructors ^ encode_recursor_spec recursor

let encode_mutual_inductive_block_payload name_id universe_params constraints inductives =
  one_byte 0x04 ^ encode_uvar_int name_id ^ encode_usize_vec universe_params
  ^ encode_universe_constraints constraints ^ encode_uvar_int (List.length inductives)
  ^ String.concat "" inductives

let encode_decl_cert payload dependencies axiom_dependencies interface_hash certificate_hash =
  payload ^ encode_dependency_entries dependencies ^ encode_axiom_refs axiom_dependencies
  ^ interface_hash ^ certificate_hash

let encode_declarations entries =
  encode_uvar_int (List.length entries) ^ String.concat "" entries

let encode_export_kind tag = one_byte tag

let encode_export_entry_prefix name_id kind_tag universe_params ty body =
  encode_uvar_int name_id ^ encode_export_kind kind_tag ^ encode_usize_vec universe_params
  ^ encode_uvar_int ty ^ encode_option_usize body ^ hash_bytes 0x31 ^ encode_option_hash None
  ^ encode_option None ^ encode_option None ^ hash_bytes 0x32

let encode_export_entry name_id kind_tag universe_params ty body axiom_dependencies =
  encode_export_entry_prefix name_id kind_tag universe_params ty body
  ^ encode_axiom_refs axiom_dependencies

let encode_export_block entries =
  encode_uvar_int (List.length entries) ^ String.concat "" entries

let encode_axiom_report per_declaration module_axioms =
  encode_uvar_int (List.length per_declaration)
  ^ String.concat ""
      (List.map
         (fun (decl_index, direct_axioms, transitive_axioms) ->
           encode_uvar_int decl_index ^ encode_axiom_refs direct_axioms
           ^ encode_axiom_refs transitive_axioms)
         per_declaration)
  ^ encode_axiom_refs module_axioms

let encode_core_features features =
  encode_string "core_features" ^ encode_uvar_int (List.length features)
  ^ String.concat "" (List.map encode_string features)

let encode_hashes = hash_bytes 0xa1 ^ hash_bytes 0xa2 ^ hash_bytes 0xa3

let encode_header ?(format = Ext_cert.expected_format)
    ?(core_spec = Ext_cert.expected_core_spec) module_components =
  encode_string format ^ encode_string core_spec ^ encode_name module_components

let read_binary_file path =
  let channel = open_in_bin path in
  let length = in_channel_length channel in
  let contents = really_input_string channel length in
  close_in channel;
  contents

type golden_hash_fixture = {
  golden_byte_len : int;
  golden_export_hash : string;
  golden_axiom_report_hash : string;
  golden_certificate_hash : string;
}

let golden_hash_fixture label =
  let path =
    Filename.concat (root_dir ()) "test/golden/legacy_certificate_hashes.tsv"
  in
  let contents = read_binary_file path in
  let rec loop lines =
    match lines with
    | [] -> failwith ("missing golden hash fixture " ^ label)
    | line :: rest ->
        if line = "" || contains line "label\t" then loop rest
        else (
          match split_tabs line with
          | [ current; byte_len; export_hash; axiom_report_hash; certificate_hash ]
            when current = label ->
              {
                golden_byte_len = int_of_string byte_len;
                golden_export_hash = export_hash;
                golden_axiom_report_hash = axiom_report_hash;
                golden_certificate_hash = certificate_hash;
              }
          | _ -> loop rest)
  in
  loop (String.split_on_char '\n' contents)

let hex_of_raw_hash hash = Ext_sha256.to_hex (Bytes.of_string hash)

let decode_module_bytes label bytes =
  match Ext_cert.read_module (Ext_bytes.of_string bytes) with
  | Ok (decoded, next) ->
      assert_int_equal (label ^ " offset") (String.length bytes) (Ext_bytes.offset next);
      decoded
  | Error error ->
      failwith
        (label ^ ": unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)

let assert_header label expected_module header =
  assert_equal (label ^ " format") Ext_cert.expected_format header.Ext_cert.format;
  assert_equal (label ^ " core spec") Ext_cert.expected_core_spec header.Ext_cert.core_spec;
  assert_equal (label ^ " module") expected_module (Ext_name.to_string header.Ext_cert.module_name)

let run_decoder_header_tests () =
  let golden_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let golden = read_binary_file golden_path in
  (match Ext_cert.read_header (Ext_bytes.of_string golden) with
  | Error error ->
      failwith ("golden header: unexpected decode error " ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (header, next) ->
      assert_equal "golden header format" Ext_cert.expected_format header.Ext_cert.format;
      assert_equal "golden header core spec" Ext_cert.expected_core_spec header.Ext_cert.core_spec;
      assert_bool "golden header module is structured"
        (String.length (Ext_name.to_string header.Ext_cert.module_name) > 0);
      assert_bool "golden header advances reader" (Ext_bytes.offset next > 0));

  let assert_versioned_header label relative_path expected_format expected_core
      expected_version =
    let bytes = read_binary_file (Filename.concat (root_dir ()) relative_path) in
    match Ext_cert.read_header (Ext_bytes.of_string bytes) with
    | Error error ->
        failwith
          (label ^ ": unexpected decode error "
          ^ Ext_bytes.reason_code error.Ext_bytes.reason)
    | Ok (header, _) ->
        assert_equal (label ^ " format") expected_format header.Ext_cert.format;
        assert_equal (label ^ " core spec") expected_core
          header.Ext_cert.core_spec;
        assert_bool (label ^ " version")
          (header.Ext_cert.version = expected_version)
  in
  assert_versioned_header "current header"
    "../../testdata/certificates/security/mutual-inductive-constructor-universe-bound-v0.2.npcert"
    Ext_cert.current_format Ext_cert.current_core_spec Ext_cert.Current;
  assert_versioned_header "previous header"
    "../../testdata/package/npa-mathlib-downstream/vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert"
    Ext_cert.previous_format Ext_cert.previous_core_spec Ext_cert.Previous;

  let valid_header = encode_header [ "Std"; "Nat" ] in
  (match Ext_cert.read_header (Ext_bytes.of_string valid_header) with
  | Error error ->
      failwith ("valid header: unexpected decode error " ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (header, next) ->
      assert_header "valid header" "Std.Nat" header;
      assert_int_equal "valid header offset" (String.length valid_header) (Ext_bytes.offset next));

  let bad_format = encode_header ~format:"BAD-CERT" [ "Std"; "Nat" ] in
  assert_decode_error "format mismatch" "certificate_decode_error" Ext_bytes.Format_mismatch
    Ext_bytes.Header_format (String.length (encode_string "BAD-CERT"))
    (Ext_cert.read_header (Ext_bytes.of_string bad_format));

  let core_prefix = encode_string Ext_cert.expected_format ^ encode_string "NPA-Core-X" in
  let bad_core = core_prefix ^ encode_name [ "Std"; "Nat" ] in
  assert_decode_error "core spec mismatch" "certificate_decode_error"
    Ext_bytes.Core_spec_mismatch Ext_bytes.Header_core_spec (String.length core_prefix)
    (Ext_cert.read_header (Ext_bytes.of_string bad_core));

  let mixed_pair_prefix =
    encode_string Ext_cert.current_format
    ^ encode_string Ext_cert.previous_core_spec
  in
  let mixed_pair = mixed_pair_prefix ^ encode_name [ "Std"; "Nat" ] in
  assert_decode_error "mixed header pair" "certificate_decode_error"
    Ext_bytes.Core_spec_mismatch Ext_bytes.Header_core_spec
    (String.length mixed_pair_prefix)
    (Ext_cert.read_header (Ext_bytes.of_string mixed_pair));

  let invalid_utf8 = encode_raw_string (string_of_codes [ 0xff ]) in
  assert_decode_error "invalid utf8 header" "noncanonical_encoding" Ext_bytes.Invalid_utf8
    Ext_bytes.Header_format 1
    (Ext_cert.read_header (Ext_bytes.of_string invalid_utf8));

  let empty_module_prefix =
    encode_string Ext_cert.expected_format ^ encode_string Ext_cert.expected_core_spec
  in
  let empty_module = empty_module_prefix ^ encode_uvar_int 0 in
  assert_decode_error "empty module name" "noncanonical_encoding" Ext_bytes.Empty_name
    Ext_bytes.Header_module (String.length empty_module_prefix)
    (Ext_cert.read_header (Ext_bytes.of_string empty_module));

  let empty_component_prefix = empty_module_prefix ^ encode_uvar_int 1 in
  let empty_component = empty_component_prefix ^ encode_string "" in
  assert_decode_error "empty name component" "noncanonical_encoding"
    Ext_bytes.Empty_name_component Ext_bytes.Header_module (String.length empty_component_prefix)
    (Ext_cert.read_header (Ext_bytes.of_string empty_component));

  let dotted_component_prefix = empty_module_prefix ^ encode_uvar_int 1 ^ encode_uvar_int 7 in
  let dotted_component = dotted_component_prefix ^ "Std.Nat" in
  assert_decode_error "dotted name component" "noncanonical_encoding"
    Ext_bytes.Dotted_name_component Ext_bytes.Header_module
    (String.length dotted_component_prefix + 3)
    (Ext_cert.read_header (Ext_bytes.of_string dotted_component));

  let operator_component_prefix = empty_module_prefix ^ encode_uvar_int 1 ^ encode_uvar_int 1 in
  let operator_component = operator_component_prefix ^ "+" in
  assert_decode_error "operator name component" "noncanonical_encoding"
    Ext_bytes.Invalid_name_component Ext_bytes.Header_module
    (String.length operator_component_prefix)
    (Ext_cert.read_header (Ext_bytes.of_string operator_component));

  let prime_component = empty_module_prefix ^ encode_name [ "add_comm'" ] in
  (match Ext_cert.read_header (Ext_bytes.of_string prime_component) with
  | Error error ->
      failwith
        ("prime component: unexpected decode error "
        ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (header, _) ->
      assert_equal "prime component name" "add_comm'"
        (Ext_name.to_string header.Ext_cert.module_name));

  let name_table = encode_uvar_int 2 ^ encode_name [ "A" ] ^ encode_name [ "Std"; "Nat" ] in
  (match Ext_cert.read_name_table (Ext_bytes.of_string name_table) with
  | Error error ->
      failwith ("name table: unexpected decode error " ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (entries, next) ->
      assert_int_equal "name table length" 2 (List.length entries);
      assert_equal "name table first name" "A" (Ext_name.to_string (List.hd entries).Ext_cert.name);
      assert_int_equal "name table offset" (String.length name_table) (Ext_bytes.offset next));

  let duplicate_entry = encode_name [ "A" ] in
  let duplicate_name_table = encode_uvar_int 2 ^ duplicate_entry ^ duplicate_entry in
  assert_decode_error "duplicate name table entry" "noncanonical_encoding" Ext_bytes.Duplicate_name
    Ext_bytes.Name_table (String.length (encode_uvar_int 2 ^ duplicate_entry))
    (Ext_cert.read_name_table (Ext_bytes.of_string duplicate_name_table))

let level_value (entry : Ext_level.located) = entry.level

let term_value (entry : Ext_term.located) = entry.term

let run_decoder_tables_tests () =
  let universe_name = make_name [ "u" ] in
  let nat_name = make_name [ "Nat" ] in
  let names = [ universe_name; nat_name ] in
  let valid_level_table =
    encode_uvar_int 3 ^ encode_level_zero ^ encode_level_param 0 ^ encode_level_succ 0
  in
  let levels =
    match Ext_level.read_table names (Ext_bytes.of_string valid_level_table) with
    | Error error ->
        failwith
          ("valid level table: unexpected decode error "
         ^ Ext_bytes.reason_code error.Ext_bytes.reason)
    | Ok (levels, next) ->
        assert_int_equal "valid level table offset" (String.length valid_level_table)
          (Ext_bytes.offset next);
        assert_int_equal "valid level table length" 3 (List.length levels);
        levels
  in
  (match List.map level_value levels with
  | [ Ext_level.Zero; Ext_level.Param name; Ext_level.Succ Ext_level.Zero ] ->
      assert_equal "valid level param name" "u" (Ext_name.to_string name)
  | _ -> failwith "valid level table did not decode into structured level AST");

  let builtin_nat = encode_global_builtin 1 (hash_bytes 0x42) in
  let valid_term_table =
    encode_uvar_int 7 ^ encode_term_sort 0 ^ encode_term_bvar 0
    ^ encode_term_const builtin_nat [ 0; 1 ]
    ^ encode_term_app 2 1 ^ encode_term_lam 0 3 ^ encode_term_pi 0 4
    ^ encode_term_let 0 1 5
  in
  let terms =
    match Ext_term.read_table names levels (Ext_bytes.of_string valid_term_table) with
    | Error error ->
        failwith
          ("valid term table: unexpected decode error "
         ^ Ext_bytes.reason_code error.Ext_bytes.reason)
    | Ok (terms, next) ->
        assert_int_equal "valid term table offset" (String.length valid_term_table)
          (Ext_bytes.offset next);
        assert_int_equal "valid term table length" 7 (List.length terms);
        terms
  in
  (match List.map term_value terms with
  | [
   Ext_term.Sort Ext_level.Zero;
   Ext_term.BVar 0;
   Ext_term.Const
     (Ext_term.Builtin { name; decl_interface_hash }, [ Ext_level.Zero; Ext_level.Param _ ]);
   Ext_term.App (_, _);
   Ext_term.Lam (_, _);
   Ext_term.Pi (_, _);
   Ext_term.Let (_, _, _);
  ] ->
      assert_equal "valid term const builtin name" "Nat" (Ext_name.to_string name);
      assert_int_equal "valid term const hash length" 32 (String.length decl_interface_hash)
  | _ -> failwith "valid term table did not decode into structured term AST");

  assert_decode_error "unknown level tag" "certificate_decode_error"
    (Ext_bytes.Unknown_tag 0xff) Ext_bytes.Level_table 1
    (Ext_level.read_table names (Ext_bytes.of_string (encode_uvar_int 1 ^ one_byte 0xff)));
  assert_decode_error "level table length exceeds payload" "certificate_decode_error"
    Ext_bytes.Unexpected_eof Ext_bytes.Level_table 1
    (Ext_level.read_table names (Ext_bytes.of_string (encode_uvar_int 2 ^ encode_level_zero)));
  assert_decode_error "dangling level self reference" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Level_table 1
    (Ext_level.read_table names (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_level_succ 0)));
  assert_decode_error "dangling level name reference" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Level_table 1
    (Ext_level.read_table [ universe_name ]
       (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_level_param 1)));
  assert_decode_error "non-normalized max zero" "noncanonical_encoding"
    Ext_bytes.Non_normalized_level Ext_bytes.Level_table 4
    (Ext_level.read_table [ universe_name ]
       (Ext_bytes.of_string
          (encode_uvar_int 3 ^ encode_level_zero ^ encode_level_param 0
         ^ encode_level_max 0 1)));
  assert_decode_error "duplicate level entry" "noncanonical_encoding"
    Ext_bytes.Noncanonical_order Ext_bytes.Level_table 2
    (Ext_level.read_table names
       (Ext_bytes.of_string (encode_uvar_int 2 ^ encode_level_zero ^ encode_level_zero)));
  let level_depth_entries =
    encode_level_zero
    ^ String.concat ""
        (List.init Ext_bytes.max_node_depth (fun index ->
             encode_level_succ index))
  in
  let level_depth_table =
    encode_uvar_int (Ext_bytes.max_node_depth + 1) ^ level_depth_entries
  in
  let last_level_offset =
    String.length level_depth_table
    - String.length (encode_level_succ (Ext_bytes.max_node_depth - 1))
  in
  assert_decode_error "level depth resource limit" "certificate_decode_error"
    Ext_bytes.Resource_limit Ext_bytes.Level_table last_level_offset
    (Ext_level.read_table names (Ext_bytes.of_string level_depth_table));
  assert_decode_error "unresolved universe metavariable" "certificate_decode_error"
    Ext_bytes.Unresolved_metavariable Ext_bytes.Level_table 1
    (Ext_level.read_table [ make_unchecked_name [ "z?meta" ] ]
       (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_level_param 0)));
  assert_decode_error "unresolved human universe metavariable" "certificate_decode_error"
    Ext_bytes.Unresolved_metavariable Ext_bytes.Level_table 1
    (Ext_level.read_table [ make_unchecked_name [ "__npa_internal_human_universe_meta#0" ] ]
       (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_level_param 0)));

  assert_decode_error "unknown term tag" "certificate_decode_error"
    (Ext_bytes.Unknown_tag 0xff) Ext_bytes.Term_table 1
    (Ext_term.read_table names levels (Ext_bytes.of_string (encode_uvar_int 1 ^ one_byte 0xff)));
  assert_decode_error "term table length exceeds payload" "certificate_decode_error"
    Ext_bytes.Unexpected_eof Ext_bytes.Term_table 1
    (Ext_term.read_table names levels
       (Ext_bytes.of_string (encode_uvar_int 2 ^ one_byte 0x01)));
  assert_decode_error "dangling term level reference" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Term_table 1
    (Ext_term.read_table names [] (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_term_sort 0)));
  assert_decode_error "dangling term self reference" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Term_table 1
    (Ext_term.read_table names levels
       (Ext_bytes.of_string (encode_uvar_int 1 ^ encode_term_app 0 0)));
  assert_decode_error "unknown global ref tag" "certificate_decode_error"
    (Ext_bytes.Unknown_tag 0xfe) Ext_bytes.Term_table 2
    (Ext_term.read_table names levels
       (Ext_bytes.of_string (encode_uvar_int 1 ^ one_byte 0x02 ^ one_byte 0xfe)));
  assert_decode_error "dangling global ref name" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Term_table 1
    (Ext_term.read_table names levels
       (Ext_bytes.of_string
          (encode_uvar_int 1 ^ encode_term_const (encode_global_builtin 9 (hash_bytes 0x01)) [])));
  assert_decode_error "duplicate term entry" "noncanonical_encoding"
    Ext_bytes.Non_normalized_term Ext_bytes.Term_table 3
    (Ext_term.read_table names levels
       (Ext_bytes.of_string (encode_uvar_int 2 ^ encode_term_sort 0 ^ encode_term_sort 0)))

let simple_level_table = [ { Ext_level.level = Ext_level.Zero; offset = 0 } ]

let simple_term_table = [ { Ext_term.term = Ext_term.Sort Ext_level.Zero; offset = 0 } ]

let encode_module ?(core_features = []) ?(axiom_report = encode_axiom_report [] [])
    ?(module_name = [ "M" ]) ?(imports = []) name_entries level_entries term_entries
    declarations export_entries =
  encode_header module_name ^ encode_imports imports ^ encode_name_table name_entries
  ^ encode_level_table level_entries ^ encode_term_table term_entries
  ^ encode_declarations declarations ^ encode_export_block export_entries ^ axiom_report
  ^ (if core_features = [] then "" else encode_core_features core_features)
  ^ encode_hashes

let encode_minimal_module ?(core_features = []) ?(axiom_report = encode_axiom_report [] [])
    declarations export_entries =
  encode_module ~core_features ~axiom_report [ [ "A" ] ] [ encode_level_zero ]
    [ encode_term_sort 0 ] declarations export_entries

let minimal_axiom_decl =
  encode_decl_cert (encode_axiom_decl_payload 0 [] 0) [] [] (hash_bytes 0x11) (hash_bytes 0x12)

let minimal_export_entry = encode_export_entry 0 0x00 [] 0 None []

let assert_decoded_minimal label decoded expected_feature_count =
  assert_equal (label ^ " module") "M"
    (Ext_name.to_string decoded.Ext_cert.header.Ext_cert.module_name);
  assert_int_equal (label ^ " imports") 0 (List.length decoded.Ext_cert.imports);
  assert_int_equal (label ^ " names") 1 (List.length decoded.Ext_cert.name_table);
  assert_int_equal (label ^ " levels") 1 (List.length decoded.Ext_cert.level_table);
  assert_int_equal (label ^ " terms") 1 (List.length decoded.Ext_cert.term_table);
  assert_int_equal (label ^ " declarations") 1
    (List.length decoded.Ext_cert.declaration_table);
  assert_int_equal (label ^ " exports") 1 (List.length decoded.Ext_cert.export_block);
  assert_int_equal (label ^ " axiom report mismatch preserved") 0
    (List.length decoded.Ext_cert.axiom_report.Ext_cert.per_declaration);
  assert_int_equal (label ^ " feature count") expected_feature_count
    (List.length decoded.Ext_cert.axiom_report.Ext_cert.core_features);
  assert_int_equal (label ^ " export hash length") 32
    (String.length decoded.Ext_cert.hashes.Ext_cert.export_hash);
  assert_int_equal (label ^ " axiom report hash length") 32
    (String.length decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash);
  assert_int_equal (label ^ " certificate hash length") 32
    (String.length decoded.Ext_cert.hashes.Ext_cert.certificate_hash)

let run_decoder_declarations_tests () =
  let golden_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let golden = read_binary_file golden_path in
  (match Ext_cert.read_module (Ext_bytes.of_string golden) with
  | Error error ->
      failwith
        ("golden module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)
  | Ok (decoded, next) ->
      assert_bool "golden module has declarations"
        (List.length decoded.Ext_cert.declaration_table > 0);
      assert_bool "golden module has exports" (List.length decoded.Ext_cert.export_block > 0);
      assert_int_equal "golden module offset" (String.length golden) (Ext_bytes.offset next));

  let minimal = encode_minimal_module [ minimal_axiom_decl ] [ minimal_export_entry ] in
  (match Ext_cert.read_module (Ext_bytes.of_string minimal) with
  | Error error ->
      failwith
        ("minimal module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (decoded, next) ->
      assert_decoded_minimal "minimal module" decoded 0;
      assert_int_equal "minimal module offset" (String.length minimal) (Ext_bytes.offset next));

  let feature_module =
    encode_minimal_module ~core_features:[ "unsupported_feature" ] [ minimal_axiom_decl ]
      [ minimal_export_entry ]
  in
  (match Ext_cert.read_module (Ext_bytes.of_string feature_module) with
  | Error error ->
      failwith
        ("feature module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (decoded, next) ->
      assert_decoded_minimal "feature module" decoded 1;
      assert_equal "feature name" "unsupported_feature"
        (List.hd decoded.Ext_cert.axiom_report.Ext_cert.core_features).Ext_feature.feature;
      assert_int_equal "feature module offset" (String.length feature_module)
        (Ext_bytes.offset next));

  let variant_names =
    List.map
      (fun name -> make_name [ name ])
      [ "A0"; "A1"; "D0"; "D1"; "T0"; "T1"; "I0"; "I1"; "M0"; "C"; "R" ]
  in
  let constraints = [ (0, 0x00, 0) ] in
  let constructor = [ (9, 0) ] in
  let recursor = Some (10, [], 0, 0, 0) in
  let variant_payloads =
    [
      encode_axiom_decl_payload 0 [] 0;
      encode_constrained_axiom_decl_payload 1 [] constraints 0;
      encode_def_decl_payload 0x01 2 [] 0 0 `Reducible;
      encode_def_decl_payload 0x11 3 [] ~constraints:(Some constraints) 0 0 `Opaque;
      encode_theorem_decl_payload 0x02 4 [] 0 0;
      encode_theorem_decl_payload 0x12 5 [] ~constraints:(Some constraints) 0 0;
      encode_inductive_decl_payload 0x03 6 [] [] [] 0 constructor recursor;
      encode_inductive_decl_payload 0x13 7 [] ~constraints:(Some constraints) [] [] 0
        constructor recursor;
      encode_mutual_inductive_block_payload 8 [] constraints
        [ encode_mutual_inductive_spec 6 [] [] 0 constructor recursor ];
    ]
  in
  let variant_declarations =
    encode_declarations
      (List.mapi
         (fun index payload ->
           encode_decl_cert payload [] [] (hash_bytes (0x60 + index)) (hash_bytes (0x70 + index)))
         variant_payloads)
  in
  (match
     Ext_cert.read_declarations 0 variant_names simple_level_table simple_term_table
       (Ext_bytes.of_string variant_declarations)
   with
  | Error error ->
      failwith
        ("variant declarations: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (declarations, next) ->
      assert_int_equal "variant declaration count" 9 (List.length declarations);
      assert_int_equal "variant declaration offset" (String.length variant_declarations)
        (Ext_bytes.offset next);
      assert_bool "variant declarations include mutual block"
        (List.exists
           (fun declaration -> declaration.Ext_cert.kind = Ext_cert.Mutual_inductive)
           declarations));

  let duplicate_declarations =
    encode_declarations [ minimal_axiom_decl; minimal_axiom_decl ]
  in
  assert_decode_error "duplicate declaration name" "noncanonical_encoding"
    Ext_bytes.Duplicate_declaration Ext_bytes.Declarations
    (String.length (encode_uvar_int 2 ^ minimal_axiom_decl))
    (Ext_cert.read_declarations 0 [ make_name [ "A" ] ] simple_level_table simple_term_table
       (Ext_bytes.of_string duplicate_declarations));

  let dangling_term_export =
    encode_uvar_int 1 ^ encode_uvar_int 0 ^ encode_export_kind 0x00 ^ encode_usize_vec []
    ^ encode_uvar_int 1
  in
  assert_decode_error "export dangling term" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Export_block 4
    (Ext_cert.read_export_block Ext_cert.Legacy 0
       (Array.of_list [ make_name [ "A" ] ])
       (Array.of_list simple_level_table)
       (Array.of_list simple_term_table) 1
       (Ext_bytes.of_string dangling_term_export));

  let export_prefix = encode_export_entry_prefix 0 0x00 [] 0 None in
  let axiom_ref_len = encode_uvar_int 1 in
  let dangling_decl_offset = String.length (encode_uvar_int 1 ^ export_prefix ^ axiom_ref_len) in
  let dangling_decl_export =
    encode_uvar_int 1 ^ export_prefix ^ axiom_ref_len ^ encode_global_local 99
    ^ encode_uvar_int 0 ^ hash_bytes 0x51
  in
  assert_decode_error "export dangling declaration" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Export_block dangling_decl_offset
    (Ext_cert.read_export_block Ext_cert.Legacy 0
       (Array.of_list [ make_name [ "A" ] ])
       (Array.of_list simple_level_table)
       (Array.of_list simple_term_table) 1
       (Ext_bytes.of_string dangling_decl_export))

let run_decoder_reachability_tests () =
  let golden_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let golden = read_binary_file golden_path in
  (match Ext_cert.read_module (Ext_bytes.of_string golden) with
  | Error error ->
      failwith
        ("reachability golden module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)
  | Ok (_, next) ->
      assert_int_equal "reachability golden offset" (String.length golden)
        (Ext_bytes.offset next));

  let minimal = encode_minimal_module [ minimal_axiom_decl ] [ minimal_export_entry ] in
  (match Ext_cert.read_module (Ext_bytes.of_string minimal) with
  | Error error ->
      failwith
        ("reachability minimal module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (_, next) ->
      assert_int_equal "reachability minimal offset" (String.length minimal)
        (Ext_bytes.offset next));

  let axiom_report_root =
    encode_module ~axiom_report:(encode_axiom_report [] [ (encode_global_local 0, 1, hash_bytes 0x44) ])
      [ [ "A" ]; [ "B" ] ] [ encode_level_zero ] [ encode_term_sort 0 ]
      [ minimal_axiom_decl ] [ minimal_export_entry ]
  in
  (match Ext_cert.read_module (Ext_bytes.of_string axiom_report_root) with
  | Error error ->
      failwith
        ("axiom report root module: unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason)
  | Ok (_, next) ->
      assert_int_equal "axiom report root offset" (String.length axiom_report_root)
        (Ext_bytes.offset next));

  let unused_name_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_uvar_int 2 ^ encode_name [ "A" ]
  in
  let unused_name =
    encode_module [ [ "A" ]; [ "Z" ] ] [ encode_level_zero ] [ encode_term_sort 0 ]
      [ minimal_axiom_decl ] [ minimal_export_entry ]
  in
  assert_decode_error "unused name table entry" "noncanonical_encoding"
    Ext_bytes.Unused_table_entry Ext_bytes.Name_table (String.length unused_name_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string unused_name));

  let reordered_name_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_uvar_int 2 ^ encode_name [ "Z" ]
  in
  let reordered_name_decl =
    encode_decl_cert (encode_axiom_decl_payload 1 [] 0) [] [] (hash_bytes 0x19) (hash_bytes 0x1a)
  in
  let reordered_name_export = encode_export_entry 1 0x00 [] 0 None [] in
  let reordered_name =
    encode_module [ [ "Z" ]; [ "A" ] ] [ encode_level_zero ] [ encode_term_sort 0 ]
      [ reordered_name_decl ] [ reordered_name_export ]
  in
  assert_decode_error "reordered name table" "noncanonical_encoding"
    Ext_bytes.Noncanonical_order Ext_bytes.Name_table (String.length reordered_name_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string reordered_name));
  (match Ext_cli.context_of_bytes reordered_name with
  | { Ext_cli.module_name = Some "M"; certificate_hash = Some hash } ->
      assert_equal "reordered name diagnostic certificate hash"
        ("sha256:" ^ hex_of_raw_hash (hash_bytes 0xa3)) hash
  | _ -> failwith "reordered name diagnostic context must preserve identity");

  let malformed_without_certificate_hash =
    encode_header [ "M" ] ^ String.make 10 '\255' ^ hash_bytes 0xb1
    ^ hash_bytes 0xb2
  in
  let malformed_certificate_hash =
    Ext_canonical.hash_with_domain
      (Ext_canonical.module_certificate_domain Ext_cert.Legacy)
      malformed_without_certificate_hash
  in
  let malformed_later_section =
    malformed_without_certificate_hash ^ malformed_certificate_hash
  in
  assert_decode_error "malformed later section" "certificate_decode_error"
    Ext_bytes.Uvar_overflow Ext_bytes.Imports
    (String.length (encode_header [ "M" ]) + 9)
    (Ext_cert.read_module (Ext_bytes.of_string malformed_later_section));
  (match Ext_cli.context_of_bytes malformed_later_section with
  | { Ext_cli.module_name = Some "M"; certificate_hash = Some hash } ->
      assert_equal "malformed later diagnostic certificate hash"
        (Ext_result.wire_hash malformed_certificate_hash) hash
  | _ -> failwith "malformed later diagnostic context must preserve identity");
  assert_bool "malformed later diagnostic hash must bind exact bytes"
    (Ext_cli.context_of_bytes
       (mutate_byte malformed_later_section
          (String.length malformed_later_section - 1))
    = Ext_cli.empty_context);

  let unused_level_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_name_table [ [ "A" ] ]
    ^ encode_uvar_int 2 ^ encode_level_zero
  in
  let unused_level =
    encode_module [ [ "A" ] ] [ encode_level_zero; encode_level_param 0 ] [ encode_term_sort 0 ]
      [ minimal_axiom_decl ] [ minimal_export_entry ]
  in
  assert_decode_error "unused level table entry" "noncanonical_encoding"
    Ext_bytes.Unused_table_entry Ext_bytes.Level_table (String.length unused_level_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string unused_level));

  let unused_term_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_name_table [ [ "A" ] ]
    ^ encode_level_table [ encode_level_zero ] ^ encode_uvar_int 2 ^ encode_term_sort 0
  in
  let unused_term =
    encode_module [ [ "A" ] ] [ encode_level_zero ] [ encode_term_sort 0; encode_term_bvar 0 ]
      [ minimal_axiom_decl ] [ minimal_export_entry ]
  in
  assert_decode_error "unused term table entry" "noncanonical_encoding"
    Ext_bytes.Unused_table_entry Ext_bytes.Term_table (String.length unused_term_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string unused_term));

  let reordered_level_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_name_table [ [ "A" ] ]
    ^ encode_uvar_int 2 ^ encode_level_param 0
  in
  let reordered_level_decl =
    encode_decl_cert (encode_axiom_decl_payload 0 [] 0) [] [] (hash_bytes 0x21) (hash_bytes 0x22)
  in
  let reordered_level_export = encode_export_entry 0 0x00 [] 0 None [] in
  let reordered_level =
    encode_module [ [ "A" ] ] [ encode_level_param 0; encode_level_zero ] [ encode_term_sort 1 ]
      [ reordered_level_decl ] [ reordered_level_export ]
  in
  assert_decode_error "reordered level table" "noncanonical_encoding"
    Ext_bytes.Noncanonical_order Ext_bytes.Level_table (String.length reordered_level_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string reordered_level));

  let reordered_term_prefix =
    encode_header [ "M" ] ^ encode_imports [] ^ encode_name_table [ [ "A" ] ]
    ^ encode_level_table [ encode_level_zero ] ^ encode_uvar_int 2 ^ encode_term_bvar 0
  in
  let reordered_term_decl =
    encode_decl_cert (encode_axiom_decl_payload 0 [] 1) [] [] (hash_bytes 0x23) (hash_bytes 0x24)
  in
  let reordered_term_export = encode_export_entry 0 0x00 [] 1 None [] in
  let reordered_term =
    encode_module [ [ "A" ] ] [ encode_level_zero ] [ encode_term_bvar 0; encode_term_sort 0 ]
      [ reordered_term_decl ] [ reordered_term_export ]
  in
  assert_decode_error "reordered term table" "noncanonical_encoding"
    Ext_bytes.Noncanonical_order Ext_bytes.Term_table (String.length reordered_term_prefix)
    (Ext_cert.read_module (Ext_bytes.of_string reordered_term));

  assert_decode_error "trailing bytes after hashes" "certificate_decode_error"
    Ext_bytes.Trailing_bytes Ext_bytes.Full_certificate (String.length minimal)
    (Ext_cert.read_module (Ext_bytes.of_string (minimal ^ "x")))

let encode_export_entry_full name_id kind_tag universe_params ty body type_hash body_hash
    reducibility opacity decl_interface_hash axiom_dependencies =
  encode_uvar_int name_id ^ encode_export_kind kind_tag ^ encode_usize_vec universe_params
  ^ encode_uvar_int ty ^ encode_option_usize body ^ type_hash ^ encode_option_hash body_hash
  ^ encode_option reducibility ^ encode_option opacity ^ decl_interface_hash
  ^ encode_axiom_refs axiom_dependencies

let first_declaration decoded =
  match decoded.Ext_cert.declaration_table with
  | declaration :: _ -> declaration
  | [] -> failwith "expected declaration fixture"

let assert_canonical_hash label expected_hex result =
  let hash = assert_ok label result in
  assert_equal label expected_hex (hex_of_raw_hash hash)

let assert_canonical_bytes label expected result =
  assert_equal label expected (assert_ok label result)

let assert_hash_hexes label expected result =
  let hashes = assert_ok label result in
  assert_int_equal (label ^ " length") (List.length expected) (List.length hashes);
  List.iteri
    (fun index expected_hex ->
      assert_equal
        (label ^ " " ^ string_of_int index)
        expected_hex
        (hex_of_raw_hash (List.nth hashes index)))
    expected;
  hashes

let located_names names =
  List.mapi (fun offset name -> { Ext_cert.name; offset }) names

let decode_level_table label names bytes =
  match Ext_level.read_table names (Ext_bytes.of_string bytes) with
  | Ok (levels, next) ->
      assert_int_equal (label ^ " offset") (String.length bytes) (Ext_bytes.offset next);
      levels
  | Error error ->
      failwith
        (label ^ ": unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)

let decode_term_table label names levels bytes =
  match Ext_term.read_table names levels (Ext_bytes.of_string bytes) with
  | Ok (terms, next) ->
      assert_int_equal (label ^ " offset") (String.length bytes) (Ext_bytes.offset next);
      terms
  | Error error ->
      failwith
        (label ^ ": unexpected decode error "
       ^ Ext_bytes.reason_code error.Ext_bytes.reason ^ " at "
       ^ Ext_bytes.section_name error.Ext_bytes.section ^ ":"
       ^ string_of_int error.Ext_bytes.offset)

let assert_export_term_hashes label decoded =
  let level_hashes =
    assert_ok (label ^ " level hashes") (Ext_canonical.level_hashes decoded.Ext_cert.level_table)
  in
  let term_hashes =
    assert_ok (label ^ " term hashes")
      (Ext_canonical.term_hashes decoded.Ext_cert.name_table decoded.Ext_cert.level_table
         level_hashes decoded.Ext_cert.term_table)
  in
  List.iteri
    (fun index export ->
      let prefix = label ^ " export " ^ string_of_int index in
      let type_hash =
        assert_ok (prefix ^ " type hash")
          (Ext_canonical.hash_for_term Ext_bytes.Export_block export.Ext_cert.export_offset
             decoded.Ext_cert.name_table decoded.Ext_cert.term_table term_hashes
             export.Ext_cert.export_ty)
      in
      assert_equal (prefix ^ " type hash")
        (hex_of_raw_hash export.Ext_cert.export_type_hash)
        (hex_of_raw_hash type_hash);
      match (export.Ext_cert.export_body, export.Ext_cert.export_body_hash) with
      | None, None -> ()
      | Some body, Some expected_body_hash ->
          let body_hash =
            assert_ok (prefix ^ " body hash")
              (Ext_canonical.hash_for_term Ext_bytes.Export_block export.Ext_cert.export_offset
                 decoded.Ext_cert.name_table decoded.Ext_cert.term_table term_hashes body)
          in
          assert_equal (prefix ^ " body hash") (hex_of_raw_hash expected_body_hash)
            (hex_of_raw_hash body_hash)
      | _ -> failwith (prefix ^ ": body and body_hash option mismatch"))
    decoded.Ext_cert.export_block

let assert_declaration_hashes label decoded =
  List.iteri
    (fun index declaration ->
      let prefix = label ^ " decl " ^ string_of_int index in
      let interface_payload =
        assert_ok (prefix ^ " interface payload")
          (Ext_canonical.declaration_interface_payload decoded.Ext_cert.name_table
             decoded.Ext_cert.level_table decoded.Ext_cert.term_table
             declaration.Ext_cert.payload declaration.Ext_cert.dependencies
             declaration.Ext_cert.axiom_dependencies)
      in
      let interface_hash =
        Ext_canonical.hash_with_domain Ext_canonical.domain_decl_interface interface_payload
      in
      assert_equal (prefix ^ " interface hash")
        (hex_of_raw_hash declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash)
        (hex_of_raw_hash interface_hash);
      let certificate_payload =
        assert_ok (prefix ^ " certificate payload")
          (Ext_canonical.declaration_certificate_payload decoded.Ext_cert.name_table
             decoded.Ext_cert.level_table decoded.Ext_cert.term_table declaration.Ext_cert.payload
             interface_hash declaration.Ext_cert.dependencies declaration.Ext_cert.axiom_dependencies)
      in
      let certificate_hash =
        Ext_canonical.hash_with_domain Ext_canonical.domain_decl_certificate certificate_payload
      in
      assert_equal (prefix ^ " certificate hash")
        (hex_of_raw_hash declaration.Ext_cert.hashes.Ext_cert.decl_certificate_hash)
        (hex_of_raw_hash certificate_hash))
    decoded.Ext_cert.declaration_table

let recompute_stored_declaration_hashes label decoded =
  let declaration_table =
    List.mapi
      (fun index declaration ->
        let prefix = label ^ " decl " ^ string_of_int index in
        let interface_hash, certificate_hash =
          assert_ok (prefix ^ " recomputed hashes")
            (Ext_canonical.declaration_hashes decoded.Ext_cert.name_table
               decoded.Ext_cert.level_table decoded.Ext_cert.term_table declaration)
        in
        let hashes =
          {
            declaration.Ext_cert.hashes with
            Ext_cert.decl_interface_hash = interface_hash;
            decl_certificate_hash = certificate_hash;
          }
        in
        { declaration with Ext_cert.hashes = hashes })
      decoded.Ext_cert.declaration_table
  in
  { decoded with Ext_cert.declaration_table }

let replace_first_declaration decoded update =
  match decoded.Ext_cert.declaration_table with
  | declaration :: rest ->
      { decoded with Ext_cert.declaration_table = update declaration :: rest }
  | [] -> failwith "expected declaration fixture"

let assert_declaration_hash_verifies label decoded =
  match
    assert_ok (label ^ " declaration hash check")
      (Ext_canonical.verify_declaration_hashes decoded)
  with
  | Ext_canonical.Declaration_hashes_ok -> ()
  | Ext_canonical.Declaration_hash_mismatch mismatch ->
      failwith
        (label ^ ": unexpected declaration hash mismatch at "
       ^ string_of_int mismatch.Ext_canonical.mismatch_offset)

let assert_declaration_hash_rejects label expected_kind expected_reason decoded =
  match
    assert_ok (label ^ " declaration hash check")
      (Ext_canonical.verify_declaration_hashes decoded)
  with
  | Ext_canonical.Declaration_hashes_ok -> failwith (label ^ ": expected hash mismatch")
  | Ext_canonical.Declaration_hash_mismatch mismatch ->
      let kind =
        Ext_canonical.declaration_hash_mismatch_kind_code
          mismatch.Ext_canonical.mismatch_kind
      in
      let reason =
        Ext_canonical.declaration_hash_role_reason_code
          mismatch.Ext_canonical.mismatch_role
      in
      let offset = mismatch.Ext_canonical.mismatch_offset in
      assert_equal (label ^ " kind") expected_kind kind;
      assert_equal (label ^ " reason") expected_reason reason;
      assert_bool (label ^ " expected differs from actual")
        (mismatch.Ext_canonical.expected_hash <> mismatch.Ext_canonical.actual_hash);
      let declaration =
        match
          List.nth_opt decoded.Ext_cert.declaration_table
            mismatch.Ext_canonical.mismatch_decl_index
        with
        | Some declaration -> declaration
        | None -> failwith (label ^ ": mismatch declaration index is invalid")
      in
      let expected_interface, expected_certificate =
        assert_ok (label ^ " recomputed mismatch hashes")
          (Ext_canonical.declaration_hashes decoded.Ext_cert.name_table
             decoded.Ext_cert.level_table decoded.Ext_cert.term_table declaration)
      in
      let expected_hash, actual_hash =
        match mismatch.Ext_canonical.mismatch_role with
        | Ext_canonical.Decl_interface_hash ->
            ( expected_interface,
              declaration.Ext_cert.hashes.Ext_cert.decl_interface_hash )
        | Ext_canonical.Decl_certificate_hash ->
            ( expected_certificate,
              declaration.Ext_cert.hashes.Ext_cert.decl_certificate_hash )
      in
      assert_equal (label ^ " exact expected hash") expected_hash
        mismatch.Ext_canonical.expected_hash;
      assert_equal (label ^ " exact actual hash") actual_hash
        mismatch.Ext_canonical.actual_hash;
      let raw =
        Ext_result.render_failed
          (Ext_result.checker_error ~reason_code:reason
             ~section:"declarations" ~offset
             ~expected_hash:(Ext_result.wire_hash expected_hash)
             ~actual_hash:(Ext_result.wire_hash actual_hash) kind)
      in
      assert_contains (label ^ " raw kind") ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ expected_reason ^ "\"")
        raw;
      assert_contains (label ^ " raw section") "\"section\": \"declarations\"" raw;
      assert_contains (label ^ " raw offset") ("\"offset\": " ^ string_of_int offset) raw;
      assert_contains (label ^ " raw expected hash")
        ("\"expected_hash\": \"" ^ Ext_result.wire_hash expected_hash ^ "\"")
        raw;
      assert_contains (label ^ " raw actual hash")
        ("\"actual_hash\": \"" ^ Ext_result.wire_hash actual_hash ^ "\"") raw

let assert_module_hash_verifies label bytes decoded =
  match
    assert_ok (label ^ " module hash check")
      (Ext_canonical.verify_module_hashes bytes decoded)
  with
  | Ext_canonical.Module_hashes_ok -> ()
  | Ext_canonical.Module_hash_mismatch mismatch ->
      failwith
        (label ^ ": unexpected module hash mismatch "
       ^ Ext_canonical.module_hash_role_kind_code
           mismatch.Ext_canonical.module_mismatch_role
       ^ " at "
       ^ string_of_int mismatch.Ext_canonical.module_mismatch_offset)

let assert_module_hash_rejects label expected_kind expected_offset bytes decoded =
  match
    assert_ok (label ^ " module hash check")
      (Ext_canonical.verify_module_hashes bytes decoded)
  with
  | Ext_canonical.Module_hashes_ok -> failwith (label ^ ": expected module hash mismatch")
  | Ext_canonical.Module_hash_mismatch mismatch ->
      let kind =
        Ext_canonical.module_hash_role_kind_code
          mismatch.Ext_canonical.module_mismatch_role
      in
      let offset = mismatch.Ext_canonical.module_mismatch_offset in
      assert_equal (label ^ " kind") expected_kind kind;
      assert_int_equal (label ^ " offset") expected_offset offset;
      assert_bool (label ^ " expected differs from actual")
        (mismatch.Ext_canonical.module_expected_hash
        <> mismatch.Ext_canonical.module_actual_hash);
      let expected_hash, actual_hash =
        match mismatch.Ext_canonical.module_mismatch_role with
        | Ext_canonical.Export_hash ->
            ( assert_ok (label ^ " recomputed expected export hash")
                (Ext_canonical.expected_export_hash decoded),
              decoded.Ext_cert.hashes.Ext_cert.export_hash )
        | Ext_canonical.Axiom_report_hash ->
            ( assert_ok (label ^ " recomputed expected axiom hash")
                (Ext_canonical.axiom_report_hash decoded),
              decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash )
        | Ext_canonical.Certificate_hash ->
            ( assert_ok (label ^ " recomputed expected certificate hash")
                (Ext_canonical.certificate_hash bytes decoded),
              decoded.Ext_cert.hashes.Ext_cert.certificate_hash )
      in
      assert_equal (label ^ " exact expected hash") expected_hash
        mismatch.Ext_canonical.module_expected_hash;
      assert_equal (label ^ " exact actual hash") actual_hash
        mismatch.Ext_canonical.module_actual_hash;
      let raw =
        Ext_result.render_failed
          (Ext_result.checker_error ~reason_code:kind ~section:"hashes" ~offset
             ~expected_hash:(Ext_result.wire_hash expected_hash)
             ~actual_hash:(Ext_result.wire_hash actual_hash) kind)
      in
      assert_contains (label ^ " raw kind") ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ expected_kind ^ "\"")
        raw;
      assert_contains (label ^ " raw section") "\"section\": \"hashes\"" raw;
      assert_contains (label ^ " raw offset") ("\"offset\": " ^ string_of_int offset) raw;
      assert_contains (label ^ " raw expected hash")
        ("\"expected_hash\": \"" ^ Ext_result.wire_hash expected_hash ^ "\"")
        raw;
      assert_contains (label ^ " raw actual hash")
        ("\"actual_hash\": \"" ^ Ext_result.wire_hash actual_hash ^ "\"") raw

let import_store_load_error_code error =
  match error with
  | Ext_import_store.Import_dir_unavailable -> "import_dir_unavailable"
  | Ext_import_store.Source_or_replay_input_rejected -> "source_or_replay_input_rejected"
  | Ext_import_store.Certificate_decode_error decode_error ->
      "certificate_decode_error:" ^ Ext_bytes.reason_code decode_error.Ext_bytes.reason
  | Ext_import_store.Certificate_hash_mismatch mismatch ->
      "certificate_hash_mismatch:" ^ mismatch.Ext_import_store.hash_mismatch_kind
  | Ext_import_store.Duplicate_import_binding _ -> "duplicate_import_binding"

let assert_import_store_ok label result =
  match result with
  | Ok value -> value
  | Error error ->
      failwith (label ^ ": unexpected import store error " ^ import_store_load_error_code error)

let assert_import_store_load_error label expected result =
  match result with
  | Ok _ -> failwith (label ^ ": expected import store error")
  | Error error -> assert_equal (label ^ " load error") expected (import_store_load_error_code error)

let assert_import_resolves label store request =
  match Ext_import_store.resolve_normal store request with
  | Ok value -> value
  | Error error ->
      failwith
        (label ^ ": unexpected import resolution error "
       ^ Ext_import_store.resolve_error_reason_code error.Ext_import_store.resolve_reason)

let assert_import_resolve_rejects label expected_kind expected_reason expected_offset store
    request =
  match Ext_import_store.resolve_normal ~offset:expected_offset store request with
  | Ok _ -> failwith (label ^ ": expected import resolution error")
  | Error error ->
      let kind = Ext_import_store.resolve_error_kind error in
      let reason =
        Ext_import_store.resolve_error_reason_code error.Ext_import_store.resolve_reason
      in
      assert_equal (label ^ " kind") expected_kind kind;
      assert_equal (label ^ " reason") expected_reason reason;
      assert_int_equal (label ^ " offset") expected_offset
        error.Ext_import_store.resolve_offset;
      let raw =
        Ext_result.import_failure ~kind ~reason_code:reason ~section:"imports"
          ~offset:expected_offset
      in
      assert_contains (label ^ " raw kind") ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ expected_reason ^ "\"")
        raw;
      assert_contains (label ^ " raw section") "\"section\": \"imports\"" raw;
      assert_contains (label ^ " raw offset") ("\"offset\": " ^ string_of_int expected_offset) raw

let assert_import_environment_ok ?(policy = Ext_import_store.normal_policy) label store
    decoded =
  match Ext_import_store.build_import_environment ~policy store decoded with
  | Ok value -> value
  | Error error ->
      failwith
        (label ^ ": unexpected import environment error "
       ^ Ext_import_store.resolve_error_reason_code error.Ext_import_store.resolve_reason)

let assert_import_environment_rejects ?(policy = Ext_import_store.normal_policy) label
    expected_kind expected_reason store decoded =
  match Ext_import_store.build_import_environment ~policy store decoded with
  | Ok _ -> failwith (label ^ ": expected import environment error")
  | Error error ->
      let kind = Ext_import_store.resolve_error_kind error in
      let reason =
        Ext_import_store.resolve_error_reason_code error.Ext_import_store.resolve_reason
      in
      assert_equal (label ^ " kind") expected_kind kind;
      assert_equal (label ^ " reason") expected_reason reason;
      let raw =
        Ext_result.import_failure ~kind ~reason_code:reason ~section:"imports"
          ~offset:error.Ext_import_store.resolve_offset
      in
      assert_contains (label ^ " raw kind") ("\"kind\": \"" ^ expected_kind ^ "\"") raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ expected_reason ^ "\"")
        raw;
      assert_contains (label ^ " raw section") "\"section\": \"imports\"" raw;
      assert_contains (label ^ " raw offset")
        ("\"offset\": " ^ string_of_int error.Ext_import_store.resolve_offset)
        raw

let assert_env_resolves label env global_ref =
  match Ext_env.resolve_global_ref env global_ref with
  | Ok signature -> signature
  | Error error ->
      failwith
        (label ^ ": unexpected env error "
       ^ Ext_env.error_reason_code error.Ext_env.reason)

let assert_env_rejects label expected_kind expected_reason env global_ref =
  match Ext_env.resolve_global_ref env global_ref with
  | Ok _ -> failwith (label ^ ": expected env error")
  | Error error ->
      assert_equal (label ^ " kind") expected_kind (Ext_env.error_kind error);
      assert_equal (label ^ " reason") expected_reason
        (Ext_env.error_reason_code error.Ext_env.reason);
      assert_equal (label ^ " section") "declarations"
        (Ext_bytes.section_name error.Ext_env.section)

let assert_typecheck_ok label result =
  match result with
  | Ok () -> ()
  | Error error ->
      failwith
        (label ^ ": unexpected typecheck error "
       ^ Ext_typecheck.error_reason_code error.Ext_typecheck.reason)

let assert_declaration_check_ok label result =
  match result with
  | Ok env -> env
  | Error error ->
      failwith
        (label ^ ": unexpected declaration check error "
       ^ Ext_typecheck.error_reason_code error.Ext_typecheck.reason)

let assert_typecheck_rejects label expected_kind expected_reason result =
  match result with
  | Ok _ -> failwith (label ^ ": expected typecheck error")
  | Error error ->
      assert_equal (label ^ " kind") expected_kind (Ext_typecheck.error_kind error);
      assert_equal (label ^ " reason") expected_reason
        (Ext_typecheck.error_reason_code error.Ext_typecheck.reason);
      assert_equal (label ^ " section") "declarations"
        (Ext_bytes.section_name error.Ext_typecheck.section)

let assert_infers_term label expected result =
  match result with
  | Ok actual ->
      if actual <> expected then failwith (label ^ ": inferred unexpected term")
  | Error error ->
      failwith
        (label ^ ": unexpected typecheck error "
       ^ Ext_typecheck.error_reason_code error.Ext_typecheck.reason)

let assert_term_result label expected result =
  match result with
  | Ok actual ->
      if actual <> expected then failwith (label ^ ": unexpected term result")
  | Error error ->
      failwith
        (label ^ ": unexpected typecheck error "
       ^ Ext_typecheck.error_reason_code error.Ext_typecheck.reason)

let assert_defeq label expected result =
  match result with
  | Ok actual ->
      assert_equal (label ^ " result") (string_of_bool expected)
        (string_of_bool actual)
  | Error error ->
      failwith
        (label ^ ": unexpected typecheck error "
       ^ Ext_typecheck.error_reason_code error.Ext_typecheck.reason)

let theorem_payload_with_type payload decl_ty =
  match payload with
  | Ext_cert.TheoremDecl
      { decl_name; decl_universe_params; decl_universe_constraints; decl_proof; decl_opacity; _ }
    ->
      Ext_cert.TheoremDecl
        {
          decl_name;
          decl_universe_params;
          decl_universe_constraints;
          decl_ty;
          decl_proof;
          decl_opacity;
        }
  | _ -> failwith "expected theorem declaration"

let theorem_payload_with_proof payload decl_proof =
  match payload with
  | Ext_cert.TheoremDecl
      { decl_name; decl_universe_params; decl_universe_constraints; decl_ty; decl_opacity; _ }
    ->
      Ext_cert.TheoremDecl
        {
          decl_name;
          decl_universe_params;
          decl_universe_constraints;
          decl_ty;
          decl_proof;
          decl_opacity;
        }
  | _ -> failwith "expected theorem declaration"

let mutate_first_dependency_hash declaration hash =
  match declaration.Ext_cert.dependencies with
  | dependency :: rest ->
      let dependency =
        { dependency with Ext_cert.dependency_decl_interface_hash = hash }
      in
      { declaration with Ext_cert.dependencies = dependency :: rest }
  | [] -> failwith "expected dependency fixture"

let mutate_first_axiom_dependency_hash declaration hash =
  match declaration.Ext_cert.axiom_dependencies with
  | axiom :: rest ->
      let axiom = { axiom with Ext_cert.axiom_decl_interface_hash = hash } in
      { declaration with Ext_cert.axiom_dependencies = axiom :: rest }
  | [] -> failwith "expected axiom dependency fixture"

let run_hash_level_term_tests () =
  let names = [ make_name [ "u" ]; make_name [ "Imported" ] ] in
  let name_table = located_names names in
  let level_bytes =
    encode_uvar_int 4 ^ encode_level_param 0 ^ encode_level_succ 0
    ^ encode_level_max 1 0 ^ encode_level_imax 0 0
  in
  let level_table = decode_level_table "hash level table" names level_bytes in
  let level_hashes =
    assert_hash_hexes "level hash"
      [
        "14ca4d271ed543507887e0ea523cefe7767b12c4c88c64db7797af8e5d60edca";
        "3c4dc3d2830d5c7b16bf22a38bbdc0867936d8e0faa2cdfb909fbfb314e0b9ef";
        "5ca42f83e7ab0f56fa5d53b157a5816bba36dfe71ca83d228b790dd7f52f667e";
        "b7dff10a5ac7d0c3c25ec2f2007b12015444606e970292c103dd2239df70cc48";
      ]
      (Ext_canonical.level_hashes level_table)
  in

  let imported_ref = encode_global_imported 0 1 (hash_bytes 0x55) in
  let term_bytes =
    encode_uvar_int 8 ^ encode_term_sort 0 ^ encode_term_sort 1 ^ encode_term_bvar 0
    ^ encode_term_const imported_ref [ 0; 1 ]
    ^ encode_term_app 3 2 ^ encode_term_lam 0 4 ^ encode_term_pi 0 5
    ^ encode_term_let 0 2 6
  in
  let term_table = decode_term_table "hash term table" names level_table term_bytes in
  let term_hashes =
    assert_hash_hexes "term hash"
      [
        "4dbd7b9567ca2c9a3014d70c03e2213e85686af92f3aa86ee57a1003de1c48d5";
        "d4c881c652406552c33e9f7e374c0eed412f711733a4657b978d052262f19406";
        "7f20eac79de1e58183de939cbf75e45bc92e8c8a1ac0b7c8e4fca287d201fcb7";
        "f6aac19b5b3fbe1c698ebc7b02acd3f32d7d287fe06ad7108191d5d6cfe09c42";
        "aa45ed6b3051ec6dd79b578d048c64711404e1434d39082d8874ad1777db8ea9";
        "8079e8d16fa1f32538052afd5379b3107399c2964d6e43aad7082ad938b8c670";
        "37adbeb21882f9c57f6c6f952715b9e75e8a30e53ab88269d20ec40976b3300e";
        "9dde1d65cb02d6d632083bd28394894abb0c42b55285190f4e1d4b648433ac46";
      ]
      (Ext_canonical.term_hashes name_table level_table level_hashes term_table)
  in

  let mutated_level_table =
    decode_level_table "mutated level table" names
      (encode_uvar_int 2 ^ encode_level_zero ^ encode_level_succ 0)
  in
  let mutated_level_hashes =
    assert_ok "mutated level hashes"
      (Ext_canonical.level_hashes mutated_level_table)
  in
  assert_bool "mutating referenced level changes dependent level hash"
    (List.nth level_hashes 1 <> List.nth mutated_level_hashes 1);
  let mutated_term_table =
    decode_term_table "mutated term table" names level_table
      (encode_uvar_int 5 ^ encode_term_sort 0 ^ encode_term_sort 1
      ^ encode_term_bvar 1 ^ encode_term_const imported_ref [ 0; 1 ]
      ^ encode_term_app 3 2)
  in
  let mutated_term_hashes =
    assert_ok "mutated term hashes"
      (Ext_canonical.term_hashes name_table level_table level_hashes mutated_term_table)
  in
  assert_bool "mutating referenced term changes dependent term hash"
    (List.nth term_hashes 4 <> List.nth mutated_term_hashes 4);

  let dangling_level_table = [ { Ext_level.level = Ext_level.Succ Ext_level.Zero; offset = 7 } ] in
  assert_decode_error "level hash dangling child" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Level_table 7
    (Ext_canonical.level_hashes dangling_level_table);
  let dangling_term_table =
    [ { Ext_term.term = Ext_term.App (Ext_term.BVar 0, Ext_term.BVar 0); offset = 9 } ]
  in
  assert_decode_error "term hash dangling child" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Term_table 9
    (Ext_canonical.term_hashes [] [] [] dangling_term_table);
  let missing_level_term_table =
    [ { Ext_term.term = Ext_term.Sort Ext_level.Zero; offset = 11 } ]
  in
  assert_decode_error "term hash dangling level" "certificate_decode_error"
    Ext_bytes.Dangling_reference Ext_bytes.Term_table 11
    (Ext_canonical.term_hashes [] [] [] missing_level_term_table);

  let assert_golden_export_terms label path =
    let decoded =
      decode_module_bytes (label ^ " hash level-term golden") (read_binary_file path)
    in
    assert_export_term_hashes label decoded
  in
  assert_golden_export_terms "nat"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert");
  assert_golden_export_terms "eq"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Logic/Eq/certificate.npcert")

let run_hash_declarations_tests () =
  let assert_golden_declarations label path =
    let decoded =
      decode_module_bytes (label ^ " declaration hash golden") (read_binary_file path)
    in
    assert_declaration_hash_verifies label decoded
  in
  assert_golden_declarations "nat"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert");
  assert_golden_declarations "eq"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Logic/Eq/certificate.npcert");

  let simple_theorem_decl =
    encode_decl_cert (encode_theorem_decl_payload 0x02 0 [] 0 1) [] []
      (hash_bytes 0x41) (hash_bytes 0x42)
  in
  let simple_theorem_export =
    encode_export_entry_full 0 0x02 [] 0 None (hash_bytes 0x31) None None
      (Some encode_opacity_opaque) (hash_bytes 0x32) []
  in
  let simple_theorem_module =
    encode_module [ [ "A" ] ] [ encode_level_zero ]
      [ encode_term_sort 0; encode_term_bvar 0 ]
      [ simple_theorem_decl ] [ simple_theorem_export ]
  in
  let simple_theorem =
    recompute_stored_declaration_hashes "simple theorem declaration hashes"
      (decode_module_bytes "simple theorem declaration hashes" simple_theorem_module)
  in
  assert_declaration_hash_verifies "simple theorem valid declaration hashes"
    simple_theorem;
  let mutated_type =
    replace_first_declaration simple_theorem (fun declaration ->
        {
          declaration with
          Ext_cert.payload =
            theorem_payload_with_type declaration.Ext_cert.payload (Ext_term.BVar 0);
        })
  in
  assert_declaration_hash_rejects "mutated declaration type"
    "declaration_hash_mismatch" "decl_interface_hash_mismatch" mutated_type;
  let mutated_body =
    replace_first_declaration simple_theorem (fun declaration ->
        {
          declaration with
          Ext_cert.payload =
            theorem_payload_with_proof declaration.Ext_cert.payload
              Ext_term.(Sort Ext_level.Zero);
        })
  in
  assert_declaration_hash_rejects "mutated declaration body"
    "declaration_hash_mismatch" "decl_certificate_hash_mismatch" mutated_body;

  let imported_ref = encode_global_imported 0 1 (hash_bytes 0x55) in
  let dependency_theorem_decl =
    encode_decl_cert
      (encode_theorem_decl_payload 0x02 0 [] 0 1)
      [ (imported_ref, hash_bytes 0x55) ] [] (hash_bytes 0x51) (hash_bytes 0x52)
  in
  let dependency_theorem_export =
    encode_export_entry_full 0 0x02 [] 0 None (hash_bytes 0x31) None None
      (Some encode_opacity_opaque) (hash_bytes 0x32) []
  in
  let dependency_module =
    encode_module ~imports:[ ([ "Dep" ], hash_bytes 0x71, None) ]
      [ [ "A" ]; [ "Imported" ] ] [ encode_level_zero ]
      [ encode_term_sort 0; encode_term_const imported_ref [] ]
      [ dependency_theorem_decl ] [ dependency_theorem_export ]
  in
  let dependency_theorem =
    recompute_stored_declaration_hashes "dependency declaration hashes"
      (decode_module_bytes "dependency declaration hashes" dependency_module)
  in
  assert_declaration_hash_verifies "dependency valid declaration hashes"
    dependency_theorem;
  let mutated_dependency =
    replace_first_declaration dependency_theorem (fun declaration ->
        mutate_first_dependency_hash declaration (hash_bytes 0x56))
  in
  assert_declaration_hash_rejects "mutated declaration dependency"
    "dependency_hash_mismatch" "decl_certificate_hash_mismatch" mutated_dependency;

  let axiom_dependency_ref = encode_global_imported 0 1 (hash_bytes 0x44) in
  let axiom_dependency_decl =
    encode_decl_cert (encode_axiom_decl_payload 0 [] 0) []
      [ (axiom_dependency_ref, 1, hash_bytes 0x44) ] (hash_bytes 0x61)
      (hash_bytes 0x62)
  in
  let axiom_dependency_export =
    encode_export_entry_full 0 0x00 [] 0 None (hash_bytes 0x31) None None None
      (hash_bytes 0x32) []
  in
  let axiom_dependency_module =
    encode_module ~imports:[ ([ "Dep" ], hash_bytes 0x71, None) ]
      [ [ "A" ]; [ "Imported" ] ] [ encode_level_zero ] [ encode_term_sort 0 ]
      [ axiom_dependency_decl ] [ axiom_dependency_export ]
  in
  let axiom_dependency =
    recompute_stored_declaration_hashes "axiom dependency declaration hashes"
      (decode_module_bytes "axiom dependency declaration hashes" axiom_dependency_module)
  in
  assert_declaration_hash_verifies "axiom dependency valid declaration hashes"
    axiom_dependency;
  let mutated_axiom_dependency =
    replace_first_declaration axiom_dependency (fun declaration ->
        mutate_first_axiom_dependency_hash declaration (hash_bytes 0x45))
  in
  assert_declaration_hash_rejects "mutated declaration axiom dependency"
    "dependency_hash_mismatch" "decl_certificate_hash_mismatch"
    mutated_axiom_dependency

let run_hash_module_tests () =
  let golden_paths =
    [
      ( "nat",
        Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
      );
      ( "eq",
        Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Logic/Eq/certificate.npcert"
      );
    ]
  in
  let decoded_golden label path =
    let bytes = read_binary_file path in
    (bytes, decode_module_bytes (label ^ " module hash golden") bytes)
  in
  List.iter
    (fun (label, path) ->
      let bytes, decoded = decoded_golden label path in
      assert_module_hash_verifies (label ^ " valid module hashes") bytes decoded)
    golden_paths;

  let bytes, decoded = decoded_golden "nat mutation corpus" (List.assoc "nat" golden_paths) in
  let hashes = decoded.Ext_cert.hashes in
  let assert_mutated_hash label expected_kind offset =
    let mutated = mutate_byte bytes offset in
    let decoded_mutated =
      decode_module_bytes (label ^ " mutated module hash") mutated
    in
    assert_module_hash_rejects label expected_kind offset mutated decoded_mutated
  in
  assert_mutated_hash "mutated export hash" "export_hash_mismatch"
    hashes.Ext_cert.export_hash_offset;
  assert_mutated_hash "mutated axiom report hash" "axiom_report_mismatch"
    hashes.Ext_cert.axiom_report_hash_offset;
  assert_mutated_hash "mutated certificate hash" "certificate_hash_mismatch"
    hashes.Ext_cert.certificate_hash_offset;

  let prefix_mutated = mutate_byte bytes 0 in
  assert_module_hash_rejects "module certificate hash uses exact input prefix"
    "certificate_hash_mismatch" hashes.Ext_cert.certificate_hash_offset prefix_mutated
    decoded;

  let mutated_export_block =
    match decoded.Ext_cert.export_block with
    | export :: rest ->
        {
          export with
          Ext_cert.export_type_hash = mutate_byte export.Ext_cert.export_type_hash 0;
        }
        :: rest
    | [] -> failwith "expected golden export block"
  in
  let decoded_with_stored_export_block = { decoded with Ext_cert.export_block = mutated_export_block } in
  let forged_export_hash =
    assert_ok "stored export block hash"
      (Ext_canonical.export_hash decoded_with_stored_export_block)
  in
  let forged_hashes =
    { decoded.Ext_cert.hashes with Ext_cert.export_hash = forged_export_hash }
  in
  let decoded_with_forged_export_hash =
    { decoded_with_stored_export_block with Ext_cert.hashes = forged_hashes }
  in
  assert_module_hash_rejects
    "module hash verifier rebuilds expected export block from declarations"
    "export_hash_mismatch" hashes.Ext_cert.export_hash_offset bytes
    decoded_with_forged_export_hash

let run_import_store_tests () =
  let nat_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let nat_dir = Filename.dirname nat_path in
  let nat_store =
    assert_import_store_ok "nat import dir" (Ext_import_store.load_import_dir nat_dir)
  in
  assert_int_equal "nat import store entry count" 1
    (List.length (Ext_import_store.entries nat_store));
  let nat_module =
    match Ext_import_store.entries nat_store with
    | [ entry ] -> entry
    | _ -> failwith "expected one nat import entry"
  in
  assert_equal "nat import module name" "Std.Nat.Basic"
    (Ext_name.to_string nat_module.Ext_import_store.import_entry.Ext_import.module_name);
  assert_bool "nat import exposes public exports"
    (List.length
       nat_module.Ext_import_store.public_environment.Ext_import_store.public_exports
    > 0);
  assert_bool "import store source certificates are not high-trust checked"
    (not nat_module.Ext_import_store.checked_by_ext_checker);

  let request_without_certificate_hash =
    {
      Ext_import.module_name =
        nat_module.Ext_import_store.import_entry.Ext_import.module_name;
      export_hash = nat_module.Ext_import_store.import_entry.Ext_import.export_hash;
      certificate_hash = None;
    }
  in
  ignore
    (assert_import_resolves "normal import resolves by module and export hash"
       nat_store request_without_certificate_hash);
  let request_with_certificate_hash =
    {
      request_without_certificate_hash with
      Ext_import.certificate_hash =
        nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash;
    }
  in
  ignore
    (assert_import_resolves "normal import resolves with matching certificate hash"
       nat_store request_with_certificate_hash);
  assert_import_resolve_rejects "missing import store entry" "import_not_found"
    "missing_import" 17 Ext_import_store.empty request_without_certificate_hash;
  let wrong_export_request =
    {
      request_without_certificate_hash with
      Ext_import.export_hash = mutate_byte request_without_certificate_hash.Ext_import.export_hash 0;
    }
  in
  assert_import_resolve_rejects "normal import rejects export hash mismatch"
    "import_hash_mismatch" "import_export_hash_mismatch" 23 nat_store
    wrong_export_request;
  let wrong_certificate_request =
    {
      request_without_certificate_hash with
      Ext_import.certificate_hash =
        Option.map
          (fun hash -> mutate_byte hash 0)
          nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash;
    }
  in
  assert_import_resolve_rejects "normal import rejects certificate hash mismatch"
    "import_hash_mismatch" "import_certificate_hash_mismatch" 29 nat_store
    wrong_certificate_request;

  let nat_bytes = read_binary_file nat_path in
  assert_import_store_load_error "bounded certificate read enforces aggregate remainder"
    "certificate_decode_error:resource_limit"
    (Ext_import_store.read_binary_file_with_limit nat_path
       (String.length nat_bytes - 1));
  let aggregate_dir = Filename.temp_file "npa-checker-ext-aggregate" ".dir" in
  Sys.remove aggregate_dir;
  Unix.mkdir aggregate_dir 0o700;
  let aggregate_dir = Unix.realpath aggregate_dir in
  let first_candidate = Filename.concat aggregate_dir "first.npcert" in
  let second_candidate = Filename.concat aggregate_dir "second.npcert" in
  let write_candidate path =
    let channel = open_out_bin path in
    output_string channel nat_bytes;
    close_out channel
  in
  write_candidate first_candidate;
  write_candidate second_candidate;
  let aggregate_bytes = 2 * String.length nat_bytes in
  (match
     Ext_session.load_candidates_with_budget
       ~max_candidate_bytes:aggregate_bytes aggregate_dir
   with
  | Ok candidates ->
      assert_int_equal "aggregate candidate byte budget accepts exact total" 2
        (List.length candidates)
  | Error _ -> failwith "exact aggregate candidate byte budget must accept");
  (match
     Ext_session.load_candidates_with_budget
       ~max_candidate_bytes:(aggregate_bytes - 1) aggregate_dir
   with
  | Error
      (Ext_session.Load_error
        (Ext_import_store.Certificate_decode_error error)) ->
      assert_equal "aggregate candidate byte budget reason" "resource_limit"
        (Ext_bytes.reason_code error.Ext_bytes.reason);
      assert_int_equal "aggregate candidate byte budget remaining offset"
        (String.length nat_bytes - 1) error.Ext_bytes.offset
  | Ok _ -> failwith "aggregate candidate byte budget must reject combined size"
  | Error _ -> failwith "aggregate candidate byte budget returned wrong error");
  Sys.remove first_candidate;
  Sys.remove second_candidate;
  Unix.rmdir aggregate_dir;
  assert_import_store_load_error "duplicate module export binding rejects"
    "duplicate_import_binding"
    (Ext_import_store.from_source_free_certificates [ nat_bytes; nat_bytes ]);
  let decoded_nat = decode_module_bytes "import store hash mutation fixture" nat_bytes in
  let mutated_import_hash =
    mutate_byte nat_bytes decoded_nat.Ext_cert.hashes.Ext_cert.export_hash_offset
  in
  assert_import_store_load_error "import cert hash verification runs before exposure"
    "certificate_hash_mismatch:export_hash_mismatch"
    (Ext_import_store.from_source_free_certificates [ mutated_import_hash ]);

  let source_replay_fixture =
    Filename.concat (root_dir ()) "test/fixtures/import_store"
  in
  let ignored_store =
    assert_import_store_ok "source and replay files are ignored"
      (Ext_import_store.load_import_dir source_replay_fixture)
  in
  assert_int_equal "source and replay fixtures are not read" 0
    (List.length (Ext_import_store.entries ignored_store));
  assert_import_store_load_error "source import dir path is rejected"
    "source_or_replay_input_rejected"
    (Ext_import_store.load_import_dir
       (Filename.concat source_replay_fixture "ignored.npa"));
  assert_bool "replay prefix is not an exact replay component"
    (not
       (Ext_import_store.is_source_or_replay_path
          (Filename.concat source_replay_fixture "replay.json.backup")));
  let symlink_target = Filename.temp_file "npa-checker-ext-source" ".npa" in
  let symlink_path = symlink_target ^ ".link.npcert" in
  Unix.symlink symlink_target symlink_path;
  assert_import_store_load_error "symbolic-link certificate is not followed"
    "source_or_replay_input_rejected"
    (Ext_import_store.read_binary_file symlink_path);
  Sys.remove symlink_path;
  Sys.remove symlink_target

let decoded_import_request label module_name export_hash certificate_hash =
  decode_module_bytes label
    (encode_module ~module_name:[ "Use"; "Import" ]
       ~imports:[ (Ext_name.components module_name, export_hash, certificate_hash) ]
       [] [] [] [] [])

let decoded_import_requests label imports =
  decode_module_bytes label
    (encode_module ~module_name:[ "Use"; "Import" ]
       ~imports:
         (List.map
            (fun (module_name, export_hash, certificate_hash) ->
              (Ext_name.components module_name, export_hash, certificate_hash))
            imports)
       [] [] [] [] [])

let single_import_offset label decoded =
  match decoded.Ext_cert.imports with
  | [ import ] -> import.Ext_cert.import_offset
  | _ -> failwith (label ^ ": expected one import request")

let single_resolved_import label environment =
  match Ext_import_store.import_environment_imports environment with
  | [ import ] -> import
  | _ -> failwith (label ^ ": expected one resolved import")

let load_single_import_entry label path =
  let store =
    assert_import_store_ok label
      (Ext_import_store.from_source_free_certificates [ read_binary_file path ])
  in
  match Ext_import_store.entries store with
  | [ entry ] -> entry
  | _ -> failwith (label ^ ": expected one import entry")

let run_import_normal_tests () =
  let nat_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let nat_store =
    assert_import_store_ok "normal nat import dir"
      (Ext_import_store.load_import_dir (Filename.dirname nat_path))
  in
  let nat_module =
    match Ext_import_store.entries nat_store with
    | [ entry ] -> entry
    | _ -> failwith "expected one nat import entry"
  in
  let nat_request =
    decoded_import_request "normal import request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  let nat_environment =
    assert_import_environment_ok "normal import environment resolves" nat_store
      nat_request
  in
  let nat_import = single_resolved_import "normal nat import" nat_environment in
  assert_equal "normal import resolved module" "Std.Nat.Basic"
    (Ext_name.to_string nat_import.Ext_import_store.resolved_module_name);
  assert_equal "normal import resolved export hash"
    nat_module.Ext_import_store.import_entry.Ext_import.export_hash
    nat_import.Ext_import_store.resolved_export_hash;
  assert_bool "normal import carries certificate hash"
    (nat_import.Ext_import_store.resolved_certificate_hash
    = nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash);
  assert_bool "normal import copies public exports"
    (List.length
       nat_import.Ext_import_store.resolved_public_environment.Ext_import_store.public_exports
    > 0);
  assert_int_equal "normal import flattened exports"
    (List.length
       nat_import.Ext_import_store.resolved_public_environment.Ext_import_store.public_exports)
    (List.length (Ext_import_store.import_environment_public_exports nat_environment));

  let wrong_export_request =
    decoded_import_request "normal wrong export request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      (mutate_byte nat_module.Ext_import_store.import_entry.Ext_import.export_hash 0)
      None
  in
  assert_import_environment_rejects
    "normal import environment rejects name-only match"
    "import_hash_mismatch" "import_export_hash_mismatch" nat_store
    wrong_export_request;
  let missing_request =
    decoded_import_request "normal missing request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  assert_import_environment_rejects "normal import environment missing import"
    "import_not_found" "missing_import" Ext_import_store.empty missing_request;
  assert_int_equal "normal missing import offset comes from certificate"
    (single_import_offset "missing request" missing_request)
    (match Ext_import_store.build_import_environment Ext_import_store.empty missing_request with
    | Error error -> error.Ext_import_store.resolve_offset
    | Ok _ -> failwith "expected missing import");

  let wrong_certificate_request =
    decoded_import_request "normal wrong certificate request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash
      (Option.map
         (fun hash -> mutate_byte hash 0)
         nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash)
  in
  assert_import_environment_rejects
    "normal import environment rejects certificate hash mismatch"
    "import_hash_mismatch" "import_certificate_hash_mismatch" nat_store
    wrong_certificate_request;

  let imported_axiom_name = make_name [ "ImportedAxiom" ] in
  let imported_axiom_hash = hash_bytes 0x7a in
  let imported_axiom =
    {
      Ext_cert.axiom_global_ref =
        Ext_term.Builtin
          { name = imported_axiom_name; decl_interface_hash = imported_axiom_hash };
      axiom_name = imported_axiom_name;
      axiom_decl_interface_hash = imported_axiom_hash;
    }
  in
  let public_exports =
    match
      nat_module.Ext_import_store.public_environment.Ext_import_store.public_exports
    with
    | export :: rest ->
        {
          export with
          Ext_import_store.public_axiom_dependencies = [ imported_axiom ];
        }
        :: rest
    | [] -> failwith "expected nat public exports"
  in
  let dependency_store =
    [
      {
        nat_module with
        Ext_import_store.public_environment =
          {
            nat_module.Ext_import_store.public_environment with
            Ext_import_store.public_exports;
            public_module_axioms = [ imported_axiom ];
          };
      };
    ]
  in
  let dependency_environment =
    assert_import_environment_ok "normal import copies axiom dependencies"
      dependency_store nat_request
  in
  let dependency_import =
    single_resolved_import "dependency import" dependency_environment
  in
  let dependency_public_environment =
    dependency_import.Ext_import_store.resolved_public_environment
  in
  let dependency_public_export =
    match dependency_public_environment.Ext_import_store.public_exports with
    | export :: _ -> export
    | [] -> failwith "expected dependency public export"
  in
  assert_int_equal "normal import copies export axiom dependencies" 1
    (List.length dependency_public_export.Ext_import_store.public_axiom_dependencies);
  assert_int_equal "normal import copies module axiom dependencies" 1
    (List.length dependency_public_environment.Ext_import_store.public_module_axioms);
  assert_int_equal "normal import flattens module axiom dependencies" 1
    (List.length
       (Ext_import_store.import_environment_module_axioms dependency_environment));

  let local_axiom_dependency = (encode_global_local 0, 0, hash_bytes 0x91) in
  let local_ref_decl =
    encode_decl_cert (encode_axiom_decl_payload 0 [] 0) [] [] (hash_bytes 0x91)
      (hash_bytes 0x92)
  in
  let local_ref_export =
    encode_export_entry_full 0 0x00 [] 1 None (hash_bytes 0x31) None None None
      (hash_bytes 0x91) [ local_axiom_dependency ]
  in
  let local_ref_module =
    encode_module ~module_name:[ "Local"; "Provider" ]
      ~axiom_report:(encode_axiom_report [] [ local_axiom_dependency ])
      [ [ "A" ] ]
      [ encode_level_zero ]
      [ encode_term_sort 0; encode_term_const (encode_global_local 0) [] ]
      [ local_ref_decl ] [ local_ref_export ]
  in
  let local_entry =
    assert_ok "local provider module entry"
      (Ext_import_store.module_entry_of_decoded
         (decode_module_bytes "local provider module" local_ref_module))
  in
  let local_request =
    decoded_import_request "normal local provider request"
      local_entry.Ext_import_store.import_entry.Ext_import.module_name
      local_entry.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  let local_environment =
    assert_import_environment_ok "normal local provider import"
      [ local_entry ] local_request
  in
  let local_import = single_resolved_import "normal local provider" local_environment in
  let local_public_environment =
    local_import.Ext_import_store.resolved_public_environment
  in
  let local_export =
    match local_public_environment.Ext_import_store.public_exports with
    | [ export ] -> export
    | _ -> failwith "expected one local provider public export"
  in
  let assert_public_self_axiom label axiom =
    match axiom.Ext_cert.axiom_global_ref with
    | Ext_term.Imported { import_index; name; decl_interface_hash } ->
        assert_int_equal (label ^ " import index")
          Ext_import_store.public_self_import_index import_index;
        assert_equal (label ^ " name") "A" (Ext_name.to_string name);
        assert_equal (label ^ " interface hash") (hash_bytes 0x91)
          decl_interface_hash
    | _ -> failwith (label ^ ": expected imported public self axiom ref")
  in
  (match local_export.Ext_import_store.public_ty with
  | Ext_term.Const
      ( Ext_term.Imported { import_index; name; decl_interface_hash },
        [] ) ->
      assert_int_equal "public environment remaps local ref import index"
        Ext_import_store.public_self_import_index import_index;
      assert_equal "public environment remaps local ref name" "A"
        (Ext_name.to_string name);
      assert_equal "public environment remaps local ref interface hash"
        (hash_bytes 0x91) decl_interface_hash
  | Ext_term.Const (Ext_term.Local _, _) ->
      failwith "public environment must not expose local refs"
  | _ -> failwith "expected public type to be an imported const");
  (match local_export.Ext_import_store.public_axiom_dependencies with
  | [ axiom ] -> assert_public_self_axiom "public export axiom dependency" axiom
  | _ -> failwith "expected one public export axiom dependency");
  match local_public_environment.Ext_import_store.public_module_axioms with
  | [ axiom ] -> assert_public_self_axiom "public module axiom dependency" axiom
  | _ -> failwith "expected one public module axiom dependency"

let run_import_high_trust_tests () =
  let nat_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let nat_module = load_single_import_entry "high-trust nat fixture" nat_path in
  assert_bool "source-free nat fixture starts unchecked"
    (not nat_module.Ext_import_store.checked_by_ext_checker);
  let nat_request_without_hash =
    decoded_import_request "high-trust missing certificate hash request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  assert_import_environment_rejects ~policy:Ext_import_store.high_trust_policy
    "high-trust rejects missing import certificate hash"
    "import_not_found" "missing_import_certificate_hash" [ nat_module ]
    nat_request_without_hash;
  let nat_request_with_hash =
    decoded_import_request "high-trust nat request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash
      nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash
  in
  assert_import_environment_rejects ~policy:Ext_import_store.high_trust_policy
    "high-trust rejects unchecked source-free import"
    "import_not_found" "unchecked_import" [ nat_module ] nat_request_with_hash;
  let wrong_certificate_request =
    decoded_import_request "high-trust wrong certificate request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash
      (Option.map
         (fun hash -> mutate_byte hash 0)
         nat_module.Ext_import_store.import_entry.Ext_import.certificate_hash)
  in
  assert_import_environment_rejects ~policy:Ext_import_store.high_trust_policy
    "high-trust rejects certificate hash mismatch"
    "import_hash_mismatch" "import_certificate_hash_mismatch" [ nat_module ]
    wrong_certificate_request

let declaration_fixture ?(offset = 0) ?(interface_hash = hash_bytes 0x51)
    ?(certificate_hash = hash_bytes 0x52) kind payload =
  let name =
    match payload with
    | Ext_cert.AxiomDecl { decl_name; _ }
    | Ext_cert.DefDecl { decl_name; _ }
    | Ext_cert.TheoremDecl { decl_name; _ }
    | Ext_cert.InductiveDecl { decl_name; _ }
    | Ext_cert.MutualInductiveBlockDecl { decl_name; _ } ->
        decl_name
  in
  {
    Ext_cert.name;
    kind;
    payload;
    dependencies = [];
    axiom_dependencies = [];
    hashes =
      {
        Ext_cert.decl_interface_hash = interface_hash;
        decl_certificate_hash = certificate_hash;
        decl_interface_hash_offset = offset;
        decl_certificate_hash_offset = offset;
      };
    offset;
  }

let declaration_with_dependencies declaration dependencies =
  { declaration with Ext_cert.dependencies = dependencies }

let dependency_entry global_ref decl_interface_hash =
  {
    Ext_cert.dependency_global_ref = global_ref;
    dependency_decl_interface_hash = decl_interface_hash;
  }

let axiom_ref global_ref axiom_name axiom_decl_interface_hash =
  { Ext_cert.axiom_global_ref = global_ref; axiom_name; axiom_decl_interface_hash }

let empty_axiom_report_entry index =
  {
    Ext_cert.report_decl_index = index;
    report_direct_axioms = [];
    report_transitive_axioms = [];
    report_offset = 300 + index;
  }

let empty_axiom_report declaration_count =
  {
    Ext_cert.per_declaration = List.init declaration_count empty_axiom_report_entry;
    module_axioms = [];
    module_axioms_offset = 400;
    core_features = [];
    core_features_offset = None;
  }

let decoded_axiom_report_fixture ?(module_name = make_name [ "AxiomReportFixture" ])
    names declarations =
  {
    Ext_cert.header =
      {
        format = Ext_cert.expected_format;
        core_spec = Ext_cert.expected_core_spec;
        module_name;
        version = Ext_cert.Legacy;
      };
    imports = [];
    name_table = located_names names;
    level_table = [];
    term_table = [];
    declaration_table = declarations;
    export_block = [];
    axiom_report = empty_axiom_report (List.length declarations);
    hashes =
      {
        Ext_cert.export_hash = hash_bytes 0x10;
        axiom_report_hash = hash_bytes 0x11;
        certificate_hash = hash_bytes 0x12;
        export_hash_offset = 500;
        axiom_report_hash_offset = 501;
        certificate_hash_offset = 502;
      };
  }

let set_axiom_report_hash decoded =
  let payload =
    assert_ok "axiom-report encode recomputed report"
      (Ext_canonical.encode_axiom_report decoded.Ext_cert.name_table
         decoded.Ext_cert.axiom_report)
  in
  let axiom_report_hash =
    Ext_canonical.hash_with_domain Ext_canonical.domain_axiom_report payload
  in
  {
    decoded with
    Ext_cert.hashes =
      { decoded.Ext_cert.hashes with Ext_cert.axiom_report_hash };
  }

let declaration_report_by_index report decl_index =
  match
    List.find_opt
      (fun entry -> entry.Ext_cert.report_decl_index = decl_index)
      report.Ext_cert.per_declaration
  with
  | Some entry -> entry
  | None -> failwith "missing recomputed declaration axiom report"

let set_declaration_axiom_dependencies_from_report decoded report =
  let declaration_table =
    List.mapi
      (fun decl_index declaration ->
        let entry = declaration_report_by_index report decl_index in
        {
          declaration with
          Ext_cert.axiom_dependencies = entry.Ext_cert.report_transitive_axioms;
        })
      decoded.Ext_cert.declaration_table
  in
  { decoded with Ext_cert.declaration_table }

let assert_axiom_report_value_ok label result =
  match result with
  | Ok value -> value
  | Error error ->
      failwith
        (label ^ ": unexpected axiom report error "
       ^ Ext_axiom.error_reason_code error)

let with_valid_recomputed_axiom_report imports decoded =
  let report =
    assert_axiom_report_value_ok "axiom-report recompute fixture"
      (Ext_axiom.recompute_axiom_report imports decoded)
  in
  let decoded = set_declaration_axiom_dependencies_from_report decoded report in
  set_axiom_report_hash { decoded with Ext_cert.axiom_report = report }

let assert_axiom_report_ok label result =
  match result with
  | Ok () -> ()
  | Error error ->
      failwith
        (label ^ ": unexpected axiom report error "
       ^ Ext_axiom.error_reason_code error)

let assert_axiom_report_rejects label expected_section expected_offset result =
  match result with
  | Ok () -> failwith (label ^ ": expected axiom report mismatch")
  | Error error ->
      assert_equal (label ^ " kind") "axiom_report_mismatch"
        (Ext_axiom.error_kind error);
      assert_equal (label ^ " reason") "axiom_report_mismatch"
        (Ext_axiom.error_reason_code error);
      assert_equal (label ^ " section") expected_section
        (Ext_bytes.section_name error.Ext_axiom.section);
      assert_int_equal (label ^ " offset") expected_offset error.Ext_axiom.offset;
      let raw =
        Ext_result.axiom_report_failure ~section:expected_section
          ~offset:expected_offset
      in
      assert_contains (label ^ " raw kind")
        "\"kind\": \"axiom_report_mismatch\"" raw;
      assert_contains (label ^ " raw reason")
        "\"reason_code\": \"axiom_report_mismatch\"" raw;
      assert_contains (label ^ " raw section")
        ("\"section\": \"" ^ expected_section ^ "\"")
        raw;
      assert_contains (label ^ " raw offset")
        ("\"offset\": " ^ string_of_int expected_offset)
        raw

let assert_policy_parse_ok label result =
  match result with
  | Ok policy -> policy
  | Error error ->
      failwith
        (label ^ ": unexpected policy parse error "
       ^ error.Ext_axiom.policy_field ^ " " ^ error.Ext_axiom.actual_value)

let assert_policy_parse_rejects label expected_field expected_value actual_value
    result =
  match result with
  | Ok _ -> failwith (label ^ ": expected policy parse error")
  | Error error ->
      assert_equal (label ^ " kind") "policy_input_error"
        (Ext_axiom.policy_error_kind error);
      assert_equal (label ^ " reason") "request_axiom_policy_invalid"
        (Ext_axiom.policy_error_reason_code error);
      assert_equal (label ^ " field") expected_field
        error.Ext_axiom.policy_field;
      assert_equal (label ^ " expected") expected_value
        error.Ext_axiom.expected_value;
      assert_equal (label ^ " actual") actual_value error.Ext_axiom.actual_value

let run_axiom_policy_parse_tests () =
  assert_bool "axiom policy default denies sorry"
    Ext_axiom.default_policy.Ext_axiom.deny_sorry;
  assert_bool "axiom policy default denies custom axioms"
    Ext_axiom.default_policy.Ext_axiom.deny_custom_axioms;
  assert_int_equal "axiom policy default allowlist empty" 0
    (List.length Ext_axiom.default_policy.Ext_axiom.allowed_axioms);

  let policy =
    assert_policy_parse_ok "axiom policy parses first-release toml"
      (Ext_axiom.parse_policy_toml
         {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = [
  "User.Custom.P",
  "Std.Logic.Eq.rec",
]
|})
  in
  assert_bool "axiom policy keeps mandatory sorry denial"
    policy.Ext_axiom.deny_sorry;
  assert_bool "axiom policy keeps mandatory custom denial"
    policy.Ext_axiom.deny_custom_axioms;
  assert_bool "axiom policy allows exact Std.Logic.Eq.rec"
    (Ext_axiom.policy_allows policy (make_name [ "Std"; "Logic"; "Eq"; "rec" ]));
  assert_bool "axiom policy rejects prefix-like axiom"
    (not
       (Ext_axiom.policy_allows policy
          (make_name [ "Std"; "Logic"; "Eq"; "rec"; "custom" ])));
  assert_bool "axiom policy rejects unlisted axiom"
    (not (Ext_axiom.policy_allows policy (make_name [ "User"; "Other" ])));

  let canonical_name_order =
    assert_policy_parse_ok "axiom policy uses canonical name-byte order"
      (Ext_axiom.parse_policy_toml
         {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = ["B", "AA"]
|})
  in
  assert_int_equal "canonical name-byte order keeps both names" 2
    (List.length canonical_name_order.Ext_axiom.allowed_axioms);

  let nbsp = string_of_codes [ 0xc2; 0xa0 ] in
  ignore
    (assert_policy_parse_ok "axiom policy accepts runner Unicode whitespace"
       (Ext_axiom.parse_policy_toml
          ("format" ^ nbsp ^ "=" ^ nbsp
         ^ "\"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms"
         ^ nbsp ^ "=" ^ nbsp ^ "[]\n")));
  assert_policy_parse_rejects "axiom policy rejects invalid UTF-8" "axiom_policy"
    "valid_toml" "invalid_toml"
    (Ext_axiom.parse_policy_toml
       ("format = \"npa.independent-checker.axiom_policy.v1\"\n"
       ^ "allowed_axioms = []\n" ^ string_of_codes [ 0xff ]));

  assert_policy_parse_rejects "axiom policy requires format"
    "axiom_policy.format" Ext_axiom.policy_format "missing"
    (Ext_axiom.parse_policy_toml "");
  assert_policy_parse_rejects "axiom policy requires allowlist"
    "axiom_policy.allowed_axioms" "array" "missing"
    (Ext_axiom.parse_policy_toml
       {|format = "npa.independent-checker.axiom_policy.v1"|});

  assert_policy_parse_rejects "axiom policy rejects JSON input" "axiom_policy"
    "valid_toml" "invalid_toml"
    (Ext_axiom.parse_policy_toml
       {|{"deny_sorry": true, "allowed_axioms": []}|});
  assert_policy_parse_rejects "axiom policy duplicate field is deterministic"
    "axiom_policy.format" "unique_object_keys" "duplicate_field"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = []
|});
  assert_policy_parse_rejects "axiom policy rejects custom-denial override"
    "axiom_policy.deny_custom_axioms" "absent" "unknown_field"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = []
deny_custom_axioms = false
|});
  assert_policy_parse_rejects "axiom policy allowlist wrong type"
    "axiom_policy.allowed_axioms" "array" "wrong_type"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = "Std.Logic.Eq.rec"
|});
  assert_policy_parse_rejects "axiom policy allowlist entry wrong type"
    "axiom_policy.allowed_axioms[0]" "axiom_name" "wrong_type"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = [1]
|});
  assert_policy_parse_rejects "axiom policy allowlist invalid name"
    "axiom_policy.allowed_axioms[0]" "axiom_name" "invalid_name_format"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = ["Std..Logic"]
|});
  assert_policy_parse_rejects "axiom policy allowlist order violation"
    "axiom_policy.allowed_axioms[1]" "axiom_name_canonical_order"
    "order_violation"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = ["AA", "B"]
|});
  assert_policy_parse_rejects "axiom policy duplicate axiom name"
    "axiom_policy.allowed_axioms[1]" "unique_axiom_name"
    "duplicate_axiom_name"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = ["Std.Logic.Eq.rec", "Std.Logic.Eq.rec"]
|});
  assert_policy_parse_rejects "axiom policy unknown field"
    "axiom_policy.allow_axioms" "absent" "unknown_field"
    (Ext_axiom.parse_policy_toml
       {|
format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = []
allow_axioms = []
|})

let assert_axiom_policy_ok label result =
  match result with
  | Ok () -> ()
  | Error error ->
      failwith
        (label ^ ": unexpected axiom policy error "
       ^ Ext_axiom.policy_check_error_reason_code error)

let assert_axiom_policy_rejects label expected_reason expected_section
    expected_offset result =
  match result with
  | Ok () -> failwith (label ^ ": expected axiom policy rejection")
  | Error error ->
      assert_equal (label ^ " kind") "forbidden_axiom"
        (Ext_axiom.policy_check_error_kind error);
      assert_equal (label ^ " reason") expected_reason
        (Ext_axiom.policy_check_error_reason_code error);
      assert_equal (label ^ " section") expected_section
        (Ext_bytes.section_name error.Ext_axiom.policy_section);
      assert_int_equal (label ^ " offset") expected_offset
        error.Ext_axiom.policy_offset;
      let raw =
        Ext_result.axiom_policy_failure ~reason_code:expected_reason
          ~section:expected_section ~offset:expected_offset
      in
      assert_contains (label ^ " raw kind") "\"kind\": \"forbidden_axiom\"" raw;
      assert_contains (label ^ " raw reason")
        ("\"reason_code\": \"" ^ expected_reason ^ "\"")
        raw;
      assert_contains (label ^ " raw section")
        ("\"section\": \"" ^ expected_section ^ "\"")
        raw;
      assert_contains (label ^ " raw offset")
        ("\"offset\": " ^ string_of_int expected_offset)
        raw

let decoded_single_axiom_policy_fixture module_name axiom_name axiom_hash =
  let axiom_decl =
    declaration_fixture ~offset:10 ~interface_hash:axiom_hash Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = axiom_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
         })
  in
  with_valid_recomputed_axiom_report Ext_import_store.import_environment_empty
    (decoded_axiom_report_fixture ~module_name [ axiom_name ] [ axiom_decl ])

let run_axiom_policy_tests () =
  let empty_imports = Ext_import_store.import_environment_empty in
  let custom_name = make_name [ "P" ] in
  let custom_decoded =
    decoded_single_axiom_policy_fixture (make_name [ "Policy"; "Custom" ])
      custom_name (hash_bytes 0xb1)
  in
  assert_axiom_policy_rejects "axiom policy rejects custom axiom"
    "forbidden_axiom" "axiom_report"
    custom_decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
    (Ext_axiom.enforce_axiom_policy empty_imports custom_decoded
       Ext_axiom.default_policy);
  let allow_custom_policy =
    {
      Ext_axiom.default_policy with
      Ext_axiom.allowed_axioms = [ make_name [ "Policy"; "Custom"; "P" ] ];
    }
  in
  assert_axiom_policy_ok "axiom policy accepts exact allowed custom axiom"
    (Ext_axiom.enforce_axiom_policy empty_imports custom_decoded
       allow_custom_policy);
  let permissive_policy =
    {
      Ext_axiom.default_policy with
      Ext_axiom.deny_custom_axioms = false;
      allowed_axioms = [];
    }
  in
  assert_axiom_policy_ok "axiom policy permits custom axioms when gate disabled"
    (Ext_axiom.enforce_axiom_policy empty_imports custom_decoded
       permissive_policy);

  let sorry_decoded =
    decoded_single_axiom_policy_fixture (make_name [ "Std"; "Nat" ])
      (make_name [ "A"; "sorry" ]) (hash_bytes 0xb2)
  in
  assert_axiom_policy_rejects "axiom policy rejects synthetic sorry first"
    "sorry_denied" "axiom_report"
    sorry_decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
    (Ext_axiom.enforce_axiom_policy empty_imports sorry_decoded
       {
         allow_custom_policy with
         Ext_axiom.allowed_axioms = [ make_name [ "Std"; "Nat"; "A"; "sorry" ] ];
       });

  let eq_rec_name = make_name [ "Eq"; "rec" ] in
  let eq_rec_hash =
    match Ext_env.builtin_decl_interface_hash eq_rec_name with
    | Some hash -> hash
    | None -> failwith "expected builtin Eq.rec hash"
  in
  let eq_rec_decoded =
    decoded_single_axiom_policy_fixture (make_name [ "Std"; "Logic" ])
      eq_rec_name eq_rec_hash
  in
  assert_axiom_policy_ok "axiom policy accepts exact Std.Logic.Eq.rec"
    (Ext_axiom.enforce_axiom_policy empty_imports eq_rec_decoded
       Ext_axiom.default_policy);

  let classical_decoded =
    decoded_single_axiom_policy_fixture (make_name [ "Std"; "Logic" ])
      (make_name [ "Classical"; "choice" ]) (hash_bytes 0xb4)
  in
  assert_axiom_policy_rejects "axiom policy rejects non Eq.rec std axiom"
    "forbidden_axiom" "axiom_report"
    classical_decoded.Ext_cert.axiom_report.Ext_cert.module_axioms_offset
    (Ext_axiom.enforce_axiom_policy empty_imports classical_decoded
       Ext_axiom.default_policy);

  let imported_eq_rec =
    axiom_ref
      (Ext_term.Imported
         {
           import_index = Ext_import_store.public_self_import_index;
           name = eq_rec_name;
           decl_interface_hash = eq_rec_hash;
         })
      eq_rec_name eq_rec_hash
  in
  let eq_rec_public_export =
    {
      Ext_import_store.public_export_name = eq_rec_name;
      public_export_kind = Ext_cert.Export_axiom;
      public_decl_interface_hash = eq_rec_hash;
      public_axiom_dependencies = [ imported_eq_rec ];
      public_universe_params = [];
      public_universe_constraints = [];
      public_ty = Ext_term.Sort Ext_env.level_type0;
      public_body = None;
    }
  in
  let std_logic_import_environment public_exports =
    {
      Ext_import_store.resolved_imports =
        [
          {
            Ext_import_store.resolved_module_name = make_name [ "Std"; "Logic" ];
            resolved_export_hash = hash_bytes 0xb5;
            resolved_certificate_hash = None;
            resolved_public_environment =
              {
                Ext_import_store.public_imports = [];
                public_exports;
                public_module_axioms = [ imported_eq_rec ];
                public_core_features = [];
                public_inductive_groups = [];
              };
          };
        ];
    }
  in
  let import_eq_rec_decoded =
    with_valid_recomputed_axiom_report
      (std_logic_import_environment [ eq_rec_public_export ])
      (decoded_axiom_report_fixture [] [])
  in
  assert_axiom_policy_ok "axiom policy accepts imported exact Std.Logic.Eq.rec"
    (Ext_axiom.enforce_axiom_policy
       (std_logic_import_environment [ eq_rec_public_export ])
       import_eq_rec_decoded Ext_axiom.default_policy);
  assert_axiom_policy_rejects
    "axiom policy rejects imported Eq.rec hash mismatch" "forbidden_axiom"
    "imports" 0
    (Ext_axiom.enforce_axiom_policy
       (std_logic_import_environment
          [
            {
              eq_rec_public_export with
              Ext_import_store.public_decl_interface_hash = hash_bytes 0xb6;
            };
          ])
       import_eq_rec_decoded Ext_axiom.default_policy);

  let imported_axiom_name = make_name [ "ImportedAxiom" ] in
  let imported_axiom_hash = hash_bytes 0xb7 in
  let imported_axiom =
    axiom_ref
      (Ext_term.Imported
         {
           import_index = Ext_import_store.public_self_import_index;
           name = imported_axiom_name;
           decl_interface_hash = imported_axiom_hash;
         })
      imported_axiom_name imported_axiom_hash
  in
  let import_environment =
    {
      Ext_import_store.resolved_imports =
        [
          {
            Ext_import_store.resolved_module_name = make_name [ "Imported" ];
            resolved_export_hash = hash_bytes 0xb8;
            resolved_certificate_hash = None;
            resolved_public_environment =
              {
                Ext_import_store.public_imports = [];
                public_exports =
                  [
                    {
                      Ext_import_store.public_export_name = imported_axiom_name;
                      public_export_kind = Ext_cert.Export_axiom;
                      public_decl_interface_hash = imported_axiom_hash;
                      public_axiom_dependencies = [ imported_axiom ];
                      public_universe_params = [];
                      public_universe_constraints = [];
                      public_ty = Ext_term.Sort Ext_env.level_type0;
                      public_body = None;
                    };
                  ];
                public_module_axioms = [ imported_axiom ];
                public_core_features = [];
                public_inductive_groups = [];
              };
          };
        ];
    }
  in
  let empty_decoded =
    with_valid_recomputed_axiom_report import_environment
      (decoded_axiom_report_fixture [] [])
  in
  assert_axiom_policy_rejects "axiom policy rechecks imported module axioms"
    "forbidden_axiom" "imports" 0
    (Ext_axiom.enforce_axiom_policy import_environment empty_decoded
       Ext_axiom.default_policy)

let run_axiom_report_tests () =
  let empty_imports = Ext_import_store.import_environment_empty in
  let axiom_name = make_name [ "LocalAxiom" ] in
  let theorem_name = make_name [ "UsesLocalAxiom" ] in
  let transitive_name = make_name [ "UsesTheorem" ] in
  let axiom_hash = hash_bytes 0x91 in
  let theorem_hash = hash_bytes 0x92 in
  let axiom_decl =
    declaration_fixture ~offset:10 ~interface_hash:axiom_hash Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = axiom_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
         })
  in
  let local_axiom_ref = Ext_term.Local { decl_index = 0 } in
  let theorem_decl =
    declaration_with_dependencies
      (declaration_fixture ~offset:20 ~interface_hash:theorem_hash Ext_cert.Theorem
         (Ext_cert.TheoremDecl
            {
              decl_name = theorem_name;
              decl_universe_params = [];
              decl_universe_constraints = [];
              decl_ty = Ext_term.Sort Ext_env.level_type0;
              decl_proof = Ext_term.Const (local_axiom_ref, []);
              decl_opacity = Ext_cert.Opaque;
            }))
      [ dependency_entry local_axiom_ref axiom_hash ]
  in
  let local_theorem_ref = Ext_term.Local { decl_index = 1 } in
  let transitive_decl =
    declaration_with_dependencies
      (declaration_fixture ~offset:30 Ext_cert.Theorem
         (Ext_cert.TheoremDecl
            {
              decl_name = transitive_name;
              decl_universe_params = [];
              decl_universe_constraints = [];
              decl_ty = Ext_term.Sort Ext_env.level_type0;
              decl_proof = Ext_term.Const (local_theorem_ref, []);
              decl_opacity = Ext_cert.Opaque;
            }))
      [ dependency_entry local_theorem_ref theorem_hash ]
  in
  let local_decoded =
    decoded_axiom_report_fixture [ axiom_name; theorem_name; transitive_name ]
      [ axiom_decl; theorem_decl; transitive_decl ]
  in
  let local_valid =
    with_valid_recomputed_axiom_report empty_imports local_decoded
  in
  assert_axiom_report_ok "axiom-report accepts local self dependency"
    (Ext_axiom.verify_axiom_report empty_imports local_valid);
  (match
     (List.nth local_valid.Ext_cert.axiom_report.Ext_cert.per_declaration 0)
       .Ext_cert.report_direct_axioms
   with
  | [ axiom ] ->
      assert_equal "axiom-report local direct self name" "LocalAxiom"
        (Ext_name.to_string axiom.Ext_cert.axiom_name)
  | _ -> failwith "expected local axiom direct dependency");
  (match
     (List.nth local_valid.Ext_cert.axiom_report.Ext_cert.per_declaration 2)
       .Ext_cert.report_direct_axioms
   with
  | [] -> ()
  | _ -> failwith "expected no direct axiom through local theorem dependency");
  (match
     (List.nth local_valid.Ext_cert.axiom_report.Ext_cert.per_declaration 2)
       .Ext_cert.report_transitive_axioms
   with
  | [ axiom ] ->
      assert_equal "axiom-report local transitive name" "LocalAxiom"
        (Ext_name.to_string axiom.Ext_cert.axiom_name)
  | _ -> failwith "expected transitive axiom through local theorem dependency");

  let missing_declaration_axiom =
    match local_valid.Ext_cert.declaration_table with
    | first :: second :: rest ->
        {
          local_valid with
          Ext_cert.declaration_table =
            first :: { second with Ext_cert.axiom_dependencies = [] } :: rest;
        }
    | _ -> failwith "expected local axiom fixture declarations"
  in
  assert_axiom_report_rejects
    "axiom-report rejects missing declaration axiom dependency" "declarations"
    theorem_decl.Ext_cert.offset
    (Ext_axiom.verify_axiom_report empty_imports missing_declaration_axiom);

  let missing_actual_dependency =
    match local_valid.Ext_cert.declaration_table with
    | first :: second :: third :: rest ->
        {
          local_valid with
          Ext_cert.declaration_table =
            first :: second :: { third with Ext_cert.dependencies = [] } :: rest;
        }
    | _ -> failwith "expected local axiom fixture declarations"
  in
  assert_axiom_report_rejects "axiom-report rejects missing actual dependency"
    "declarations" transitive_decl.Ext_cert.offset
    (Ext_axiom.verify_axiom_report empty_imports missing_actual_dependency);

  let missing_report_axiom =
    let per_declaration =
      match local_valid.Ext_cert.axiom_report.Ext_cert.per_declaration with
      | first :: second :: rest ->
          first
          :: { second with Ext_cert.report_transitive_axioms = [] }
          :: rest
      | _ -> failwith "expected local axiom report entries"
    in
    let report =
      { local_valid.Ext_cert.axiom_report with Ext_cert.per_declaration }
    in
    set_axiom_report_hash { local_valid with Ext_cert.axiom_report = report }
  in
  assert_axiom_report_rejects "axiom-report rejects missing report axiom"
    "axiom_report"
    (List.nth
       missing_report_axiom.Ext_cert.axiom_report.Ext_cert.per_declaration
       1)
      .Ext_cert.report_offset
    (Ext_axiom.verify_axiom_report empty_imports missing_report_axiom);

  let mismatched_report_hash =
    {
      local_valid with
      Ext_cert.hashes =
        {
          local_valid.Ext_cert.hashes with
          Ext_cert.axiom_report_hash =
            mutate_byte
              local_valid.Ext_cert.hashes.Ext_cert.axiom_report_hash
              0;
        };
    }
  in
  assert_axiom_report_rejects "axiom-report rejects recomputed hash mismatch"
    "hashes"
    local_valid.Ext_cert.hashes.Ext_cert.axiom_report_hash_offset
    (Ext_axiom.verify_axiom_report empty_imports mismatched_report_hash);

  let imported_axiom_name = make_name [ "ImportedAxiom" ] in
  let imported_theorem_name = make_name [ "ImportedTheorem" ] in
  let uses_import_name = make_name [ "UsesImportedTheorem" ] in
  let imported_axiom_hash = hash_bytes 0xa1 in
  let imported_theorem_hash = hash_bytes 0xa2 in
  let imported_axiom =
    axiom_ref
      (Ext_term.Imported
         {
           import_index = Ext_import_store.public_self_import_index;
           name = imported_axiom_name;
           decl_interface_hash = imported_axiom_hash;
         })
      imported_axiom_name imported_axiom_hash
  in
  let public_environment =
    {
      Ext_import_store.public_imports = [];
      public_exports =
        [
          {
            Ext_import_store.public_export_name = imported_axiom_name;
            public_export_kind = Ext_cert.Export_axiom;
            public_decl_interface_hash = imported_axiom_hash;
            public_axiom_dependencies = [ imported_axiom ];
            public_universe_params = [];
            public_universe_constraints = [];
            public_ty = Ext_term.Sort Ext_env.level_type0;
            public_body = None;
          };
          {
            Ext_import_store.public_export_name = imported_theorem_name;
            public_export_kind = Ext_cert.Export_theorem;
            public_decl_interface_hash = imported_theorem_hash;
            public_axiom_dependencies = [ imported_axiom ];
            public_universe_params = [];
            public_universe_constraints = [];
            public_ty = Ext_term.Sort Ext_env.level_type0;
            public_body = None;
          };
        ];
      public_module_axioms = [ imported_axiom ];
      public_core_features = [];
      public_inductive_groups = [];
    }
  in
  let import_environment =
    {
      Ext_import_store.resolved_imports =
        [
          {
            Ext_import_store.resolved_module_name = make_name [ "Imported" ];
            resolved_export_hash = hash_bytes 0xa3;
            resolved_certificate_hash = None;
            resolved_public_environment = public_environment;
          };
        ];
    }
  in
  let imported_theorem_ref =
    Ext_term.Imported
      {
        import_index = 0;
        name = imported_theorem_name;
        decl_interface_hash = imported_theorem_hash;
      }
  in
  let uses_import_decl =
    declaration_with_dependencies
      (declaration_fixture ~offset:30 Ext_cert.Theorem
         (Ext_cert.TheoremDecl
            {
              decl_name = uses_import_name;
              decl_universe_params = [];
              decl_universe_constraints = [];
              decl_ty = Ext_term.Sort Ext_env.level_type0;
              decl_proof = Ext_term.Const (imported_theorem_ref, []);
              decl_opacity = Ext_cert.Opaque;
            }))
      [ dependency_entry imported_theorem_ref imported_theorem_hash ]
  in
  let import_decoded =
    decoded_axiom_report_fixture
      [ imported_axiom_name; imported_theorem_name; uses_import_name ]
      [ uses_import_decl ]
  in
  let import_valid =
    with_valid_recomputed_axiom_report import_environment import_decoded
  in
  assert_axiom_report_ok "axiom-report preserves imported axiom dependencies"
    (Ext_axiom.verify_axiom_report import_environment import_valid);
  match import_valid.Ext_cert.axiom_report.Ext_cert.module_axioms with
  | [ axiom ] -> (
      match axiom.Ext_cert.axiom_global_ref with
      | Ext_term.Imported { import_index; name; decl_interface_hash } ->
          assert_int_equal "axiom-report imported axiom index" 0 import_index;
          assert_equal "axiom-report imported axiom name" "ImportedAxiom"
            (Ext_name.to_string name);
          assert_equal "axiom-report imported axiom hash" imported_axiom_hash
            decl_interface_hash
      | _ -> failwith "expected imported axiom dependency")
  | _ -> failwith "expected imported axiom dependency in module report"

let assert_duplicate_universe_param_error label result =
  match result with
  | Ok _ -> failwith (label ^ ": duplicate universe params must reject")
  | Error error ->
      assert_equal (label ^ " kind") "universe_inconsistency" (Ext_env.error_kind error);
      assert_equal (label ^ " reason") "duplicate_universe_param"
        (Ext_env.error_reason_code error.Ext_env.reason)

let run_type_env_tests () =
  let nat_path =
    Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert"
  in
  let nat_module = load_single_import_entry "type-env nat fixture" nat_path in
  let nat_request =
    decoded_import_request "type-env nat import request"
      nat_module.Ext_import_store.import_entry.Ext_import.module_name
      nat_module.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  let import_environment =
    assert_import_environment_ok "type-env import environment"
      [ nat_module ] nat_request
  in
  let env = Ext_env.of_imports import_environment in
  let import =
    single_resolved_import "type-env import" import_environment
  in
  let public_export =
    match
      import.Ext_import_store.resolved_public_environment
        .Ext_import_store.public_exports
    with
    | export :: _ -> export
    | [] -> failwith "expected imported public export"
  in
  let imported_ref =
    Ext_term.Imported
      {
        import_index = 0;
        name = public_export.Ext_import_store.public_export_name;
        decl_interface_hash =
          public_export.Ext_import_store.public_decl_interface_hash;
      }
  in
  let imported_signature =
    assert_env_resolves "type-env resolves imported export by name and hash" env
      imported_ref
  in
  assert_equal "type-env imported signature name"
    (Ext_name.to_string public_export.Ext_import_store.public_export_name)
    (Ext_name.to_string imported_signature.Ext_env.signature_name);
  assert_env_rejects "type-env rejects imported hash mismatch" "type_mismatch"
    "unknown_reference" env
    (Ext_term.Imported
       {
         import_index = 0;
         name = public_export.Ext_import_store.public_export_name;
         decl_interface_hash =
           mutate_byte public_export.Ext_import_store.public_decl_interface_hash 0;
       });
  assert_env_rejects "type-env rejects imported name mismatch" "type_mismatch"
    "unknown_reference" env
    (Ext_term.Imported
       {
         import_index = 0;
         name = make_name [ "Not"; "Exported" ];
         decl_interface_hash =
           public_export.Ext_import_store.public_decl_interface_hash;
       });

  let nat_name = make_name [ "Nat" ] in
  let nat_builtin_hash =
    match Ext_env.builtin_decl_interface_hash nat_name with
    | Some hash -> hash
    | None -> failwith "expected Nat builtin hash"
  in
  let nat_builtin =
    assert_env_resolves "type-env resolves builtin by name and hash" env
      (Ext_term.Builtin { name = nat_name; decl_interface_hash = nat_builtin_hash })
  in
  assert_bool "type-env builtin signature is builtin"
    (nat_builtin.Ext_env.signature_origin = Ext_env.Builtin);
  assert_env_rejects "type-env rejects builtin hash mismatch" "type_mismatch"
    "unknown_reference" env
    (Ext_term.Builtin
       { name = nat_name; decl_interface_hash = mutate_byte nat_builtin_hash 0 });
  let nat_rec_name = make_name [ "Nat"; "rec" ] in
  let nat_rec_hash =
    match Ext_env.builtin_decl_interface_hash nat_rec_name with
    | Some hash -> hash
    | None -> failwith "expected Nat.rec builtin hash"
  in
  let nat_rec_builtin =
    assert_env_resolves "type-env resolves Nat.rec builtin signature" env
      (Ext_term.Builtin { name = nat_rec_name; decl_interface_hash = nat_rec_hash })
  in
  assert_int_equal "type-env Nat.rec universe arity" 1
    (List.length nat_rec_builtin.Ext_env.signature_universe_params);
  (match nat_rec_builtin.Ext_env.signature_ty with
  | Ext_term.Pi _ -> ()
  | _ -> failwith "type-env Nat.rec type must not be a placeholder sort");

  let axiom_name = make_name [ "A" ] in
  let u_name = make_name [ "u" ] in
  let axiom_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = axiom_name;
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort (Ext_level.Param u_name);
         })
  in
  assert_env_rejects "type-env rejects forward local reference" "type_mismatch"
    "unknown_reference" Ext_env.empty (Ext_term.Local { decl_index = 0 });
  let env_with_axiom =
    match Ext_env.add_checked_declaration Ext_env.empty axiom_decl with
    | Ok env -> env
    | Error error ->
        failwith
          ("unexpected add axiom error "
         ^ Ext_env.error_reason_code error.Ext_env.reason)
  in
  let local_signature =
    assert_env_resolves "type-env resolves checked local declaration" env_with_axiom
      (Ext_term.Local { decl_index = 0 })
  in
  assert_equal "type-env local signature name" "A"
    (Ext_name.to_string local_signature.Ext_env.signature_name);
  assert_env_rejects "type-env rejects future local declaration" "type_mismatch"
    "unknown_reference" env_with_axiom (Ext_term.Local { decl_index = 1 });

  let duplicate_universe_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "DupUniverse" ];
           decl_universe_params = [ u_name; u_name ];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_level.Zero;
         })
  in
  assert_duplicate_universe_param_error "type-env duplicate universe"
    (Ext_env.add_checked_declaration Ext_env.empty duplicate_universe_decl);
  let duplicate_mutual_decl =
    declaration_fixture Ext_cert.Mutual_inductive
      (Ext_cert.MutualInductiveBlockDecl
         {
           decl_name = make_name [ "DupMutualUniverse" ];
           decl_universe_params = [ u_name; u_name ];
           decl_universe_constraints = [];
           mutual_inductives = [];
         })
  in
  assert_duplicate_universe_param_error "type-env duplicate mutual universe"
    (Ext_env.add_checked_declaration Ext_env.empty duplicate_mutual_decl);

  let theorem_decl =
    declaration_fixture Ext_cert.Theorem
      (Ext_cert.TheoremDecl
         {
           decl_name = make_name [ "T" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_level.Zero;
           decl_proof = Ext_term.BVar 0;
           decl_opacity = Ext_cert.Opaque;
         })
  in
  let env_with_theorem =
    match Ext_env.add_checked_declaration env_with_axiom theorem_decl with
    | Ok env -> env
    | Error error ->
        failwith
          ("unexpected add theorem error "
         ^ Ext_env.error_reason_code error.Ext_env.reason)
  in
  let theorem_signature =
    assert_env_resolves "type-env resolves checked theorem" env_with_theorem
      (Ext_term.Local { decl_index = 1 })
  in
  assert_bool "type-env theorem remains opaque"
    (theorem_signature.Ext_env.signature_unfolding = Ext_env.Opaque);
  let imported_theorem_name = make_name [ "Imported"; "T" ] in
  let imported_theorem_hash = hash_bytes 0x91 in
  let imported_theorem_environment =
    {
      Ext_import_store.resolved_imports =
        [
          {
            Ext_import_store.resolved_module_name = make_name [ "Imported" ];
            resolved_export_hash = hash_bytes 0x92;
            resolved_certificate_hash = None;
            resolved_public_environment =
              {
                Ext_import_store.public_imports = [];
                public_exports =
                  [
                    {
                      Ext_import_store.public_export_name = imported_theorem_name;
                      public_export_kind = Ext_cert.Export_theorem;
                      public_decl_interface_hash = imported_theorem_hash;
                      public_axiom_dependencies = [];
                      public_universe_params = [];
                      public_universe_constraints = [];
                      public_ty = Ext_term.Sort Ext_level.Zero;
                      public_body = Some (Ext_term.BVar 0);
                    };
                  ];
                public_module_axioms = [];
                public_core_features = [];
                public_inductive_groups = [];
              };
          };
        ];
    }
  in
  let imported_theorem_signature =
    assert_env_resolves "type-env imported theorem remains resolvable"
      (Ext_env.of_imports imported_theorem_environment)
      (Ext_term.Imported
         {
           import_index = 0;
           name = imported_theorem_name;
           decl_interface_hash = imported_theorem_hash;
         })
  in
  assert_bool "type-env imported theorem body remains opaque"
    (imported_theorem_signature.Ext_env.signature_unfolding = Ext_env.Opaque);

  let constructor_name = make_name [ "One" ] in
  let recursor_name = make_name [ "One"; "rec" ] in
  let inductive_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "OneType" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_level.Zero;
           ind_constructors =
             [ { Ext_cert.constructor_name; constructor_ty = Ext_term.Sort Ext_level.Zero } ];
           ind_recursor =
             Some
               {
                 Ext_cert.recursor_name;
                 recursor_universe_params = [];
                 recursor_ty = Ext_term.Sort Ext_level.Zero;
                 recursor_rules = { minor_start = 0; major_index = 0 };
               };
         })
  in
  let env_with_inductive =
    match Ext_env.add_checked_declaration Ext_env.empty inductive_decl with
    | Ok env -> env
    | Error error ->
        failwith
          ("unexpected add inductive error "
         ^ Ext_env.error_reason_code error.Ext_env.reason)
  in
  let constructor_signature =
    assert_env_resolves "type-env resolves generated constructor" env_with_inductive
      (Ext_term.LocalGenerated { decl_index = 0; name = constructor_name })
  in
  assert_equal "type-env constructor signature name" "One"
    (Ext_name.to_string constructor_signature.Ext_env.signature_name);
  let recursor_signature =
    assert_env_resolves "type-env resolves generated recursor" env_with_inductive
      (Ext_term.LocalGenerated { decl_index = 0; name = recursor_name })
  in
  assert_equal "type-env recursor signature name" "One.rec"
    (Ext_name.to_string recursor_signature.Ext_env.signature_name);
  assert_env_rejects "type-env rejects unknown generated local" "type_mismatch"
    "unknown_reference" env_with_inductive
    (Ext_term.LocalGenerated { decl_index = 0; name = make_name [ "Missing" ] })

let run_type_core_tests () =
  let nat = Ext_env.nat in
  let nat_zero = Ext_env.nat_zero in
  let theorem_ty = Ext_term.Pi (nat, nat) in
  let theorem_proof = Ext_term.Lam (nat, Ext_term.BVar 0) in
  assert_infers_term "type-core Sort zero inhabits Sort (succ zero)"
    (Ext_term.Sort (Ext_level.Succ Ext_level.Zero))
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.Sort Ext_level.Zero));
  assert_typecheck_rejects
    "type-core does not add cumulative Sort subtyping" "type_mismatch"
    "type_mismatch"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.Sort Ext_level.Zero)
       (Ext_term.Sort (Ext_level.Succ (Ext_level.Succ Ext_level.Zero))));
  assert_typecheck_ok "type-core well-typed theorem proof"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context theorem_proof
       theorem_ty);
  assert_infers_term "type-core lambda inference" theorem_ty
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context theorem_proof);
  assert_infers_term "type-core Pi inference"
    (Ext_term.Sort
       (Ext_level.Imax (Ext_level.Succ Ext_level.Zero, Ext_level.Succ Ext_level.Zero)))
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context theorem_ty);
  assert_typecheck_ok "type-core well-typed application"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.App (theorem_proof, nat_zero))
       nat);

  let alias_decl =
    declaration_fixture Ext_cert.Definition
      (Ext_cert.DefDecl
         {
           decl_name = make_name [ "AliasNat" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort (Ext_level.Succ Ext_level.Zero);
           decl_value = nat;
           decl_reducibility = Ext_cert.Reducible;
         })
  in
  let alias_env =
    match Ext_env.add_checked_declaration Ext_env.empty alias_decl with
    | Ok env -> env
    | Error error ->
        failwith
          ("unexpected add alias error "
         ^ Ext_env.error_reason_code error.Ext_env.reason)
  in
  let alias_ref = Ext_term.Const (Ext_term.Local { decl_index = 0 }, []) in
  assert_typecheck_ok "type-core reducible definition unfolds in expected type"
    (Ext_typecheck.check alias_env Ext_typecheck.empty_context nat_zero alias_ref);

  let let_term = Ext_term.Let (nat, nat_zero, Ext_term.BVar 0) in
  assert_infers_term "type-core let inference" nat
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context let_term);
  assert_typecheck_ok "type-core let checks value and body"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context let_term nat);

  assert_typecheck_rejects "type-core rejects ill-typed application" "type_mismatch"
    "expected_function"
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.App (nat_zero, nat_zero)));
  assert_typecheck_rejects "type-core rejects out-of-scope bvar" "type_mismatch"
    "invalid_bvar"
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context (Ext_term.BVar 0));
  assert_typecheck_rejects "type-core rejects sort/type mismatch" "type_mismatch"
    "type_mismatch"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context nat_zero
       (Ext_term.Sort Ext_level.Zero));
  assert_typecheck_rejects "type-core rejects lambda against non-Pi expected type"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context theorem_proof nat);
  assert_typecheck_rejects "type-core rejects non-sort Pi domain" "type_mismatch"
    "expected_sort"
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.Pi (nat_zero, nat)));
  assert_typecheck_rejects "type-core rejects bad let value" "type_mismatch"
    "type_mismatch"
    (Ext_typecheck.infer Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.Let (nat, Ext_term.Sort Ext_level.Zero, Ext_term.BVar 0)))

let run_type_declarations_tests () =
  let nat = Ext_env.nat in
  let nat_zero = Ext_env.nat_zero in
  let theorem_ty = Ext_term.Pi (nat, nat) in
  let theorem_proof = Ext_term.Lam (nat, Ext_term.BVar 0) in
  let axiom_hash = hash_bytes 0x60 in
  let def_hash = hash_bytes 0x61 in
  let theorem_hash = hash_bytes 0x62 in
  let axiom_decl =
    declaration_fixture ~interface_hash:axiom_hash Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "AxiomNat" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = nat;
         })
  in
  let def_decl =
    declaration_fixture ~interface_hash:def_hash Ext_cert.Definition
      (Ext_cert.DefDecl
         {
           decl_name = make_name [ "ZeroAlias" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = nat;
           decl_value = nat_zero;
           decl_reducibility = Ext_cert.Reducible;
         })
  in
  let theorem_decl =
    declaration_fixture ~interface_hash:theorem_hash Ext_cert.Theorem
      (Ext_cert.TheoremDecl
         {
           decl_name = make_name [ "IdNat" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = theorem_ty;
           decl_proof = theorem_proof;
           decl_opacity = Ext_cert.Opaque;
         })
  in
  let checked_env =
    assert_declaration_check_ok "type-declarations valid axiom def theorem"
      (Ext_typecheck.check_declarations [ axiom_decl; def_decl; theorem_decl ])
  in
  let theorem_signature =
    assert_env_resolves "type-declarations theorem added to checked env" checked_env
      (Ext_term.Local { decl_index = 2 })
  in
  assert_equal "type-declarations theorem signature name" "IdNat"
    (Ext_name.to_string theorem_signature.Ext_env.signature_name);

  let dependent_decl =
    declaration_with_dependencies theorem_decl
      [ dependency_entry (Ext_term.Local { decl_index = 0 }) axiom_hash ]
  in
  ignore
    (assert_declaration_check_ok "type-declarations dependency is ordered and available"
       (Ext_typecheck.check_declarations [ axiom_decl; dependent_decl ]));

  let forward_dependency_decl =
    declaration_with_dependencies def_decl
      [ dependency_entry (Ext_term.Local { decl_index = 0 }) def_hash ]
  in
  assert_typecheck_rejects "type-declarations rejects unavailable local dependency"
    "type_mismatch" "unknown_reference"
    (Ext_typecheck.check_declarations [ forward_dependency_decl ]);

  let mismatched_dependency_decl =
    declaration_with_dependencies theorem_decl
      [ dependency_entry (Ext_term.Local { decl_index = 0 }) (hash_bytes 0x7f) ]
  in
  assert_typecheck_rejects "type-declarations rejects dependency hash mismatch"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check_declarations [ axiom_decl; mismatched_dependency_decl ]);

  let wrong_theorem_decl =
    declaration_fixture Ext_cert.Theorem
      (Ext_cert.TheoremDecl
         {
           decl_name = make_name [ "WrongTheorem" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = nat;
           decl_proof = Ext_term.Sort Ext_level.Zero;
           decl_opacity = Ext_cert.Opaque;
         })
  in
  assert_typecheck_rejects "type-declarations rejects wrong theorem proof type"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check_declarations [ wrong_theorem_decl ]);

  let bad_arity_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "BadUniverseArity" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_env.builtin_const "Nat" [ Ext_level.Zero ];
         })
  in
  assert_typecheck_rejects "type-declarations rejects bad constant universe arity"
    "universe_inconsistency" "bad_universe_arity"
    (Ext_typecheck.check_declarations [ bad_arity_decl ]);

  let meta_name = make_unchecked_name [ "z?meta" ] in
  let unresolved_meta_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "UnresolvedUniverseMeta" ];
           decl_universe_params = [ meta_name ];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort (Ext_level.Param meta_name);
         })
  in
  assert_typecheck_rejects
    "type-declarations rejects unresolved universe metavariable"
    "universe_inconsistency" "unresolved_metavariable"
    (Ext_typecheck.check_declarations [ unresolved_meta_decl ])

let binder_type ty = { Ext_cert.binder_ty = ty }

let constructor_spec constructor_name constructor_ty =
  { Ext_cert.constructor_name; constructor_ty }

let local_family ?(decl_index = 0) levels =
  Ext_term.Const (Ext_term.Local { decl_index }, levels)

let local_generated ?(decl_index = 0) name levels =
  Ext_term.Const (Ext_term.LocalGenerated { decl_index; name }, levels)

let generated_signature_names env =
  String.concat ","
    (List.map
       (fun (_, signature) -> Ext_name.to_string signature.Ext_env.signature_name)
       env.Ext_env.generated_signatures)

let run_inductive_constructor_tests () =
  let nat_like_name = make_name [ "NatLike" ] in
  let nat_like_zero_name = make_name [ "NatLike"; "zero" ] in
  let nat_like_succ_name = make_name [ "NatLike"; "succ" ] in
  let nat_like = local_family [] in
  let nat_like_zero = constructor_spec nat_like_zero_name nat_like in
  let nat_like_succ =
    constructor_spec nat_like_succ_name (Ext_term.Pi (nat_like, nat_like))
  in
  let nat_like_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = nat_like_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors = [ nat_like_zero; nat_like_succ ];
           ind_recursor = None;
         })
  in
  let nat_like_env =
    assert_declaration_check_ok
      "inductive-constructors valid Nat-like constructors"
      (Ext_typecheck.check_declarations [ nat_like_decl ])
  in
  assert_equal "inductive-constructors generated Nat-like order"
    "NatLike.zero,NatLike.succ"
    (generated_signature_names nat_like_env);
  let nat_zero_signature =
    assert_env_resolves "inductive-constructors resolves Nat-like zero"
      nat_like_env
      (Ext_term.LocalGenerated { decl_index = 0; name = nat_like_zero_name })
  in
  if nat_zero_signature.Ext_env.signature_ty <> nat_like then
    failwith "inductive-constructors Nat-like zero type mismatch";

  let u_name = make_name [ "u" ] in
  let u_level = Ext_level.Param u_name in
  let sort_u = Ext_term.Sort u_level in
  let list_like_name = make_name [ "ListLike" ] in
  let list_like_nil_name = make_name [ "ListLike"; "nil" ] in
  let list_like_cons_name = make_name [ "ListLike"; "cons" ] in
  let list_like = local_family [ u_level ] in
  let list_like_of index = Ext_term.App (list_like, Ext_term.BVar index) in
  let list_like_nil =
    constructor_spec list_like_nil_name
      (Ext_term.Pi (sort_u, list_like_of 0))
  in
  let list_like_cons =
    constructor_spec list_like_cons_name
      (Ext_term.Pi
         ( sort_u,
           Ext_term.Pi
             ( Ext_term.BVar 0,
               Ext_term.Pi (list_like_of 1, list_like_of 2) ) ))
  in
  let list_like_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = list_like_name;
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors = [ list_like_nil; list_like_cons ];
           ind_recursor = None;
         })
  in
  let list_like_env =
    assert_declaration_check_ok
      "inductive-constructors valid List-like constructors"
      (Ext_typecheck.check_declarations [ list_like_decl ])
  in
  assert_equal "inductive-constructors generated List-like order"
    "ListLike.nil,ListLike.cons"
    (generated_signature_names list_like_env);

  let wrong_family_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "WrongFamily" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [ constructor_spec (make_name [ "WrongFamily"; "bad" ]) Ext_env.nat ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-constructors rejects constructor returning wrong family"
    "inductive_invalid" "inductive_invalid"
    (Ext_typecheck.check_declarations [ wrong_family_decl ]);

  let bad_domain_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "BadDomain" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "BadDomain"; "bad" ])
                 (Ext_term.Pi (Ext_env.nat_zero, local_family []));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-constructors validates constructor domain types"
    "type_mismatch" "expected_sort"
    (Ext_typecheck.check_declarations [ bad_domain_decl ]);

  let malformed_interface_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "MalformedList" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "MalformedList"; "bad" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( sort_u,
                          Ext_term.App (local_family [ u_level ], Ext_term.BVar 0)
                        )
                    ));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-constructors rejects malformed generated interface"
    "inductive_invalid" "inductive_invalid"
    (Ext_typecheck.check_declarations [ malformed_interface_decl ])

let run_inductive_universe_tests () =
  (* Audit.Code : Type, with Audit.Code.mk : Type -> Audit.Code.  The
     constructor domain itself lives one universe above Audit.Code's declared
     sort and must be rejected. *)
  let code_name = make_name [ "Audit"; "Code" ] in
  let mk_name = make_name [ "Audit"; "Code"; "mk" ] in
  let code = local_family [] in
  let code_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = code_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec mk_name
                 (Ext_term.Pi (Ext_term.Sort Ext_env.level_type0, code));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-universe rejects constructor domain above family universe"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations [ code_decl ]);

  let large_code = local_family [] in
  let large_code_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "LargeCode" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_level.Succ Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "Audit"; "LargeCode"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.Sort Ext_env.level_type0,
                      Ext_term.Pi (Ext_term.BVar 0, large_code) ));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok
       "inductive-universe accepts dependent fields under preceding domains"
       (Ext_typecheck.check_declarations [ large_code_decl ]));

  let le lhs rhs =
    {
      Ext_cert.constraint_lhs = lhs;
      constraint_relation = Ext_cert.Le;
      constraint_rhs = rhs;
    }
  in
  let u_name = make_name [ "u" ] in
  let u_level = Ext_level.Param u_name in
  let polymorphic_family = local_family [ u_level ] in
  let polymorphic_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "PolyCode" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "Audit"; "PolyCode"; "mk" ])
                 (Ext_term.Pi (Ext_term.Sort u_level, polymorphic_family));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-universe rejects polymorphic succ-u below u"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations [ polymorphic_decl ]);
  let constrained_family = local_family [ u_level ] in
  let constrained_payload constraints =
    Ext_cert.InductiveDecl
      {
        decl_name = make_name [ "Audit"; "Constrained" ];
        decl_universe_params = [ u_name ];
        decl_universe_constraints = constraints;
        ind_params = [];
        ind_indices = [];
        ind_sort = u_level;
        ind_constructors =
          [
            constructor_spec (make_name [ "Audit"; "Constrained"; "mk" ])
              (Ext_term.Pi (Ext_env.nat, constrained_family));
          ];
        ind_recursor = None;
      }
  in
  assert_typecheck_rejects
    "inductive-universe does not invent a missing field constraint"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations
       [ declaration_fixture Ext_cert.Inductive (constrained_payload []) ]);
  let explicit_constraint = le Ext_env.level_type0 u_level in
  let constrained_env =
    assert_declaration_check_ok
      "inductive-universe accepts an explicitly discharged field constraint"
      (Ext_typecheck.check_declarations
         [
           declaration_fixture Ext_cert.Inductive
             (constrained_payload [ explicit_constraint ]);
         ])
  in
  let constrained_constructor =
    assert_env_resolves
      "inductive-universe generated constructor inherits constraints"
      constrained_env
      (Ext_term.LocalGenerated
         { decl_index = 0; name = make_name [ "Audit"; "Constrained"; "mk" ] })
  in
  if
    constrained_constructor.Ext_env.signature_universe_constraints
    <> [ explicit_constraint ]
  then failwith "inductive-universe constructor constraints were not inherited";
  let recursor_name = make_name [ "Audit"; "ConstraintCarrier"; "rec" ] in
  let recursor_constraint_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "ConstraintCarrier" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [ explicit_constraint ];
           ind_params = [];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors = [];
           ind_recursor =
             Some
               {
                 Ext_cert.recursor_name;
                 recursor_universe_params = [ u_name; make_name [ "z" ] ];
                 recursor_ty = Ext_term.Sort u_level;
                 recursor_rules = { minor_start = 0; major_index = 0 };
               };
         })
  in
  let recursor_constraint_env =
    match Ext_env.add_checked_declaration Ext_env.empty recursor_constraint_decl with
    | Ok env -> env
    | Error _ -> failwith "inductive-universe could not install signature fixture"
  in
  let constrained_recursor =
    assert_env_resolves "inductive-universe generated recursor inherits constraints"
      recursor_constraint_env
      (Ext_term.LocalGenerated { decl_index = 0; name = recursor_name })
  in
  if
    constrained_recursor.Ext_env.signature_universe_constraints
    <> [ explicit_constraint ]
  then failwith "inductive-universe recursor constraints were not inherited";

  let parameter_family = local_family [ u_level ] in
  let parameter_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "ParameterOnly" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type (Ext_term.Sort u_level) ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "Audit"; "ParameterOnly"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.Sort u_level,
                      Ext_term.App (parameter_family, Ext_term.BVar 0) ));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok
       "inductive-universe excludes the uniform parameter prefix"
       (Ext_typecheck.check_declarations [ parameter_decl ]));

  let prop_family = local_family [] in
  let prop_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "PropBox" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_level.Zero;
           ind_constructors =
             [
               constructor_spec (make_name [ "Audit"; "PropBox"; "mk" ])
                 (Ext_term.Pi (Ext_term.Sort Ext_env.level_type0, prop_family));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok
       "inductive-universe preserves impredicative Prop fields"
       (Ext_typecheck.check_declarations [ prop_decl ]));

  let zero_constrained_family = local_family [ u_level ] in
  let zero_constrained_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Audit"; "ZeroConstrained" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints =
             [
               {
                 Ext_cert.constraint_lhs = u_level;
                 constraint_relation = Ext_cert.Eq;
                 constraint_rhs = Ext_level.Zero;
               };
             ];
           ind_params = [];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec
                 (make_name [ "Audit"; "ZeroConstrained"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.Sort Ext_env.level_type0,
                      zero_constrained_family ));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "inductive-universe does not treat a zero-constrained parameter as Prop"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations [ zero_constrained_decl ]);

  let v_name = make_name [ "v" ] in
  let w_name = make_name [ "w" ] in
  let v_level = Ext_level.Param v_name in
  let w_level = Ext_level.Param w_name in
  let max_context =
    match Ext_universe.create [ u_name; v_name; w_name ] [ le u_level v_level ] with
    | Ok context -> context
    | Error _ -> failwith "inductive-universe could not construct max context"
  in
  (match
     Ext_universe.entails_level_le max_context u_level
       (Ext_level.Max (v_level, w_level))
   with
  | Ok true -> ()
  | _ -> failwith "inductive-universe right-hand max obligation was not entailed");
  let transitive_context =
    match
      Ext_universe.create [ u_name; v_name; w_name ]
        [ le u_level v_level; le v_level w_level ]
    with
    | Ok context -> context
    | Error _ -> failwith "inductive-universe could not construct transitive context"
  in
  (match Ext_universe.entails_level_le transitive_context u_level w_level with
  | Ok true -> ()
  | _ -> failwith "inductive-universe transitive obligation was not entailed");
  (match
     Ext_universe.entails_level_le transitive_context (Ext_level.Succ v_level)
       (Ext_level.Max (u_level, w_level))
   with
  | Ok false -> ()
  | _ -> failwith "inductive-universe false supported obligation was accepted");

  let constraint_shape_decl name constraints =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "Audit"; name ];
           decl_universe_params = [ u_name; v_name; w_name ];
           decl_universe_constraints = constraints;
           decl_ty = Ext_term.Sort u_level;
         })
  in
  assert_typecheck_rejects
    "inductive-universe rejects duplicate stored constraints"
    "universe_inconsistency" "duplicate_universe_constraint"
    (Ext_typecheck.check_declarations
       [
         constraint_shape_decl "DuplicateConstraint"
           [ le u_level v_level; le u_level v_level ];
       ]);
  assert_typecheck_rejects
    "inductive-universe rejects unsorted stored constraints"
    "noncanonical_encoding" "noncanonical_universe_constraints"
    (Ext_typecheck.check_declarations
       [
         constraint_shape_decl "UnsortedConstraint"
           [ le v_level w_level; le u_level v_level ];
       ]);

  let resource_params =
    List.init 64 (fun index -> make_name [ Printf.sprintf "u%03d" index ])
  in
  let resource_context =
    match Ext_universe.create resource_params [] with
    | Ok context -> context
    | Error _ -> failwith "inductive-universe could not construct resource context"
  in
  let max_level names =
    List.fold_left
      (fun level name ->
        Ext_level.normalize (Ext_level.Max (level, Ext_level.Param name)))
      Ext_level.Zero names
  in
  let rec take_names count names =
    if count = 0 then []
    else
      match names with
      | [] -> []
      | name :: rest -> name :: take_names (count - 1) rest
  in
  let rec drop_names count names =
    if count = 0 then names
    else
      match names with
      | [] -> []
      | _ :: rest -> drop_names (count - 1) rest
  in
  (match
     Ext_universe.entails_level_le resource_context
       (max_level (take_names 32 resource_params))
       (max_level (drop_names 31 resource_params))
   with
  | Error { Ext_universe.reason = Ext_universe.Resource_limit } -> ()
  | _ -> failwith "inductive-universe max atom-pair limit was not enforced");

  let too_many_params =
    List.init 65 (fun index -> make_name [ Printf.sprintf "v%03d" index ])
  in
  (match Ext_universe.create too_many_params [] with
  | Error { Ext_universe.reason = Ext_universe.Resource_limit } -> ()
  | _ -> failwith "inductive-universe context node limit was not enforced");

  let provider_hash = hash_bytes 0x76 in
  let provider_decl =
    declaration_fixture ~interface_hash:provider_hash Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "Audit"; "Provider" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [ le Ext_env.level_type0 u_level ];
           decl_ty = Ext_term.Sort u_level;
         })
  in
  let consumer_payload constraints =
    Ext_cert.AxiomDecl
      {
        decl_name = make_name [ "Audit"; "Consumer" ];
        decl_universe_params = [ v_name ];
        decl_universe_constraints = constraints;
        decl_ty = Ext_term.Const (Ext_term.Local { decl_index = 0 }, [ v_level ]);
      }
  in
  assert_typecheck_rejects
    "inductive-universe enforces instantiated signature constraints"
    "universe_inconsistency" "universe_constraint_violation"
    (Ext_typecheck.check_declarations
       [
         provider_decl;
         declaration_fixture Ext_cert.Axiom (consumer_payload []);
       ]);
  ignore
    (assert_declaration_check_ok
       "inductive-universe accepts entailed instantiated signature constraints"
       (Ext_typecheck.check_declarations
          [
            provider_decl;
            declaration_fixture Ext_cert.Axiom
              (consumer_payload [ le Ext_env.level_type0 v_level ]);
          ]));

  let unsupported_constraint_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "Audit"; "UnsupportedConstraint" ];
           decl_universe_params = [ u_name; v_name; w_name ];
           decl_universe_constraints =
             [ le u_level (Ext_level.Max (v_level, w_level)) ];
           decl_ty = Ext_term.Sort u_level;
         })
  in
  assert_typecheck_rejects
    "inductive-universe rejects stored right-hand max constraints"
    "universe_inconsistency" "unsupported_universe_constraint"
    (Ext_typecheck.check_declarations [ unsupported_constraint_decl ]);

  let unsatisfiable_constraint_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "Audit"; "UnsatisfiableConstraint" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints =
             [ le (Ext_level.Succ u_level) u_level ];
           decl_ty = Ext_term.Sort u_level;
         })
  in
  assert_typecheck_rejects "inductive-universe rejects inconsistent assumptions"
    "universe_inconsistency" "unsatisfiable_universe_constraints"
    (Ext_typecheck.check_declarations [ unsatisfiable_constraint_decl ]);

  let malicious_mutual_decl =
    let family_name = make_name [ "Audit"; "Mutual"; "Code" ] in
    declaration_fixture Ext_cert.Mutual_inductive
      (Ext_cert.MutualInductiveBlockDecl
         {
           decl_name = make_name [ "Audit"; "Mutual" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           mutual_inductives =
             [
               {
                 Ext_cert.mutual_name = family_name;
                 mutual_params = [];
                 mutual_indices = [];
                 mutual_sort = Ext_env.level_type0;
                 mutual_constructors =
                   [
                     constructor_spec
                       (make_name [ "Audit"; "Mutual"; "Code"; "mk" ])
                       (Ext_term.Pi
                          ( Ext_term.Sort Ext_env.level_type0,
                            Ext_term.Const
                              ( Ext_term.LocalGenerated
                                  { decl_index = 0; name = family_name },
                                [] ) ));
                   ];
                 mutual_recursor = None;
               };
             ];
         })
  in
  assert_typecheck_rejects
    "inductive-universe enforces malicious mutual constructor bounds"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations [ malicious_mutual_decl ]);

  let legacy_export_offset = 919 in
  let constrained_export =
    {
      Ext_cert.export_name = make_name [ "Audit"; "Provider" ];
      export_kind = Ext_cert.Export_axiom;
      export_universe_params = [ u_name ];
      export_universe_constraints = [];
      export_ty = Ext_term.Sort u_level;
      export_body = None;
      export_type_hash = hash_bytes 0x77;
      export_body_hash = None;
      export_reducibility = None;
      export_opacity = None;
      export_decl_interface_hash = provider_hash;
      export_axiom_dependencies = [];
      export_offset = legacy_export_offset;
    }
  in
  let constrained_legacy_module =
    {
      (decoded_axiom_report_fixture
         [ make_name [ "Audit"; "Provider" ]; u_name ] [ provider_decl ])
      with
      Ext_cert.export_block = [ constrained_export ];
    }
  in
  assert_decode_error
    "inductive-universe legacy exports cannot erase constraints"
    "unsupported_schema_version"
    Ext_bytes.Constrained_export_requires_format_upgrade Ext_bytes.Export_block
    legacy_export_offset
    (Ext_import_store.public_environment_of_decoded constrained_legacy_module);

  let fixture_path =
    Filename.concat (root_dir ())
      "../../testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert"
  in
  let fixture =
    decode_module_bytes "inductive-universe frozen fixture"
      (read_binary_file fixture_path)
  in
  assert_typecheck_rejects "inductive-universe rejects frozen exploit fixture"
    "universe_inconsistency" "constructor_universe_bound_violation"
    (Ext_typecheck.check_declarations fixture.Ext_cert.declaration_table)

let run_positivity_tests () =
  let positive_name = make_name [ "Positive" ] in
  let positive_family = local_family [] in
  let positive_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = positive_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "Positive"; "zero" ]) positive_family;
               constructor_spec (make_name [ "Positive"; "succ" ])
                 (Ext_term.Pi (positive_family, positive_family));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok "positivity accepts direct recursive domain"
       (Ext_typecheck.check_declarations [ positive_decl ]));

  let positive_function_name = make_name [ "PositiveFunction" ] in
  let positive_function_family = local_family [] in
  let positive_function_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = positive_function_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "PositiveFunction"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.Pi (Ext_env.nat, positive_function_family),
                      positive_function_family ));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok
       "positivity accepts recursive occurrence in function codomain"
       (Ext_typecheck.check_declarations [ positive_function_decl ]));

  let u_name = make_name [ "u" ] in
  let u_level = Ext_level.Param u_name in
  let sort_u = Ext_term.Sort u_level in
  let list_like = local_family [ u_level ] in
  let list_like_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "ListPositive" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "ListPositive"; "nil" ])
                 (Ext_term.Pi (sort_u, Ext_term.App (list_like, Ext_term.BVar 0)));
               constructor_spec (make_name [ "ListPositive"; "cons" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( Ext_term.BVar 0,
                          Ext_term.Pi
                            ( Ext_term.App (list_like, Ext_term.BVar 1),
                              Ext_term.App (list_like, Ext_term.BVar 2) ) )
                    ));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok "positivity accepts List-like direct recursion"
       (Ext_typecheck.check_declarations [ list_like_decl ]));

  let approved_const decl_index args =
    Ext_env.apps
      (Ext_term.Const (Ext_term.Local { decl_index }, [ u_level ]))
      args
  in
  let approved_list = approved_const 0 in
  let approved_option = approved_const 1 in
  let approved_prod = approved_const 2 in
  let approved_list_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "List" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "List"; "nil" ])
                 (Ext_term.Pi (sort_u, approved_list [ Ext_term.BVar 0 ]));
               constructor_spec (make_name [ "List"; "cons" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( Ext_term.BVar 0,
                          Ext_term.Pi
                            ( approved_list [ Ext_term.BVar 1 ],
                              approved_list [ Ext_term.BVar 2 ] ) ) ));
             ];
           ind_recursor = None;
         })
  in
  let approved_option_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Option" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "Option"; "none" ])
                 (Ext_term.Pi (sort_u, approved_option [ Ext_term.BVar 0 ]));
               constructor_spec (make_name [ "Option"; "some" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( Ext_term.BVar 0,
                          approved_option [ Ext_term.BVar 1 ] ) ));
             ];
           ind_recursor = None;
         })
  in
  let approved_prod_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Prod" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u; binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "Prod"; "mk" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( sort_u,
                          Ext_term.Pi
                            ( Ext_term.BVar 1,
                              Ext_term.Pi
                                ( Ext_term.BVar 1,
                                  approved_prod
                                    [ Ext_term.BVar 3; Ext_term.BVar 2 ] ) ) ) ));
             ];
           ind_recursor = None;
         })
  in
  let rose_family =
    Ext_term.Const (Ext_term.Local { decl_index = 3 }, [ u_level ])
  in
  let rose_at arg = Ext_term.App (rose_family, arg) in
  let rose_nested = rose_at (Ext_term.BVar 1) in
  let rose_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "Rose" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "Rose"; "node" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( Ext_term.BVar 0,
                          Ext_term.Pi
                            ( approved_prod
                                [
                                  approved_option [ rose_nested ];
                                  approved_list [ rose_nested ];
                                ],
                              rose_at (Ext_term.BVar 2) ) ) ));
             ];
           ind_recursor = None;
         })
  in
  ignore
    (assert_declaration_check_ok
       "positivity accepts exact List Option Prod nested recursion"
       (Ext_typecheck.check_declarations
          [
            approved_list_decl;
            approved_option_decl;
            approved_prod_decl;
            rose_decl;
          ]));

  let fake_list_decl =
    match approved_list_decl.Ext_cert.payload with
    | Ext_cert.InductiveDecl payload ->
        {
          approved_list_decl with
          Ext_cert.payload =
            Ext_cert.InductiveDecl
              {
                payload with
                ind_constructors =
                  [
                    constructor_spec (make_name [ "List"; "fake" ])
                      (Ext_term.Pi
                         (sort_u, approved_list [ Ext_term.BVar 0 ]));
                  ];
              };
        }
    | _ -> failwith "invalid approved List fixture"
  in
  let fake_rose_family =
    Ext_term.Const (Ext_term.Local { decl_index = 1 }, [ u_level ])
  in
  let fake_rose_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "FakeRose" ];
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors =
             [
               constructor_spec (make_name [ "FakeRose"; "node" ])
                 (Ext_term.Pi
                    ( sort_u,
                      Ext_term.Pi
                        ( approved_list
                            [ Ext_term.App (fake_rose_family, Ext_term.BVar 0) ],
                          Ext_term.App
                            (fake_rose_family, Ext_term.BVar 1) ) ));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "positivity rejects name-only fake approved List"
    "positivity_failure" "positivity_failure"
    (Ext_typecheck.check_declarations [ fake_list_decl; fake_rose_decl ]);

  let bad_family = local_family [] in
  let bad_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "BadNegative" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "BadNegative"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.Pi (bad_family, Ext_env.nat),
                      bad_family ));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "positivity rejects recursive occurrence in function domain"
    "positivity_failure" "positivity_failure"
    (Ext_typecheck.check_declarations [ bad_decl ]);

  let wrapper_decl =
    declaration_fixture Ext_cert.Axiom
      (Ext_cert.AxiomDecl
         {
           decl_name = make_name [ "Wrapper" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty =
             Ext_term.Pi
               (Ext_term.Sort Ext_env.level_type0, Ext_term.Sort Ext_env.level_type0);
         })
  in
  let nested_family = local_family ~decl_index:1 [] in
  let nested_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = make_name [ "BadNested" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors =
             [
               constructor_spec (make_name [ "BadNested"; "mk" ])
                 (Ext_term.Pi
                    ( Ext_term.App
                        (Ext_term.Const (Ext_term.Local { decl_index = 0 }, []), nested_family),
                      nested_family ));
             ];
           ind_recursor = None;
         })
  in
  assert_typecheck_rejects
    "positivity rejects unsupported nested recursive occurrence"
    "positivity_failure" "positivity_failure"
    (Ext_typecheck.check_declarations [ wrapper_decl; nested_decl ])

let run_recursor_tests () =
  let nat_name = make_name [ "RecNat" ] in
  let nat_zero_name = make_name [ "RecNat"; "zero" ] in
  let nat_succ_name = make_name [ "RecNat"; "succ" ] in
  let nat_rec_name = make_name [ "RecNat"; "rec" ] in
  let motive_universe = make_name [ "r" ] in
  let motive_level = Ext_level.Param motive_universe in
  let nat_family = local_family [] in
  let nat_zero_ctor = constructor_spec nat_zero_name nat_family in
  let nat_succ_ctor =
    constructor_spec nat_succ_name (Ext_term.Pi (nat_family, nat_family))
  in
  let nat_zero_term = local_generated nat_zero_name [] in
  let nat_succ_term arg =
    Ext_term.App (local_generated nat_succ_name [], arg)
  in
  let nat_motive_domain =
    Ext_term.Pi (nat_family, Ext_term.Sort motive_level)
  in
  let nat_zero_minor = Ext_term.App (Ext_term.BVar 0, nat_zero_term) in
  let nat_succ_minor =
    Ext_term.Pi
      ( nat_family,
        Ext_term.Pi
          ( Ext_term.App (Ext_term.BVar 2, Ext_term.BVar 0),
            Ext_term.App
              ( Ext_term.BVar 3,
                nat_succ_term (Ext_term.BVar 1) ) ) )
  in
  let nat_result = Ext_term.App (Ext_term.BVar 3, Ext_term.BVar 0) in
  let nat_recursor_ty =
    Ext_term.Pi
      ( nat_motive_domain,
        Ext_term.Pi
          ( nat_zero_minor,
            Ext_term.Pi
              ( nat_succ_minor,
                Ext_term.Pi (nat_family, nat_result) ) ) )
  in
  let nat_recursor recursor_ty =
    {
      Ext_cert.recursor_name = nat_rec_name;
      recursor_universe_params = [ motive_universe ];
      recursor_ty;
      recursor_rules = { minor_start = 1; major_index = 3 };
    }
  in
  let nat_decl recursor_ty =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = nat_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [];
           ind_sort = Ext_env.level_type0;
           ind_constructors = [ nat_zero_ctor; nat_succ_ctor ];
           ind_recursor = Some (nat_recursor recursor_ty);
         })
  in
  let nat_env =
    assert_declaration_check_ok "recursor accepts Nat-like recursor shape"
      (Ext_typecheck.check_declarations [ nat_decl nat_recursor_ty ])
  in
  let nat_rec_term =
    local_generated nat_rec_name [ Ext_env.level_type0 ]
  in
  let nat_motive = Ext_term.Lam (nat_family, nat_family) in
  let nat_step =
    Ext_term.Lam
      (nat_family, Ext_term.Lam (nat_family, Ext_term.BVar 1))
  in
  let nat_rec_zero =
    Ext_env.apps nat_rec_term
      [ nat_motive; nat_zero_term; nat_step; nat_zero_term ]
  in
  assert_term_result "recursor Nat-like zero iota" nat_zero_term
    (Ext_typecheck.whnf nat_env Ext_typecheck.empty_context nat_rec_zero);
  assert_typecheck_ok "recursor Nat-like zero checks through iota"
    (Ext_typecheck.check nat_env Ext_typecheck.empty_context nat_rec_zero
       nat_family);
  let nat_rec_succ =
    Ext_env.apps nat_rec_term
      [ nat_motive; nat_zero_term; nat_step; nat_succ_term nat_zero_term ]
  in
  assert_term_result "recursor Nat-like succ iota" nat_zero_term
    (Ext_typecheck.whnf nat_env Ext_typecheck.empty_context nat_rec_succ);
  assert_typecheck_ok "recursor Nat-like succ checks through iota"
    (Ext_typecheck.check nat_env Ext_typecheck.empty_context nat_rec_succ
       nat_family);

  let bad_motive_ty =
    Ext_term.Pi
      ( Ext_term.Pi (Ext_env.nat, Ext_term.Sort motive_level),
        Ext_term.Pi
          ( nat_zero_minor,
            Ext_term.Pi
              ( nat_succ_minor,
                Ext_term.Pi (nat_family, nat_result) ) ) )
  in
  assert_typecheck_rejects "recursor rejects bad motive domain"
    "inductive_invalid" "inductive_invalid"
    (Ext_typecheck.check_declarations [ nat_decl bad_motive_ty ]);
  let bad_minor_ty =
    let bad_succ_minor =
      Ext_term.Pi
        ( nat_family,
          Ext_term.App
            (Ext_term.BVar 2, nat_succ_term (Ext_term.BVar 0)) )
    in
    Ext_term.Pi
      ( nat_motive_domain,
        Ext_term.Pi
          ( nat_zero_minor,
            Ext_term.Pi
              ( bad_succ_minor,
                Ext_term.Pi (nat_family, nat_result) ) ) )
  in
  assert_typecheck_rejects "recursor rejects bad minor premise"
    "inductive_invalid" "inductive_invalid"
    (Ext_typecheck.check_declarations [ nat_decl bad_minor_ty ]);
  let bad_result_ty =
    Ext_term.Pi
      ( nat_motive_domain,
        Ext_term.Pi
          ( nat_zero_minor,
            Ext_term.Pi
              ( nat_succ_minor,
                Ext_term.Pi
                  ( nat_family,
                    Ext_term.App (Ext_term.BVar 3, nat_zero_term) ) ) ) )
  in
  assert_typecheck_rejects "recursor rejects bad result"
    "inductive_invalid" "inductive_invalid"
    (Ext_typecheck.check_declarations [ nat_decl bad_result_ty ]);

  let u_name = make_name [ "u" ] in
  let v_name = make_name [ "v" ] in
  let u_level = Ext_level.Param u_name in
  let v_level = Ext_level.Param v_name in
  let sort_u = Ext_term.Sort u_level in
  let list_name = make_name [ "RecList" ] in
  let nil_name = make_name [ "RecList"; "nil" ] in
  let cons_name = make_name [ "RecList"; "cons" ] in
  let list_rec_name = make_name [ "RecList"; "rec" ] in
  let list_family = local_family [ u_level ] in
  let list_of index = Ext_term.App (list_family, Ext_term.BVar index) in
  let nil_ctor =
    constructor_spec nil_name (Ext_term.Pi (sort_u, list_of 0))
  in
  let cons_ctor =
    constructor_spec cons_name
      (Ext_term.Pi
         ( sort_u,
           Ext_term.Pi
             ( Ext_term.BVar 0,
               Ext_term.Pi (list_of 1, list_of 2) ) ))
  in
  let nil_const level = local_generated nil_name [ level ] in
  let cons_const level = local_generated cons_name [ level ] in
  let list_rec_const levels = local_generated list_rec_name levels in
  let list_motive_domain =
    Ext_term.Pi
      (Ext_term.App (list_family, Ext_term.BVar 0), Ext_term.Sort v_level)
  in
  let nil_minor =
    Ext_term.App
      (Ext_term.BVar 0, Ext_term.App (nil_const u_level, Ext_term.BVar 1))
  in
  let cons_value =
    Ext_env.apps (cons_const u_level)
      [ Ext_term.BVar 5; Ext_term.BVar 2; Ext_term.BVar 1 ]
  in
  let cons_minor =
    Ext_term.Pi
      ( Ext_term.BVar 2,
        Ext_term.Pi
          ( Ext_term.App (list_family, Ext_term.BVar 3),
            Ext_term.Pi
              ( Ext_term.App (Ext_term.BVar 3, Ext_term.BVar 0),
                Ext_term.App (Ext_term.BVar 4, cons_value) ) ) )
  in
  let list_major_domain = Ext_term.App (list_family, Ext_term.BVar 3) in
  let list_result = Ext_term.App (Ext_term.BVar 3, Ext_term.BVar 0) in
  let list_recursor_ty =
    Ext_term.Pi
      ( sort_u,
        Ext_term.Pi
          ( list_motive_domain,
            Ext_term.Pi
              ( nil_minor,
                Ext_term.Pi
                  ( cons_minor,
                    Ext_term.Pi (list_major_domain, list_result) ) ) ) )
  in
  let list_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = list_name;
           decl_universe_params = [ u_name ];
           decl_universe_constraints = [];
           ind_params = [ binder_type sort_u ];
           ind_indices = [];
           ind_sort = u_level;
           ind_constructors = [ nil_ctor; cons_ctor ];
           ind_recursor =
             Some
               {
                 Ext_cert.recursor_name = list_rec_name;
                 recursor_universe_params = [ u_name; v_name ];
                 recursor_ty = list_recursor_ty;
                 recursor_rules = { minor_start = 2; major_index = 4 };
               };
         })
  in
  let list_env =
    assert_declaration_check_ok "recursor accepts List-like recursor shape"
      (Ext_typecheck.check_declarations [ list_decl ])
  in
  let list_nat =
    Ext_term.App
      (local_family [ Ext_env.level_type0 ], Ext_env.nat)
  in
  let nil_nat =
    Ext_term.App (nil_const Ext_env.level_type0, Ext_env.nat)
  in
  let cons_nat head tail =
    Ext_env.apps (cons_const Ext_env.level_type0) [ Ext_env.nat; head; tail ]
  in
  let list_rec_nat =
    list_rec_const [ Ext_env.level_type0; Ext_env.level_type0 ]
  in
  let list_motive = Ext_term.Lam (list_nat, Ext_env.nat) in
  let list_cons_case =
    Ext_term.Lam
      ( Ext_env.nat,
        Ext_term.Lam
          (list_nat, Ext_term.Lam (Ext_env.nat, Ext_term.BVar 0)) )
  in
  let list_rec_nil =
    Ext_env.apps list_rec_nat
      [ Ext_env.nat; list_motive; Ext_env.nat_zero; list_cons_case; nil_nat ]
  in
  assert_term_result "recursor List-like nil iota" Ext_env.nat_zero
    (Ext_typecheck.whnf list_env Ext_typecheck.empty_context list_rec_nil);
  assert_typecheck_ok "recursor List-like nil checks through iota"
    (Ext_typecheck.check list_env Ext_typecheck.empty_context list_rec_nil
       Ext_env.nat);
  let list_rec_cons =
    Ext_env.apps list_rec_nat
      [
        Ext_env.nat;
        list_motive;
        Ext_env.nat_zero;
        list_cons_case;
        cons_nat Ext_env.nat_zero nil_nat;
      ]
  in
  assert_term_result "recursor List-like cons iota" Ext_env.nat_zero
    (Ext_typecheck.whnf list_env Ext_typecheck.empty_context list_rec_cons);
  assert_typecheck_ok "recursor List-like cons checks through iota"
    (Ext_typecheck.check list_env Ext_typecheck.empty_context list_rec_cons
       Ext_env.nat);

  let indexed_name = make_name [ "Indexed" ] in
  let indexed_zero_name = make_name [ "Indexed"; "zero" ] in
  let indexed_succ_name = make_name [ "Indexed"; "succ" ] in
  let indexed_rec_name = make_name [ "Indexed"; "rec" ] in
  let indexed_family = local_family [] in
  let indexed_at value = Ext_term.App (indexed_family, value) in
  let indexed_zero =
    constructor_spec indexed_zero_name (indexed_at Ext_env.nat_zero)
  in
  let indexed_succ =
    constructor_spec indexed_succ_name
      (Ext_term.Pi
         ( Ext_env.nat,
           Ext_term.Pi
             ( indexed_at (Ext_term.BVar 0),
               indexed_at (Ext_env.nat_succ (Ext_term.BVar 1)) ) ))
  in
  let indexed_rules = { Ext_cert.minor_start = 1; major_index = 4 } in
  let indexed_placeholder =
    {
      Ext_cert.recursor_name = indexed_rec_name;
      recursor_universe_params = [];
      recursor_ty = Ext_term.Sort Ext_level.Zero;
      recursor_rules = indexed_rules;
    }
  in
  let indexed_recursor_ty =
    match
      Ext_typecheck.expected_recursor_type Ext_bytes.Declarations 0 0 [] []
        [ binder_type Ext_env.nat ] Ext_env.level_type0
        [ indexed_zero; indexed_succ ] indexed_placeholder
    with
    | Ok ty -> ty
    | Error _ -> failwith "failed to construct indexed recursor fixture"
  in
  let indexed_recursor =
    { indexed_placeholder with Ext_cert.recursor_ty = indexed_recursor_ty }
  in
  let indexed_decl =
    declaration_fixture Ext_cert.Inductive
      (Ext_cert.InductiveDecl
         {
           decl_name = indexed_name;
           decl_universe_params = [];
           decl_universe_constraints = [];
           ind_params = [];
           ind_indices = [ binder_type Ext_env.nat ];
           ind_sort = Ext_env.level_type0;
           ind_constructors = [ indexed_zero; indexed_succ ];
           ind_recursor = Some indexed_recursor;
         })
  in
  let indexed_env =
    assert_declaration_check_ok "recursor accepts indexed family"
      (Ext_typecheck.check_declarations [ indexed_decl ])
  in
  let indexed_zero_term = local_generated indexed_zero_name [] in
  let indexed_succ_term index previous =
    Ext_env.apps (local_generated indexed_succ_name []) [ index; previous ]
  in
  let indexed_motive =
    Ext_term.Lam
      ( Ext_env.nat,
        Ext_term.Lam (indexed_at (Ext_term.BVar 0), Ext_env.nat) )
  in
  let indexed_step =
    Ext_term.Lam
      ( Ext_env.nat,
        Ext_term.Lam
          ( indexed_at (Ext_term.BVar 0),
            Ext_term.Lam (Ext_env.nat, Ext_term.BVar 0) ) )
  in
  let indexed_rec = local_generated indexed_rec_name [] in
  let indexed_rec_zero =
    Ext_env.apps indexed_rec
      [
        indexed_motive;
        Ext_env.nat_zero;
        indexed_step;
        Ext_env.nat_zero;
        indexed_zero_term;
      ]
  in
  assert_term_result "indexed recursor zero iota" Ext_env.nat_zero
    (Ext_typecheck.whnf indexed_env Ext_typecheck.empty_context
       indexed_rec_zero);
  let indexed_rec_succ =
    Ext_env.apps indexed_rec
      [
        indexed_motive;
        Ext_env.nat_zero;
        indexed_step;
        Ext_env.nat_succ Ext_env.nat_zero;
        indexed_succ_term Ext_env.nat_zero indexed_zero_term;
      ]
  in
  assert_term_result "indexed recursor succ iota" Ext_env.nat_zero
    (Ext_typecheck.whnf indexed_env Ext_typecheck.empty_context
       indexed_rec_succ);

  let even_name = make_name [ "Mutual"; "Even" ] in
  let odd_name = make_name [ "Mutual"; "Odd" ] in
  let even_zero_name = make_name [ "Mutual"; "Even"; "zero" ] in
  let even_step_name = make_name [ "Mutual"; "Even"; "step" ] in
  let odd_step_name = make_name [ "Mutual"; "Odd"; "step" ] in
  let even_rec_name = make_name [ "Mutual"; "Even"; "rec" ] in
  let odd_rec_name = make_name [ "Mutual"; "Odd"; "rec" ] in
  let mutual_family_const name =
    Ext_term.Const (Ext_term.LocalGenerated { decl_index = 0; name }, [])
  in
  let even_family = mutual_family_const even_name in
  let odd_family = mutual_family_const odd_name in
  let even_zero = constructor_spec even_zero_name even_family in
  let even_step =
    constructor_spec even_step_name (Ext_term.Pi (odd_family, even_family))
  in
  let odd_step =
    constructor_spec odd_step_name (Ext_term.Pi (even_family, odd_family))
  in
  let mutual_rules = { Ext_cert.minor_start = 2; major_index = 5 } in
  let placeholder name =
    {
      Ext_cert.recursor_name = name;
      recursor_universe_params = [];
      recursor_ty = Ext_term.Sort Ext_level.Zero;
      recursor_rules = mutual_rules;
    }
  in
  let base_mutuals =
    [
      {
        Ext_cert.mutual_name = even_name;
        mutual_params = [];
        mutual_indices = [];
        mutual_sort = Ext_env.level_type0;
        mutual_constructors = [ even_zero; even_step ];
        mutual_recursor = Some (placeholder even_rec_name);
      };
      {
        Ext_cert.mutual_name = odd_name;
        mutual_params = [];
        mutual_indices = [];
        mutual_sort = Ext_env.level_type0;
        mutual_constructors = [ odd_step ];
        mutual_recursor = Some (placeholder odd_rec_name);
      };
    ]
  in
  let mutual_recursor target_index name =
    let recursor = placeholder name in
    match
      Ext_typecheck.expected_mutual_recursor_type Ext_bytes.Declarations 0 0
        [] base_mutuals target_index recursor
    with
    | Ok ty -> { recursor with Ext_cert.recursor_ty = ty }
    | Error _ -> failwith "failed to construct mutual recursor fixture"
  in
  let mutuals =
    match base_mutuals with
    | [ even; odd ] ->
        [
          {
            even with
            Ext_cert.mutual_recursor =
              Some (mutual_recursor 0 even_rec_name);
          };
          {
            odd with
            Ext_cert.mutual_recursor = Some (mutual_recursor 1 odd_rec_name);
          };
        ]
    | _ -> failwith "invalid mutual recursor fixture"
  in
  let mutual_decl =
    declaration_fixture Ext_cert.Mutual_inductive
      (Ext_cert.MutualInductiveBlockDecl
         {
           decl_name = make_name [ "Mutual" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           mutual_inductives = mutuals;
         })
  in
  let mutual_env =
    assert_declaration_check_ok "recursor accepts direct mutual block"
      (Ext_typecheck.check_declarations [ mutual_decl ])
  in
  let motive family = Ext_term.Lam (family, Ext_env.nat) in
  let keep_ih family =
    Ext_term.Lam (family, Ext_term.Lam (Ext_env.nat, Ext_term.BVar 0))
  in
  let even_zero_term = mutual_family_const even_zero_name in
  let odd_step_term value =
    Ext_term.App (mutual_family_const odd_step_name, value)
  in
  let even_step_term value =
    Ext_term.App (mutual_family_const even_step_name, value)
  in
  let mutual_args major =
    [
      motive even_family;
      motive odd_family;
      Ext_env.nat_zero;
      keep_ih odd_family;
      keep_ih even_family;
      major;
    ]
  in
  let mutual_zero =
    Ext_env.apps (mutual_family_const even_rec_name)
      (mutual_args even_zero_term)
  in
  assert_term_result "mutual recursor base iota" Ext_env.nat_zero
    (Ext_typecheck.whnf mutual_env Ext_typecheck.empty_context mutual_zero);
  let mutual_cross =
    Ext_env.apps (mutual_family_const even_rec_name)
      (mutual_args
         (even_step_term (odd_step_term even_zero_term)))
  in
  assert_term_result "mutual recursor cross-family iota" Ext_env.nat_zero
    (Ext_typecheck.whnf mutual_env Ext_typecheck.empty_context mutual_cross);
  assert_typecheck_ok "mutual recursor cross-family iota type checks"
    (Ext_typecheck.check mutual_env Ext_typecheck.empty_context mutual_cross
       Ext_env.nat);

  let nested_bytes =
    read_binary_file
      (Filename.concat (root_dir ())
         "test/fixtures/conformance/nested-v0.2.npcert")
  in
  let nested_decoded = decode_module_bytes "nested recursor fixture" nested_bytes in
  let nested_env =
    assert_declaration_check_ok "recursor accepts generated nested family"
      (Ext_typecheck.check_declarations nested_decoded.Ext_cert.declaration_table)
  in
  let level = Ext_env.level_type0 in
  let generated decl_index name =
    Ext_term.Const
      (Ext_term.LocalGenerated { decl_index; name = make_name name }, [ level ])
  in
  let list_family =
    Ext_term.Const (Ext_term.Local { decl_index = 0 }, [ level ])
  in
  let rose_family =
    Ext_term.Const (Ext_term.Local { decl_index = 1 }, [ level ])
  in
  let rose_nat = Ext_term.App (rose_family, Ext_env.nat) in
  let list_rose_nat = Ext_term.App (list_family, rose_nat) in
  let empty_children =
    Ext_term.App (generated 0 [ "List"; "nil" ], rose_nat)
  in
  let node =
    Ext_env.apps (generated 1 [ "Rose"; "node" ])
      [ Ext_env.nat; Ext_env.nat_zero; empty_children ]
  in
  let motive = Ext_term.Lam (rose_nat, Ext_env.nat) in
  let minor =
    Ext_term.Lam
      (Ext_env.nat, Ext_term.Lam (list_rose_nat, Ext_env.nat_zero))
  in
  let nested_recursor =
    Ext_term.Const
      ( Ext_term.LocalGenerated
          { decl_index = 1; name = make_name [ "Rose"; "rec" ] },
        [ level; level ] )
  in
  let nested_iota =
    Ext_env.apps nested_recursor [ Ext_env.nat; motive; minor; node ]
  in
  assert_term_result "nested recursor node iota" Ext_env.nat_zero
    (Ext_typecheck.whnf nested_env Ext_typecheck.empty_context nested_iota);
  assert_typecheck_ok "nested recursor node iota type checks"
    (Ext_typecheck.check nested_env Ext_typecheck.empty_context nested_iota
       Ext_env.nat)

let run_subst_tests () =
  let section = Ext_bytes.Declarations in
  let offset = 17 in
  let shift term amount cutoff =
    Ext_typecheck.shift section offset term amount cutoff
  in
  let substitute term target replacement =
    Ext_typecheck.substitute section offset term target replacement
  in
  let instantiate body value = Ext_typecheck.instantiate section offset body value in
  let nested =
    Ext_term.Lam
      ( Ext_term.BVar 1,
        Ext_term.Pi
          ( Ext_term.App (Ext_term.BVar 2, Ext_term.BVar 0),
            Ext_term.Let
              ( Ext_term.BVar 3,
                Ext_term.BVar 1,
                Ext_term.App (Ext_term.BVar 4, Ext_term.BVar 0) ) ) )
  in
  let shifted_nested =
    Ext_term.Lam
      ( Ext_term.BVar 2,
        Ext_term.Pi
          ( Ext_term.App (Ext_term.BVar 3, Ext_term.BVar 0),
            Ext_term.Let
              ( Ext_term.BVar 4,
                Ext_term.BVar 1,
                Ext_term.App (Ext_term.BVar 5, Ext_term.BVar 0) ) ) )
  in
  assert_term_result "subst shifts nested binders by Rust reference rules"
    shifted_nested (shift nested 1 0);
  assert_term_result "subst shift round trip preserves nested binders" nested
    (match shift nested 1 0 with
    | Error error -> Error error
    | Ok shifted -> shift shifted (-1) 0);

  let replacement = Ext_term.App (Ext_term.BVar 0, Ext_term.BVar 2) in
  assert_term_result "subst app replaces both boundaries"
    (Ext_term.App
       ( replacement,
         Ext_term.App (replacement, Ext_term.BVar 0) ))
    (substitute
       (Ext_term.App (Ext_term.BVar 0, Ext_term.App (Ext_term.BVar 0, Ext_term.BVar 1)))
       0 replacement);
  assert_term_result "subst lam preserves bound bvar and lifts replacement"
    (Ext_term.Lam
       ( replacement,
         Ext_term.App
           ( Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 3),
             Ext_term.BVar 0 ) ))
    (substitute
       (Ext_term.Lam
          ( Ext_term.BVar 0,
            Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 0) ))
       0 replacement);
  assert_term_result "subst pi preserves bound bvar and lifts replacement"
    (Ext_term.Pi
       ( replacement,
         Ext_term.App
           ( Ext_term.BVar 0,
             Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 3) ) ))
    (substitute
       (Ext_term.Pi
          ( Ext_term.BVar 0,
            Ext_term.App (Ext_term.BVar 0, Ext_term.BVar 1) ))
       0 replacement);
  assert_term_result "subst let preserves body binder boundary"
    (Ext_term.Let
       ( replacement,
         replacement,
         Ext_term.App
           ( Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 3),
             Ext_term.BVar 0 ) ))
    (substitute
       (Ext_term.Let
          ( Ext_term.BVar 0,
            Ext_term.BVar 0,
            Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 0) ))
       0 replacement);
  assert_term_result "subst instantiate removes the top binder"
    (Ext_term.App (Ext_term.BVar 1, Ext_term.BVar 1))
    (instantiate
       (Ext_term.App (Ext_term.BVar 2, Ext_term.BVar 0))
       (Ext_term.BVar 1));

  assert_typecheck_ok "subst preserves well-scoped beta body after instantiate"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context
       (Ext_term.Let (Ext_env.nat, Ext_env.nat_zero, Ext_term.BVar 0))
       Ext_env.nat);
  assert_typecheck_rejects "subst rejects negative bvar before reduction"
    "type_mismatch" "invalid_bvar"
    (shift (Ext_term.BVar (-1)) 1 0);
  assert_typecheck_rejects "subst rejects negative shift result"
    "type_mismatch" "invalid_bvar"
    (shift (Ext_term.BVar 0) (-1) 0);
  assert_typecheck_rejects "subst rejects negative cutoff"
    "type_mismatch" "invalid_bvar"
    (shift (Ext_term.BVar 0) 1 (-1));
  assert_typecheck_rejects "subst rejects negative target"
    "type_mismatch" "invalid_bvar"
    (substitute (Ext_term.BVar 0) (-1) Ext_env.nat_zero)

let run_reduce_tests () =
  let nat = Ext_env.nat in
  let nat_zero = Ext_env.nat_zero in
  let nat_rec level =
    Ext_env.builtin_const "Nat.rec" [ level ]
  in
  let whnf term =
    Ext_typecheck.whnf Ext_env.empty Ext_typecheck.empty_context term
  in
  let beta_term = Ext_term.App (Ext_term.Lam (nat, Ext_term.BVar 0), nat_zero) in
  assert_term_result "reduce beta lambda application" nat_zero (whnf beta_term);
  assert_term_result "reduce zeta let value" nat_zero
    (whnf (Ext_term.Let (nat, nat_zero, Ext_term.BVar 0)));

  let alias_decl =
    declaration_fixture Ext_cert.Definition
      (Ext_cert.DefDecl
         {
           decl_name = make_name [ "AliasNatReduce" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
           decl_value = nat;
           decl_reducibility = Ext_cert.Reducible;
         })
  in
  let alias_env =
    assert_declaration_check_ok "reduce adds reducible alias"
      (Ext_typecheck.check_declarations [ alias_decl ])
  in
  let alias_ref = Ext_term.Const (Ext_term.Local { decl_index = 0 }, []) in
  assert_term_result "reduce delta unfolds reducible definition" nat
    (Ext_typecheck.whnf alias_env Ext_typecheck.empty_context alias_ref);
  assert_typecheck_ok "reduce delta supports checking through reducible definition"
    (Ext_typecheck.check alias_env Ext_typecheck.empty_context nat_zero alias_ref);

  let theorem_decl =
    declaration_fixture Ext_cert.Theorem
      (Ext_cert.TheoremDecl
         {
           decl_name = make_name [ "TheoremAliasReduce" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
           decl_proof = nat;
           decl_opacity = Ext_cert.Opaque;
         })
  in
  let theorem_env =
    assert_declaration_check_ok "reduce adds opaque theorem alias"
      (Ext_typecheck.check_declarations [ theorem_decl ])
  in
  let theorem_ref = Ext_term.Const (Ext_term.Local { decl_index = 0 }, []) in
  assert_typecheck_rejects "reduce forbids theorem proof unfolding"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check theorem_env Ext_typecheck.empty_context nat_zero theorem_ref);

  let opaque_decl =
    declaration_fixture Ext_cert.Definition
      (Ext_cert.DefDecl
         {
           decl_name = make_name [ "OpaqueAliasReduce" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
           decl_value = nat;
           decl_reducibility = Ext_cert.Opaque_reducibility;
         })
  in
  let opaque_env =
    assert_declaration_check_ok "reduce adds opaque definition alias"
      (Ext_typecheck.check_declarations [ opaque_decl ])
  in
  let opaque_ref = Ext_term.Const (Ext_term.Local { decl_index = 0 }, []) in
  assert_typecheck_rejects "reduce forbids opaque definition unfolding"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check opaque_env Ext_typecheck.empty_context nat_zero opaque_ref);

  let motive = Ext_term.Lam (nat, nat) in
  let step = Ext_term.Lam (nat, Ext_term.Lam (nat, Ext_term.BVar 1)) in
  let recursor_zero =
    Ext_env.apps (nat_rec Ext_env.level_type0) [ motive; nat_zero; step; nat_zero ]
  in
  assert_term_result "reduce Nat.rec zero iota" nat_zero (whnf recursor_zero);
  assert_typecheck_ok "reduce Nat.rec zero checks through iota"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context recursor_zero nat);
  let recursor_succ =
    Ext_env.apps (nat_rec Ext_env.level_type0)
      [ motive; nat_zero; step; Ext_env.nat_succ nat_zero ]
  in
  assert_term_result "reduce Nat.rec succ iota" nat_zero (whnf recursor_succ);
  assert_typecheck_ok "reduce Nat.rec succ checks through iota"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context recursor_succ nat);

  assert_typecheck_rejects "reduce fuel exhaustion uses conversion failure kind"
    "conversion_failure" "resource_limit"
    (Ext_typecheck.whnf_with_fuel_budget ~fuel_budget:0 Ext_env.empty
       Ext_typecheck.empty_context nat_zero);
  assert_typecheck_rejects "reduce negative fuel budget is deterministic"
    "conversion_failure" "resource_limit"
    (Ext_typecheck.whnf_with_fuel_budget ~fuel_budget:(-1) Ext_env.empty
       Ext_typecheck.empty_context nat_zero);
  assert_typecheck_rejects "reduce recursive fuel exhaustion is deterministic"
    "conversion_failure" "resource_limit"
    (Ext_typecheck.whnf_with_fuel_budget ~fuel_budget:1 Ext_env.empty
       Ext_typecheck.empty_context beta_term);
  let reconstruction_fuel = ref 2 in
  assert_typecheck_rejects "mutual reconstruction work is fuel bounded"
    "conversion_failure" "resource_limit"
    (Ext_typecheck.spend_fuel_units Ext_bytes.Declarations 0
       reconstruction_fuel 3);
  assert_int_equal "rejected reconstruction keeps fuel" 2 !reconstruction_fuel;
  (match
     Ext_typecheck.spend_fuel_units Ext_bytes.Declarations 0
       reconstruction_fuel 2
   with
  | Ok () -> assert_int_equal "accepted reconstruction spends fuel" 0 !reconstruction_fuel
  | Error _ -> failwith "bounded mutual reconstruction fuel must be spendable")

let run_defeq_tests () =
  let nat = Ext_env.nat in
  let nat_zero = Ext_env.nat_zero in
  let beta_term = Ext_term.App (Ext_term.Lam (nat, Ext_term.BVar 0), nat_zero) in
  let zeta_term = Ext_term.Let (nat, nat_zero, Ext_term.BVar 0) in
  let defeq ?(env = Ext_env.empty) ?(context = Ext_typecheck.empty_context) lhs rhs =
    Ext_typecheck.is_defeq env context lhs rhs
  in
  assert_defeq "defeq beta equals contractum" true (defeq beta_term nat_zero);
  assert_defeq "defeq zeta equals body instantiation" true (defeq zeta_term nat_zero);

  let alias_decl =
    declaration_fixture Ext_cert.Definition
      (Ext_cert.DefDecl
         {
           decl_name = make_name [ "AliasNatDefeq" ];
           decl_universe_params = [];
           decl_universe_constraints = [];
           decl_ty = Ext_term.Sort Ext_env.level_type0;
           decl_value = nat;
           decl_reducibility = Ext_cert.Reducible;
         })
  in
  let alias_env =
    assert_declaration_check_ok "defeq adds reducible alias"
      (Ext_typecheck.check_declarations [ alias_decl ])
  in
  let alias_ref = Ext_term.Const (Ext_term.Local { decl_index = 0 }, []) in
  assert_defeq "defeq delta unfolds reducible definition" true
    (defeq ~env:alias_env alias_ref nat);

  let normalized_level = Ext_level.Max (Ext_level.Zero, Ext_env.level_type0) in
  assert_defeq "defeq normalizes sort levels" true
    (defeq (Ext_term.Sort normalized_level) (Ext_term.Sort Ext_env.level_type0));
  assert_defeq "defeq normalizes const levels" true
    (defeq (Ext_env.builtin_const "Eq" [ normalized_level ])
       (Ext_env.builtin_const "Eq" [ Ext_env.level_type0 ]));

  let eq_path =
    Filename.concat (root_dir ())
      "../../testdata/package/proofs/vendor/npa-std/Std/Logic/Eq/certificate.npcert"
  in
  let eq_module = load_single_import_entry "defeq Eq import fixture" eq_path in
  let eq_request =
    decoded_import_request "defeq Eq import request"
      eq_module.Ext_import_store.import_entry.Ext_import.module_name
      eq_module.Ext_import_store.import_entry.Ext_import.export_hash None
  in
  let eq_import_environment =
    assert_import_environment_ok "defeq Eq import environment" [ eq_module ]
      eq_request
  in
  let eq_env = Ext_env.of_imports eq_import_environment in
  let eq_import =
    single_resolved_import "defeq Eq resolved import" eq_import_environment
  in
  let imported_eq_const dotted levels =
    let imported_name = make_name (Ext_env.split_dotted dotted) in
    let exports =
      eq_import.Ext_import_store.resolved_public_environment.public_exports
    in
    let export =
      match
        List.find_opt
          (fun (export : Ext_import_store.public_export) ->
            Ext_name.equal export.Ext_import_store.public_export_name
              imported_name)
          exports
      with
      | Some export -> export
      | None ->
          failwith
            ("missing imported Eq export " ^ dotted ^ " among "
            ^ String.concat ","
                (List.map
                   (fun (export : Ext_import_store.public_export) ->
                     Ext_name.to_string
                       export.Ext_import_store.public_export_name)
                   exports))
    in
    Ext_term.Const
      ( Ext_term.Imported
          {
            import_index = 0;
            name = imported_name;
            decl_interface_hash =
              export.Ext_import_store.public_decl_interface_hash;
          },
        levels )
  in
  assert_defeq "defeq authenticates imported Eq as builtin" true
    (defeq ~env:eq_env
       (imported_eq_const "Eq" [ Ext_level.Zero ])
       (Ext_env.builtin_const "Eq" [ Ext_level.Zero ]));
  assert_defeq "defeq authenticates imported Eq.refl as builtin" true
    (defeq ~env:eq_env
       (imported_eq_const "Eq.refl" [ Ext_level.Zero ])
       (Ext_env.builtin_const "Eq.refl" [ Ext_level.Zero ]));
  let wrong_eq_import =
    {
      eq_import with
      Ext_import_store.resolved_module_name =
        make_name [ "Not"; "Std"; "Logic"; "Eq" ];
    }
  in
  let wrong_eq_env =
    Ext_env.of_imports
      { Ext_import_store.resolved_imports = [ wrong_eq_import ] }
  in
  assert_defeq "defeq does not bridge an Eq-shaped untrusted module" false
    (defeq ~env:wrong_eq_env
       (imported_eq_const "Eq" [ Ext_level.Zero ])
       (Ext_env.builtin_const "Eq" [ Ext_level.Zero ]));

  let fn_ty = Ext_term.Pi (nat, nat) in
  let fn_context = Ext_typecheck.push_assumption Ext_typecheck.empty_context fn_ty in
  let open_app = Ext_term.App (Ext_term.BVar 0, nat_zero) in
  assert_defeq "defeq recurses through app" true
    (defeq ~context:fn_context open_app open_app);
  assert_defeq "defeq recurses through bvar" true
    (defeq ~context:fn_context (Ext_term.BVar 0) (Ext_term.BVar 0));
  assert_defeq "defeq recurses through pi" true
    (defeq (Ext_term.Pi (nat, Ext_term.BVar 0))
       (Ext_term.Pi (nat, Ext_term.BVar 0)));
  assert_defeq "defeq recurses through lambda" true
    (defeq (Ext_term.Lam (nat, Ext_term.BVar 0))
       (Ext_term.Lam (nat, Ext_term.BVar 0)));
  assert_defeq "defeq returns deterministic false for different constructors" false
    (defeq nat_zero (Ext_env.nat_succ nat_zero));
  assert_typecheck_rejects "defeq negative type mismatch rejects"
    "type_mismatch" "type_mismatch"
    (Ext_typecheck.check Ext_env.empty Ext_typecheck.empty_context nat_zero
       (Ext_env.nat_succ nat_zero));

  assert_defeq "defeq repeated call without cache remains stable" true
    (defeq beta_term nat_zero);
  assert_defeq "defeq repeated call without cache remains stable again" true
    (defeq beta_term nat_zero);
  assert_typecheck_rejects "defeq fuel exhaustion uses conversion failure kind"
    "conversion_failure" "resource_limit"
    (Ext_typecheck.is_defeq_with_fuel_budget ~fuel_budget:0 Ext_env.empty
       Ext_typecheck.empty_context beta_term nat_zero)

let run_hash_encoder_tests () =
  let empty_module = encode_module [] [] [] [] [] in
  let empty_decoded = decode_module_bytes "empty hash fixture" empty_module in
  assert_canonical_bytes "empty full certificate re-encoding" empty_module
    (Ext_canonical.encode_module_bytes empty_decoded);
  assert_canonical_bytes "empty export payload" (encode_export_block [])
    (Ext_canonical.encode_export_block empty_decoded);
  assert_canonical_bytes "empty axiom report payload" (encode_axiom_report [] [])
    (Ext_canonical.encode_axiom_report empty_decoded.Ext_cert.name_table
       empty_decoded.Ext_cert.axiom_report);
  let empty_export_payload = assert_ok "empty export payload for domain"
      (Ext_canonical.encode_export_block empty_decoded)
  in
  assert_bool "domain label affects export hash"
    (Ext_canonical.hash_with_domain Ext_canonical.domain_module_export empty_export_payload
    <> Ext_canonical.hash_with_domain "NPA-MODULE-EXPORT-X" empty_export_payload);

  let axiom_module = encode_minimal_module [ minimal_axiom_decl ] [ minimal_export_entry ] in
  let axiom_decoded = decode_module_bytes "axiom hash fixture" axiom_module in
  assert_canonical_bytes "axiom full certificate re-encoding" axiom_module
    (Ext_canonical.encode_module_bytes axiom_decoded);
  assert_canonical_bytes "axiom export payload" (encode_export_block [ minimal_export_entry ])
    (Ext_canonical.encode_export_block axiom_decoded);
  let axiom_decl = first_declaration axiom_decoded in
  let sort_hash =
    assert_ok "sort term hash"
      (Ext_canonical.term_hash Ext_bytes.Term_table axiom_decl.Ext_cert.offset
         axiom_decoded.Ext_cert.name_table Ext_term.(Sort Ext_level.Zero))
  in
  let expected_axiom_iface =
    one_byte 0x00 ^ encode_name [ "A" ] ^ encode_uvar_int 0 ^ sort_hash
    ^ encode_dependency_entries []
  in
  assert_canonical_bytes "axiom declaration interface payload" expected_axiom_iface
    (Ext_canonical.declaration_interface_payload axiom_decoded.Ext_cert.name_table
       axiom_decoded.Ext_cert.level_table axiom_decoded.Ext_cert.term_table axiom_decl.Ext_cert.payload
       axiom_decl.Ext_cert.dependencies axiom_decl.Ext_cert.axiom_dependencies);
  let axiom_iface_hash =
    Ext_canonical.hash_with_domain Ext_canonical.domain_decl_interface expected_axiom_iface
  in
  assert_canonical_bytes "axiom declaration certificate payload"
    (axiom_iface_hash ^ encode_axiom_refs [])
    (Ext_canonical.declaration_certificate_payload axiom_decoded.Ext_cert.name_table
       axiom_decoded.Ext_cert.level_table axiom_decoded.Ext_cert.term_table
       axiom_decl.Ext_cert.payload axiom_iface_hash axiom_decl.Ext_cert.dependencies
       axiom_decl.Ext_cert.axiom_dependencies);

  let imported_ref = encode_global_imported 0 1 (hash_bytes 0x55) in
  let theorem_decl_bytes =
    encode_decl_cert
      (encode_theorem_decl_payload 0x02 0 [] 0 1)
      [ (imported_ref, hash_bytes 0x55) ] [] (hash_bytes 0x41) (hash_bytes 0x42)
  in
  let theorem_export =
    encode_export_entry_full 0 0x02 [] 0 None (hash_bytes 0x31) None None
      (Some encode_opacity_opaque) (hash_bytes 0x32) []
  in
  let theorem_module =
    encode_module ~imports:[ ([ "Dep" ], hash_bytes 0x71, None) ]
      [ [ "A" ]; [ "Imported" ] ] [ encode_level_zero ]
      [ encode_term_sort 0; encode_term_const imported_ref [] ]
      [ theorem_decl_bytes ] [ theorem_export ]
  in
  let theorem_decoded = decode_module_bytes "theorem hash fixture" theorem_module in
  assert_canonical_bytes "theorem export payload" (encode_export_block [ theorem_export ])
    (Ext_canonical.encode_export_block theorem_decoded);
  let theorem_decl = first_declaration theorem_decoded in
  let theorem_sort_hash =
    assert_ok "theorem sort term hash"
      (Ext_canonical.term_hash Ext_bytes.Term_table theorem_decl.Ext_cert.offset
         theorem_decoded.Ext_cert.name_table Ext_term.(Sort Ext_level.Zero))
  in
  let expected_theorem_iface =
    one_byte 0x02 ^ encode_name [ "A" ] ^ encode_uvar_int 0 ^ theorem_sort_hash
    ^ encode_opacity_opaque ^ encode_dependency_entries [] ^ encode_axiom_refs []
  in
  assert_canonical_bytes "theorem declaration interface payload" expected_theorem_iface
    (Ext_canonical.declaration_interface_payload theorem_decoded.Ext_cert.name_table
       theorem_decoded.Ext_cert.level_table theorem_decoded.Ext_cert.term_table
       theorem_decl.Ext_cert.payload theorem_decl.Ext_cert.dependencies
       theorem_decl.Ext_cert.axiom_dependencies);
  let theorem_proof =
    match theorem_decl.Ext_cert.payload with
    | Ext_cert.TheoremDecl { decl_proof; _ } -> decl_proof
    | _ -> failwith "expected theorem declaration"
  in
  let theorem_proof_hash =
    assert_ok "theorem proof term hash"
      (Ext_canonical.term_hash Ext_bytes.Term_table theorem_decl.Ext_cert.offset
         theorem_decoded.Ext_cert.name_table theorem_proof)
  in
  let theorem_iface_hash =
    Ext_canonical.hash_with_domain Ext_canonical.domain_decl_interface expected_theorem_iface
  in
  assert_canonical_bytes "theorem declaration certificate payload"
    (theorem_iface_hash ^ theorem_proof_hash
    ^ encode_dependency_entries [ (imported_ref, hash_bytes 0x55) ])
    (Ext_canonical.declaration_certificate_payload theorem_decoded.Ext_cert.name_table
       theorem_decoded.Ext_cert.level_table theorem_decoded.Ext_cert.term_table
       theorem_decl.Ext_cert.payload theorem_iface_hash theorem_decl.Ext_cert.dependencies
       theorem_decl.Ext_cert.axiom_dependencies);

  let import_decl =
    encode_decl_cert
      (encode_def_decl_payload 0x01 0 [] 0 1 `Reducible)
      [ (imported_ref, hash_bytes 0x55) ] [] (hash_bytes 0x56) (hash_bytes 0x57)
  in
  let import_export =
    encode_export_entry_full 0 0x01 [] 0 (Some 1) (hash_bytes 0x31)
      (Some (hash_bytes 0x61)) (Some (encode_reducibility `Reducible)) None
      (hash_bytes 0x32) []
  in
  let import_module =
    encode_module ~imports:[ ([ "Dep" ], hash_bytes 0x71, None) ] [ [ "A" ]; [ "Imported" ] ]
      [ encode_level_zero ]
      [ encode_term_sort 0; encode_term_const imported_ref [] ]
      [ import_decl ] [ import_export ]
  in
  let import_decoded = decode_module_bytes "import hash fixture" import_module in
  assert_canonical_bytes "import dependency payload"
    (encode_dependency_entries [ (imported_ref, hash_bytes 0x55) ])
    (Ext_canonical.encode_dependency_entries Ext_bytes.Declarations 0
       import_decoded.Ext_cert.name_table (first_declaration import_decoded).Ext_cert.dependencies);
  assert_canonical_bytes "import export payload" (encode_export_block [ import_export ])
    (Ext_canonical.encode_export_block import_decoded);

  let inductive_decl =
    encode_decl_cert (encode_inductive_decl_payload 0x03 0 [] [] [] 0 [ (1, 0) ] None) [] []
      (hash_bytes 0x81) (hash_bytes 0x82)
  in
  let inductive_export = encode_export_entry 0 0x03 [] 0 None [] in
  let inductive_module =
    encode_module [ [ "A" ]; [ "C" ] ] [ encode_level_zero ] [ encode_term_sort 0 ]
      [ inductive_decl ] [ inductive_export ]
  in
  let inductive_decoded = decode_module_bytes "inductive hash fixture" inductive_module in
  ignore
    (assert_ok "inductive declaration interface payload"
       (Ext_canonical.declaration_interface_payload inductive_decoded.Ext_cert.name_table
          inductive_decoded.Ext_cert.level_table inductive_decoded.Ext_cert.term_table
          (first_declaration inductive_decoded).Ext_cert.payload
          (first_declaration inductive_decoded).Ext_cert.dependencies
          (first_declaration inductive_decoded).Ext_cert.axiom_dependencies));
  assert_canonical_bytes "inductive export payload" (encode_export_block [ inductive_export ])
    (Ext_canonical.encode_export_block inductive_decoded);

  let assert_golden_module label path =
    let bytes = read_binary_file path in
    let fixture = golden_hash_fixture label in
    assert_int_equal (label ^ " golden byte length") fixture.golden_byte_len
      (String.length bytes);
    let decoded = decode_module_bytes (label ^ " golden") bytes in
    assert_equal (label ^ " stored export hash") fixture.golden_export_hash
      (hex_of_raw_hash decoded.Ext_cert.hashes.Ext_cert.export_hash);
    assert_equal (label ^ " stored axiom report hash") fixture.golden_axiom_report_hash
      (hex_of_raw_hash decoded.Ext_cert.hashes.Ext_cert.axiom_report_hash);
    assert_equal (label ^ " stored certificate hash") fixture.golden_certificate_hash
      (hex_of_raw_hash decoded.Ext_cert.hashes.Ext_cert.certificate_hash);
    assert_declaration_hashes label decoded;
    assert_canonical_hash (label ^ " encoded export hash") fixture.golden_export_hash
      (Ext_canonical.export_hash decoded);
    assert_canonical_hash (label ^ " encoded axiom report hash")
      fixture.golden_axiom_report_hash (Ext_canonical.axiom_report_hash decoded)
  in
  assert_golden_module "nat"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Nat/Basic/certificate.npcert");
  assert_golden_module "eq"
    (Filename.concat (root_dir ()) "../../testdata/package/npa-mathlib/vendor/npa-std/Std/Logic/Eq/certificate.npcert");

  let assert_versioned_reencoding label relative_path expected_version =
    let bytes = read_binary_file (Filename.concat (root_dir ()) relative_path) in
    let decoded = decode_module_bytes label bytes in
    assert_bool (label ^ " version")
      (decoded.Ext_cert.header.Ext_cert.version = expected_version);
    assert_canonical_bytes (label ^ " full certificate re-encoding") bytes
      (Ext_canonical.encode_module_bytes decoded);
    assert_declaration_hashes label decoded;
    (match Ext_canonical.verify_module_hashes bytes decoded with
    | Ok Ext_canonical.Module_hashes_ok -> ()
    | Ok (Ext_canonical.Module_hash_mismatch mismatch) ->
        failwith
          (label ^ ": unexpected module hash mismatch "
          ^ Ext_canonical.module_hash_role_kind_code
              mismatch.Ext_canonical.module_mismatch_role)
    | Error error ->
        failwith
          (label ^ ": unexpected hash decode error "
          ^ Ext_bytes.reason_code error.Ext_bytes.reason))
  in
  assert_versioned_reencoding "previous certificate"
    "../../testdata/package/npa-mathlib-downstream/vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert"
    Ext_cert.Previous;
  assert_versioned_reencoding "current certificate"
    "../../testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert"
    Ext_cert.Current

let run_checker_pipeline_tests () =
  let import_bytes =
    read_binary_file
      (Filename.concat (root_dir ())
         "../../testdata/package/npa-mathlib-downstream/vendor/npa-mathlib/Mathlib/Logic/Basic/certificate.npcert")
  in
  let leaf_bytes =
    read_binary_file
      (Filename.concat (root_dir ())
         "../../testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert")
  in
  let store =
    match Ext_import_store.from_source_free_certificates [ import_bytes ] with
    | Ok store -> store
    | Error _ -> failwith "checker pipeline failed to build import store"
  in
  match Ext_checker.check_normal store Ext_axiom.default_policy leaf_bytes with
  | Error _ -> failwith "checker pipeline unexpectedly rejected current leaf"
  | Ok checked ->
      assert_equal "checker pipeline module" "Downstream.MathlibBasic"
        (Ext_name.to_string (Ext_checker.module_name checked));
      assert_int_equal "checker pipeline declaration count" 1
        (Ext_checker.declarations_checked checked);
      let import_dir =
        Filename.concat (root_dir ())
          "../../testdata/package/npa-mathlib-downstream/vendor"
      in
      (match
         Ext_session.check_high_trust import_dir Ext_axiom.default_policy
           leaf_bytes
       with
      | Error _ -> failwith "checker high-trust session rejected valid DAG"
      | Ok session ->
          assert_int_equal "checker high-trust import count" 1
            (List.length session.Ext_session.checked_imports);
          assert_equal "checker high-trust leaf" "Downstream.MathlibBasic"
            (Ext_name.to_string
               (Ext_checker.module_name session.Ext_session.leaf)));
      let policy_path =
        Filename.concat (root_dir ()) "test/fixtures/axiom-policy.toml"
      in
      let cli =
        Ext_cli.run
          [
            "--cert";
            Filename.concat (root_dir ())
              "../../testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert";
            "--import-dir";
            import_dir;
            "--policy";
            policy_path;
            "--policy-hash";
            Ext_hash.sha256_prefixed_hex_of_string
              (read_binary_file policy_path);
            "--output";
            "json";
          ]
      in
      assert_int_equal "checker executable-shaped CLI exit" 0 cli.code;
      assert_equal "checker executable-shaped CLI stderr" "" cli.stderr;
      let assert_raw_identity label json =
        assert_contains (label ^ " schema")
          "\"schema\": \"npa.independent-checker.checker_raw_result.v1\""
          json;
        assert_contains (label ^ " checker id")
          "\"checker_id\": \"npa-checker-ext\"" json;
        assert_contains (label ^ " checker version")
          "\"checker_version\": \"0.2.0\"" json;
        assert_contains (label ^ " checker build hash")
          ("\"checker_build_hash\": \"" ^ Ext_result.checker_build_hash ^ "\"")
          json
      in
      assert_raw_identity "checker executable-shaped CLI" cli.stdout;
      assert_contains "checker executable-shaped CLI checked"
        "\"status\": \"checked\"" cli.stdout;
      assert_contains "checker executable-shaped CLI module"
        "\"module\": \"Downstream.MathlibBasic\"" cli.stdout;
      let policy_hash_mismatch =
        Ext_cli.run
          [
            "--cert";
            Filename.concat (root_dir ())
              "../../testdata/package/npa-mathlib-downstream/Downstream/MathlibBasic/certificate.npcert";
            "--import-dir";
            import_dir;
            "--policy";
            policy_path;
            "--policy-hash";
            "sha256:" ^ String.make 64 '0';
            "--output";
            "json";
          ]
      in
      assert_int_equal "checker policy hash mismatch exit" 1
        policy_hash_mismatch.code;
      assert_raw_identity "checker policy hash mismatch"
        policy_hash_mismatch.stdout;
      assert_contains "checker policy hash mismatch kind"
        "\"kind\": \"policy_input_error\"" policy_hash_mismatch.stdout;

      let boundary_dir =
        Filename.concat (root_dir ()) "test/fixtures/conformance"
      in
      let boundary_file name =
        read_binary_file (Filename.concat boundary_dir name)
      in
      let bad_provider =
        boundary_file "unchecked-provider-bad-v0.2.npcert"
      in
      let unpinned_leaf =
        boundary_file "unchecked-consumer-unpinned-v0.2.npcert"
      in
      let pinned_leaf =
        boundary_file "unchecked-consumer-pinned-v0.2.npcert"
      in
      (match
         Ext_checker.check_normal [] Ext_axiom.default_policy bad_provider
       with
      | Error (Ext_checker.Type_error _) -> ()
      | _ -> failwith "semantic boundary provider must fail direct checking");
      let unchecked_store =
        match
          Ext_import_store.from_source_free_certificates [ bad_provider ]
        with
        | Ok store -> store
        | Error _ -> failwith "semantic boundary import must hash-check"
      in
      (match
         Ext_checker.check_normal unchecked_store Ext_axiom.default_policy
           unpinned_leaf
       with
      | Ok checked ->
          assert_equal "normal boundary accepts unchecked public import"
            "Conformance.UncheckedConsumer"
            (Ext_name.to_string (Ext_checker.module_name checked))
      | Error _ ->
          failwith "normal mode must retain unchecked-import semantics");
      (match
         Ext_session.check_high_trust boundary_dir Ext_axiom.default_policy
           pinned_leaf
       with
      | Error (Ext_session.Check_error (Ext_checker.Type_error _)) -> ()
      | _ ->
          failwith
            "high-trust boundary must reject semantically invalid import");
      let permissive_policy =
        {
          Ext_axiom.default_policy with
          Ext_axiom.deny_sorry = false;
          Ext_axiom.deny_custom_axioms = false;
        }
      in
      (match
         Ext_checker.check_high_trust [] permissive_policy
           (boundary_file "forbidden-axiom-v0.2.npcert")
       with
      | Error (Ext_checker.Axiom_policy_error _) -> ()
      | _ ->
          failwith
            "high-trust checker must not permit axiom-denial overrides");

      let decoded_fixture name =
        decode_module_bytes name (boundary_file name)
      in
      let indexed = decoded_fixture "indexed-v0.2.npcert" in
      let mutual = decoded_fixture "mutual-v0.2.npcert" in
      let nested = decoded_fixture "nested-v0.2.npcert" in
      let checked_mutual =
        match
          Ext_checker.check_high_trust [] Ext_axiom.default_policy
            (boundary_file "mutual-v0.2.npcert")
        with
        | Ok checked -> checked
        | Error _ -> failwith "mutual cache provider must check"
      in
      let checked_imported_mutual =
        match
          Ext_checker.check_high_trust [ checked_mutual ]
            Ext_axiom.default_policy
            (boundary_file "imported-mutual-iota-v0.2.npcert")
        with
        | Ok checked -> checked
        | Error _ -> failwith "mutual cache consumer must check"
      in
      if Ext_checker.imported_recursor_cache_size checked_imported_mutual < 2
      then failwith "mutual iota must cache both family recursors";
      assert_int_equal "mutual iota reconstructs one shared block" 1
        (Ext_checker.imported_mutual_block_cache_size checked_imported_mutual);
      assert_bool "mutual iota runtimes share reconstructed family storage"
        (Ext_checker.imported_mutual_runtimes_share_families
           checked_imported_mutual);
      let request ?(certificate_hash = true) offset decoded =
        {
          Ext_cert.import_entry =
            {
              Ext_import.module_name =
                decoded.Ext_cert.header.Ext_cert.module_name;
              export_hash = decoded.Ext_cert.hashes.Ext_cert.export_hash;
              certificate_hash =
                (if certificate_hash then
                   Some decoded.Ext_cert.hashes.Ext_cert.certificate_hash
                 else None);
            };
          import_offset = offset;
        }
      in
      let candidate decoded =
        { Ext_session.bytes = ""; decoded }
      in
      let mutual_with_no_imports = { mutual with Ext_cert.imports = [] } in
      let indexed_depends_on_mutual =
        {
          indexed with
          Ext_cert.imports = [ request 11 mutual_with_no_imports ];
        }
      in
      let nested_depends_on_indexed =
        {
          nested with
          Ext_cert.imports = [ request 12 indexed_depends_on_mutual ];
        }
      in
      (match
         Ext_session.topological_plan
           [ candidate indexed_depends_on_mutual; candidate mutual_with_no_imports ]
           (candidate nested_depends_on_indexed)
       with
      | Ok [ first; second ] ->
          assert_equal "high-trust plan child first" "Conformance.EvenOdd"
            (Ext_name.to_string
               first.Ext_session.decoded.Ext_cert.header.Ext_cert.module_name);
          assert_equal "high-trust plan consumer second" "Conformance.Indexed"
            (Ext_name.to_string
               second.Ext_session.decoded.Ext_cert.header.Ext_cert.module_name)
      | _ -> failwith "high-trust plan must be deterministic child-first");
      let mutual_depends_on_indexed =
        {
          mutual with
          Ext_cert.imports = [ request 13 indexed_depends_on_mutual ];
        }
      in
      let indexed_cycle =
        {
          indexed with
          Ext_cert.imports = [ request 14 mutual_depends_on_indexed ];
        }
      in
      (match
         Ext_session.topological_plan
           [ candidate indexed_cycle; candidate mutual_depends_on_indexed ]
           (candidate
              {
                nested with
                Ext_cert.imports = [ request 15 indexed_cycle ];
              })
       with
      | Error (Ext_session.Graph_error { reason = Ext_session.Import_cycle; _ }) ->
          ()
      | _ -> failwith "high-trust plan must reject import cycles");
      (match
         Ext_session.topological_plan
           [ candidate mutual_with_no_imports; candidate mutual_with_no_imports ]
           (candidate
              {
                nested with
                Ext_cert.imports = [ request 16 mutual_with_no_imports ];
              })
       with
      | Error
          (Ext_session.Graph_error { reason = Ext_session.Duplicate_import; _ }) ->
          ()
      | _ -> failwith "high-trust plan must reject duplicate identities");
      (match
         Ext_session.topological_plan [ candidate mutual_with_no_imports ]
           (candidate
              {
                nested with
                Ext_cert.imports =
                  [ request ~certificate_hash:false 17 mutual_with_no_imports ];
              })
       with
      | Error
          (Ext_session.Graph_error
            { reason = Ext_session.Missing_certificate_hash; offset = 17 }) ->
          ()
      | _ ->
          failwith "high-trust plan must reject missing certificate hashes")

let should_run selected name = selected = [] || List.mem name selected

let () =
  let selected = Array.to_list Sys.argv |> List.tl in
  List.iter
    (fun name ->
      if
        not
          (List.mem name
             [
               "cli";
               "checker-pipeline";
               "defeq";
               "axiom-report";
               "axiom-policy";
               "axiom-policy-parse";
               "decoder-bytes";
               "decoder-declarations";
               "decoder-header";
               "decoder-reachability";
               "decoder-tables";
               "feature-policy";
               "hash-declarations";
               "hash-encoder";
               "hash-level-term";
               "hash-module";
               "import-high-trust";
               "import-normal";
               "import-store";
               "inductive-constructors";
               "inductive-universe";
               "positivity";
               "recursor";
               "reduce";
               "sha256";
               "subst";
               "type-core";
               "type-declarations";
               "type-env";
             ])
      then
        failwith ("unknown test filter " ^ name))
    selected;
  if should_run selected "defeq" then run_defeq_tests ();
  if should_run selected "axiom-report" then run_axiom_report_tests ();
  if should_run selected "axiom-policy" then run_axiom_policy_tests ();
  if should_run selected "axiom-policy-parse" then
    run_axiom_policy_parse_tests ();
  if should_run selected "sha256" then run_sha256_tests ();
  if should_run selected "decoder-bytes" then run_decoder_bytes_tests ();
  if should_run selected "decoder-header" then run_decoder_header_tests ();
  if should_run selected "decoder-tables" then run_decoder_tables_tests ();
  if should_run selected "decoder-declarations" then run_decoder_declarations_tests ();
  if should_run selected "decoder-reachability" then run_decoder_reachability_tests ();
  if should_run selected "feature-policy" then run_feature_policy_tests ();
  if should_run selected "hash-level-term" then run_hash_level_term_tests ();
  if should_run selected "hash-declarations" then run_hash_declarations_tests ();
  if should_run selected "hash-module" then run_hash_module_tests ();
  if should_run selected "import-store" then run_import_store_tests ();
  if should_run selected "import-normal" then run_import_normal_tests ();
  if should_run selected "import-high-trust" then run_import_high_trust_tests ();
  if should_run selected "inductive-constructors" then
    run_inductive_constructor_tests ();
  if should_run selected "inductive-universe" then
    run_inductive_universe_tests ();
  if should_run selected "positivity" then run_positivity_tests ();
  if should_run selected "recursor" then run_recursor_tests ();
  if should_run selected "reduce" then run_reduce_tests ();
  if should_run selected "subst" then run_subst_tests ();
  if should_run selected "type-env" then run_type_env_tests ();
  if should_run selected "type-core" then run_type_core_tests ();
  if should_run selected "type-declarations" then run_type_declarations_tests ();
  if should_run selected "hash-encoder" then run_hash_encoder_tests ();
  if should_run selected "checker-pipeline" then run_checker_pipeline_tests ();
  if should_run selected "cli" then run_cli_tests ()
