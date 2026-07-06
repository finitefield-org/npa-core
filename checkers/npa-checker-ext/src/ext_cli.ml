type cli_result = {
  stdout : string;
  stderr : string;
  code : int;
}

type options = {
  cert : string option;
  import_dir : string option;
  policy : string option;
  output : string option;
}

type 'a parse_result =
  | Parsed of 'a
  | Parse_error of string

let empty_options = { cert = None; import_dir = None; policy = None; output = None }

let ok stdout = { stdout; stderr = ""; code = 0 }

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

let is_source_path value =
  has_suffix value ".npa" || contains_substring value ".npa/" || contains_substring value ".npa\\"

let reject_source_path flag value =
  if is_source_path value then Some (flag ^ " must not point to .npa source")
  else None

let set_once flag current value update =
  match current with
  | Some _ -> Parse_error ("duplicate " ^ flag)
  | None -> (
      if starts_with value "--" then Parse_error ("missing value for " ^ flag)
      else (
        match reject_source_path flag value with
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
  else if options.output = None then Some "missing required --output"
  else None

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
          | None -> ok (Ext_result.skeleton_failure ())))
