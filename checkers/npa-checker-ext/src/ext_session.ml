type candidate = {
  bytes : string;
  decoded : Ext_cert.decoded_module;
}

type graph_reason =
  | Missing_import
  | Export_hash_mismatch
  | Certificate_hash_mismatch
  | Missing_certificate_hash
  | Duplicate_import
  | Import_cycle
  | Resource_limit

type graph_error = {
  reason : graph_reason;
  offset : int;
}

type error =
  | Load_error of Ext_import_store.load_error
  | Check_error of Ext_checker.phase_error
  | Graph_error of graph_error

type result = {
  leaf : Ext_checker.high_trust Ext_checker.checked;
  checked_imports : Ext_checker.high_trust Ext_checker.checked list;
}

let bind value f =
  match value with
  | Ok value -> f value
  | Error error -> Error error

let graph_error offset reason = Error (Graph_error { reason; offset })

let max_import_candidates = Ext_import_store.max_import_candidates
let max_import_candidate_bytes = Ext_bytes.max_certificate_bytes
let max_import_depth = 1_024

let prepare bytes =
  match Ext_checker.decode bytes with
  | Error error -> Error (Check_error error)
  | Ok decoded -> (
      match Ext_checker.canonical bytes decoded with
      | Error error -> Error (Check_error error)
      | Ok () -> (
          match Ext_checker.declaration_hashes decoded with
          | Error error -> Error (Check_error error)
          | Ok () -> (
              match Ext_checker.module_hashes bytes decoded with
              | Error error -> Error (Check_error error)
              | Ok () -> Ok { bytes; decoded })))

let load_candidates_with_budget ~max_candidate_bytes import_dir =
  match
    Ext_import_store.collect_certificate_bytes_with_limit import_dir
      max_candidate_bytes
  with
  | Error error -> Error (Load_error error)
  | Ok certificate_bytes ->
      if List.length certificate_bytes > max_import_candidates then
        graph_error 0 Resource_limit
      else
        let rec loop remaining candidates =
          match remaining with
          | [] -> Ok (List.rev candidates)
          | bytes :: rest ->
              bind (prepare bytes) (fun candidate ->
                  loop rest (candidate :: candidates))
        in
        loop certificate_bytes []

let load_candidates import_dir =
  load_candidates_with_budget ~max_candidate_bytes:max_import_candidate_bytes
    import_dir

let candidate_key candidate =
  ( Ext_name.components
      candidate.decoded.Ext_cert.header.Ext_cert.module_name,
    candidate.decoded.Ext_cert.hashes.Ext_cert.export_hash,
    candidate.decoded.Ext_cert.hashes.Ext_cert.certificate_hash )

let candidate_id candidate =
  Ext_name.to_string candidate.decoded.Ext_cert.header.Ext_cert.module_name
  ^ "\000" ^ candidate.decoded.Ext_cert.hashes.Ext_cert.export_hash ^ "\000"
  ^ candidate.decoded.Ext_cert.hashes.Ext_cert.certificate_hash

let validate_unique candidates =
  let sorted =
    List.sort
      (fun lhs rhs -> Stdlib.compare (candidate_key lhs) (candidate_key rhs))
      candidates
  in
  let rec loop previous remaining =
    match remaining with
    | [] -> Ok sorted
    | candidate :: rest ->
        if
          match previous with
          | Some previous -> candidate_key previous = candidate_key candidate
          | None -> false
        then graph_error 0 Duplicate_import
        else loop (Some candidate) rest
  in
  loop None sorted

let find_candidate candidates (requested : Ext_cert.located_import) =
  let entry = requested.Ext_cert.import_entry in
  let same_module =
    List.filter
      (fun candidate ->
        Ext_name.equal candidate.decoded.Ext_cert.header.Ext_cert.module_name
          entry.Ext_import.module_name)
      candidates
  in
  match same_module with
  | [] -> graph_error requested.Ext_cert.import_offset Missing_import
  | _ ->
      let same_export =
        List.filter
          (fun candidate ->
            candidate.decoded.Ext_cert.hashes.Ext_cert.export_hash
            = entry.Ext_import.export_hash)
          same_module
      in
      (match same_export with
      | [] -> graph_error requested.Ext_cert.import_offset Export_hash_mismatch
      | _ -> (
          match entry.Ext_import.certificate_hash with
          | None ->
              graph_error requested.Ext_cert.import_offset
                Missing_certificate_hash
          | Some certificate_hash ->
              let same_certificate =
                List.filter
                  (fun candidate ->
                    candidate.decoded.Ext_cert.hashes.Ext_cert.certificate_hash
                    = certificate_hash)
                  same_export
              in
              match same_certificate with
              | [] ->
                  graph_error requested.Ext_cert.import_offset
                    Certificate_hash_mismatch
              | [ candidate ] -> Ok candidate
              | _ -> graph_error requested.Ext_cert.import_offset Duplicate_import))

let topological_plan candidates leaf =
  bind (validate_unique candidates) (fun candidates ->
      let visiting = ref [] in
      let emitted = ref [] in
      let plan = ref [] in
      let rec visit depth candidate =
        if depth > max_import_depth then graph_error 0 Resource_limit
        else
          let id = candidate_id candidate in
          if List.mem id !emitted then Ok ()
          else if List.mem id !visiting then graph_error 0 Import_cycle
          else (
            visiting := id :: !visiting;
            let rec visit_imports = function
              | [] -> Ok ()
              | requested :: rest ->
                  bind (find_candidate candidates requested) (fun dependency ->
                      bind (visit (depth + 1) dependency) (fun () ->
                          visit_imports rest))
            in
            bind (visit_imports candidate.decoded.Ext_cert.imports) (fun () ->
                visiting := List.filter (fun current -> current <> id) !visiting;
                emitted := id :: !emitted;
                plan := candidate :: !plan;
                Ok ()))
      in
      let rec roots = function
        | [] -> Ok ()
        | requested :: rest ->
            bind (find_candidate candidates requested) (fun candidate ->
                bind (visit 1 candidate) (fun () -> roots rest))
      in
      bind (roots leaf.decoded.Ext_cert.imports) (fun () ->
          Ok (List.rev !plan)))

let check_high_trust import_dir policy leaf_bytes =
  bind (prepare leaf_bytes) (fun leaf_candidate ->
      bind (load_candidates import_dir) (fun candidates ->
          bind (topological_plan candidates leaf_candidate) (fun plan ->
              let rec check_imports checked_rev = function
                | [] -> Ok (List.rev checked_rev)
                | candidate :: rest -> (
                    match
                      Ext_checker.check_high_trust checked_rev policy
                        candidate.bytes
                    with
                    | Error error -> Error (Check_error error)
                    | Ok checked -> check_imports (checked :: checked_rev) rest)
              in
              bind (check_imports [] plan) (fun checked_imports ->
                  match
                    Ext_checker.check_high_trust checked_imports policy leaf_bytes
                  with
                  | Error error -> Error (Check_error error)
                  | Ok leaf -> Ok { leaf; checked_imports }))))

let graph_reason_code = function
  | Missing_import -> "missing_import"
  | Export_hash_mismatch -> "import_export_hash_mismatch"
  | Certificate_hash_mismatch -> "import_certificate_hash_mismatch"
  | Missing_certificate_hash -> "missing_import_certificate_hash"
  | Duplicate_import -> "duplicate_import"
  | Import_cycle -> "import_cycle"
  | Resource_limit -> "resource_limit"
