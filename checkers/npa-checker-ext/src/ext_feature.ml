type feature_report_entry = {
  feature : string;
  offset : int option;
}

type feature_policy_result =
  | Feature_policy_ok
  | Unsupported_core_feature of feature_report_entry

let policy_input_shape = "canonical-certificate-feature-report-only"

let supported_core_features = []

let member name values = List.exists (fun value -> value = name) values

let is_supported_first_release feature = member feature supported_core_features

let rec check_first_release_report entries =
  match entries with
  | [] -> Feature_policy_ok
  | entry :: rest ->
      if is_supported_first_release entry.feature then check_first_release_report rest
      else Unsupported_core_feature entry

let raw_result_for_first_release_report entries =
  match check_first_release_report entries with
  | Feature_policy_ok -> None
  | Unsupported_core_feature entry ->
      Some (Ext_result.unsupported_core_feature ?offset:entry.offset entry.feature)
