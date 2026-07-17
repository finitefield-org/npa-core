type phase_error =
  | Decode_error of Ext_bytes.decode_error
  | Declaration_hash_mismatch of Ext_canonical.declaration_hash_mismatch
  | Module_hash_mismatch of Ext_canonical.module_hash_mismatch
  | Unsupported_feature of Ext_feature.feature_report_entry
  | Import_error of Ext_import_store.resolve_error
  | Type_error of Ext_typecheck.error
  | Axiom_report_error of Ext_axiom.error
  | Axiom_policy_error of Ext_axiom.policy_check_error

type semantically_checked
type normal_trust
type high_trust
type 'trust checked

val decode : string -> (Ext_cert.decoded_module, phase_error) result

val canonical :
  string -> Ext_cert.decoded_module -> (unit, phase_error) result

val declaration_hashes :
  Ext_cert.decoded_module -> (unit, phase_error) result

val module_hashes :
  string -> Ext_cert.decoded_module -> (unit, phase_error) result

val check_normal :
  Ext_import_store.store ->
  Ext_axiom.policy ->
  string ->
  (normal_trust checked, phase_error) result

val check_high_trust :
  high_trust checked list ->
  Ext_axiom.policy ->
  string ->
  (high_trust checked, phase_error) result

val module_name : 'trust checked -> Ext_name.t
val export_hash : 'trust checked -> Ext_hash.digest
val certificate_hash : 'trust checked -> Ext_hash.digest
val axiom_report_hash : 'trust checked -> Ext_hash.digest
val declarations_checked : 'trust checked -> int
val imported_recursor_cache_size : 'trust checked -> int
val imported_mutual_block_cache_size : 'trust checked -> int
val imported_mutual_runtimes_share_families : 'trust checked -> bool
