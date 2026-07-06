type digest = string

let vendored_sha256_source_identity = Ext_sha256.source_identity

let sha256_raw_bytes input = Ext_sha256.digest_bytes input

let sha256_raw_string input = Ext_sha256.digest_string input

let sha256_hex_of_bytes input = Ext_sha256.hex_of_bytes input

let sha256_hex_of_string input = Ext_sha256.hex_of_string input

let sha256_prefixed_hex_of_bytes input = "sha256:" ^ sha256_hex_of_bytes input

let sha256_prefixed_hex_of_string input = "sha256:" ^ sha256_hex_of_string input

let unsupported_digest = sha256_prefixed_hex_of_string "npa-checker-ext:unsupported-digest:v1"
