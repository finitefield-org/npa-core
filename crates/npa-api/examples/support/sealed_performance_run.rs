use std::collections::BTreeMap;
use std::path::PathBuf;

use sha2::{Digest as _, Sha256};

pub const SCHEMA_ID: &str = "npa.performance.sealed-run.v1";
pub const SCHEMA_VERSION: u64 = 1;
pub const SEAL_NAME: &str = ".npa-seal.json";
pub const MAX_SEAL_BYTES: u64 = 8 * 1024 * 1024;
const CATALOG_DOMAIN: &[u8] = b"npa-performance-sealed-run-catalog-v1\0";

/// Authenticated bytes and metadata supplied by a retained-directory reader.
/// This deliberately has no dependency on a particular filesystem helper so
/// the canonical seal contract can be shared by all benchmark crates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SealedInputFile<'a> {
    pub bytes: &'a [u8],
    pub mode: u32,
    pub link_count: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogEntry {
    pub path: String,
    pub mode: u32,
    pub size: u64,
    pub sha256: String,
}

pub fn canonical_seal_bytes(
    lane_id: &str,
    report_name: &str,
    report_schema: &str,
    files: &BTreeMap<PathBuf, SealedInputFile<'_>>,
) -> Result<Vec<u8>, String> {
    validate_token(lane_id, "sealed lane id")?;
    validate_basename(report_name, "sealed report name")?;
    if report_schema.is_empty()
        || report_schema
            .bytes()
            .any(|byte| byte <= 0x20 || byte >= 0x7f)
    {
        return Err("sealed report schema is not canonical ASCII".to_owned());
    }
    let entries = catalog_entries(files)?;
    let report = entries
        .iter()
        .find(|entry| entry.path == report_name)
        .ok_or("sealed catalog does not contain its report")?;
    let catalog_sha256 = catalog_digest(lane_id, report_name, report_schema, &entries)?;
    let mut output = String::from("{\"schema_id\":");
    push_json_string(&mut output, SCHEMA_ID);
    output.push_str(",\"schema_version\":");
    output.push_str(&SCHEMA_VERSION.to_string());
    output.push_str(",\"lane_id\":");
    push_json_string(&mut output, lane_id);
    output.push_str(",\"report_name\":");
    push_json_string(&mut output, report_name);
    output.push_str(",\"report_schema\":");
    push_json_string(&mut output, report_schema);
    output.push_str(",\"report_size\":");
    output.push_str(&report.size.to_string());
    output.push_str(",\"report_sha256\":");
    push_json_string(&mut output, &report.sha256);
    output.push_str(",\"catalog_sha256\":");
    push_json_string(&mut output, &catalog_sha256);
    output.push_str(",\"catalog\":[");
    for (index, entry) in entries.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str("{\"path\":");
        push_json_string(&mut output, &entry.path);
        output.push_str(",\"type\":\"regular\",\"mode\":");
        output.push_str(&entry.mode.to_string());
        output.push_str(",\"size\":");
        output.push_str(&entry.size.to_string());
        output.push_str(",\"sha256\":");
        push_json_string(&mut output, &entry.sha256);
        output.push('}');
    }
    output.push_str("]}\n");
    let bytes = output.into_bytes();
    if u64::try_from(bytes.len()).map_err(|error| error.to_string())? > MAX_SEAL_BYTES {
        return Err("canonical sealed-run marker exceeds its byte limit".to_owned());
    }
    Ok(bytes)
}

/// Require exact canonical bytes rather than accepting a semantically
/// equivalent JSON spelling, key order, escape, or terminal whitespace.
pub fn validate_canonical_seal_bytes(
    actual: &[u8],
    lane_id: &str,
    report_name: &str,
    report_schema: &str,
    files: &BTreeMap<PathBuf, SealedInputFile<'_>>,
) -> Result<(), String> {
    if u64::try_from(actual.len()).map_err(|error| error.to_string())? > MAX_SEAL_BYTES {
        return Err("sealed-run marker exceeds its byte limit".to_owned());
    }
    let expected = canonical_seal_bytes(lane_id, report_name, report_schema, files)?;
    if actual != expected {
        return Err("sealed-run marker is not the exact canonical commitment".to_owned());
    }
    Ok(())
}

fn catalog_entries(
    files: &BTreeMap<PathBuf, SealedInputFile<'_>>,
) -> Result<Vec<CatalogEntry>, String> {
    files
        .iter()
        .map(|(relative, sealed)| {
            let path = relative
                .to_str()
                .ok_or("sealed catalog path is not UTF-8")?;
            validate_basename(path, "sealed catalog path")?;
            if path == SEAL_NAME {
                return Err("sealed catalog must exclude its own seal".to_owned());
            }
            if sealed.mode != 0o600 || sealed.link_count != 1 {
                return Err(
                    "sealed catalog member has an invalid private mode or link count".to_owned(),
                );
            }
            Ok(CatalogEntry {
                path: path.to_owned(),
                mode: sealed.mode,
                size: u64::try_from(sealed.bytes.len()).map_err(|error| error.to_string())?,
                sha256: content_sha256(sealed.bytes),
            })
        })
        .collect()
}

fn catalog_digest(
    lane_id: &str,
    report_name: &str,
    report_schema: &str,
    entries: &[CatalogEntry],
) -> Result<String, String> {
    let mut digest = Sha256::new();
    digest.update(CATALOG_DOMAIN);
    update_field(&mut digest, SCHEMA_ID.as_bytes())?;
    update_field(&mut digest, SCHEMA_VERSION.to_string().as_bytes())?;
    update_field(&mut digest, lane_id.as_bytes())?;
    update_field(&mut digest, report_name.as_bytes())?;
    update_field(&mut digest, report_schema.as_bytes())?;
    update_field(&mut digest, entries.len().to_string().as_bytes())?;
    for entry in entries {
        update_field(&mut digest, entry.path.as_bytes())?;
        update_field(&mut digest, b"regular")?;
        update_field(&mut digest, entry.mode.to_string().as_bytes())?;
        update_field(&mut digest, entry.size.to_string().as_bytes())?;
        update_field(&mut digest, entry.sha256.as_bytes())?;
    }
    Ok(format!("sha256:{:x}", digest.finalize()))
}

fn update_field(digest: &mut Sha256, bytes: &[u8]) -> Result<(), String> {
    digest.update(
        u64::try_from(bytes.len())
            .map_err(|error| error.to_string())?
            .to_be_bytes(),
    );
    digest.update(bytes);
    Ok(())
}

fn content_sha256(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn validate_token(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty()
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(format!("{label} is not a canonical token"));
    }
    Ok(())
}

fn validate_basename(value: &str, label: &str) -> Result<(), String> {
    validate_token(value, label)?;
    if value == "." || value == ".." || value.contains('/') || value.contains('\\') {
        return Err(format!("{label} is not a safe basename"));
    }
    Ok(())
}

fn push_json_string(output: &mut String, value: &str) {
    output.push('"');
    for byte in value.bytes() {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            0x00..=0x1f => {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                output.push_str("\\u00");
                output.push(char::from(HEX[usize::from(byte >> 4)]));
                output.push(char::from(HEX[usize::from(byte & 0x0f)]));
            }
            _ => output.push(char::from(byte)),
        }
    }
    output.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_seal_is_ordered_terminal_and_lane_bound() {
        let files = BTreeMap::from([
            (
                PathBuf::from("z.json"),
                SealedInputFile {
                    bytes: b"z",
                    mode: 0o600,
                    link_count: 1,
                },
            ),
            (
                PathBuf::from("matrix.json"),
                SealedInputFile {
                    bytes: b"{}\n",
                    mode: 0o600,
                    link_count: 1,
                },
            ),
        ]);
        let seal = canonical_seal_bytes("snapshot", "matrix.json", "matrix.v1", &files).unwrap();
        assert!(seal.ends_with(b"}\n"));
        let text = std::str::from_utf8(&seal).unwrap();
        assert!(text.find("matrix.json").unwrap() < text.find("z.json").unwrap());
        assert_ne!(
            seal,
            canonical_seal_bytes("shared-payload", "matrix.json", "matrix.v1", &files).unwrap()
        );
        validate_canonical_seal_bytes(&seal, "snapshot", "matrix.json", "matrix.v1", &files)
            .unwrap();
        let mut noncanonical = seal.clone();
        noncanonical.push(b'\n');
        assert!(validate_canonical_seal_bytes(
            &noncanonical,
            "snapshot",
            "matrix.json",
            "matrix.v1",
            &files
        )
        .is_err());
    }

    #[test]
    fn canonical_seal_rejects_mode_link_path_and_report_substitution() {
        let mut files = BTreeMap::from([(
            PathBuf::from("matrix.json"),
            SealedInputFile {
                bytes: b"{}\n",
                mode: 0o600,
                link_count: 1,
            },
        )]);
        let seal = canonical_seal_bytes("snapshot", "matrix.json", "matrix.v3", &files).unwrap();

        files.get_mut(&PathBuf::from("matrix.json")).unwrap().mode = 0o700;
        assert!(canonical_seal_bytes("snapshot", "matrix.json", "matrix.v3", &files).is_err());
        files.get_mut(&PathBuf::from("matrix.json")).unwrap().mode = 0o600;
        files
            .get_mut(&PathBuf::from("matrix.json"))
            .unwrap()
            .link_count = 2;
        assert!(canonical_seal_bytes("snapshot", "matrix.json", "matrix.v3", &files).is_err());

        let unsafe_path = BTreeMap::from([(
            PathBuf::from("../matrix.json"),
            SealedInputFile {
                bytes: b"{}\n",
                mode: 0o600,
                link_count: 1,
            },
        )]);
        assert!(
            canonical_seal_bytes("snapshot", "matrix.json", "matrix.v3", &unsafe_path).is_err()
        );

        let canonical = BTreeMap::from([(
            PathBuf::from("matrix.json"),
            SealedInputFile {
                bytes: b"{}\n",
                mode: 0o600,
                link_count: 1,
            },
        )]);
        assert!(validate_canonical_seal_bytes(
            &seal,
            "snapshot",
            "matrix.json",
            "matrix.v4",
            &canonical
        )
        .is_err());
        assert!(validate_canonical_seal_bytes(
            &seal,
            "snapshot",
            "other.json",
            "matrix.v3",
            &canonical
        )
        .is_err());
    }
}
