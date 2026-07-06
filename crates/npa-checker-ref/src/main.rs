#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use npa_checker_ref::{
    check_certificate, decode_certificate, ReferenceCertificateSection, ReferenceCheckError,
    ReferenceCheckErrorKind, ReferenceCheckReason, ReferenceCheckResult, ReferenceCheckerPolicy,
    ReferenceHash, ReferenceHashObject, ReferenceImportStore, ReferenceTrustMode,
    REFERENCE_CERTIFICATE_FORMAT, REFERENCE_CORE_SPEC,
};
use sha2::{Digest, Sha256};

const CHECKER_ID: &str = "npa-checker-ref";
const CHECKER_RAW_RESULT_SCHEMA: &str = "npa.independent-checker.checker_raw_result.v1";

fn main() -> ExitCode {
    let (json, code) = run_with_args(env::args().skip(1));
    println!("{json}");
    ExitCode::from(code)
}

fn run_with_args<I, S>(args: I) -> (String, u8)
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    match CliOptions::parse(args) {
        Ok(options) => match run_checker(options) {
            Ok(output) => output,
            Err(error) => (raw_internal_error_json(error.section, error.offset), 2),
        },
        Err(error) => (raw_internal_error_json(error.section, error.offset), 2),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CliOptions {
    cert_path: PathBuf,
    imports: Option<PathBuf>,
    imports_hash: Option<ReferenceHash>,
    import_dir: Option<PathBuf>,
    policy_path: Option<PathBuf>,
    policy_hash: Option<ReferenceHash>,
    output_json: bool,
}

impl CliOptions {
    fn parse<I, S>(args: I) -> Result<Self, CliError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut cert_path = None;
        let mut imports = None;
        let mut imports_hash = None;
        let mut import_dir = None;
        let mut policy_path = None;
        let mut policy_hash = None;
        let mut output_json = false;
        let mut iter = args.into_iter().map(Into::into).peekable();
        while let Some(arg) = iter.next() {
            match arg.as_str() {
                "--json" | "--canonical-only" => {}
                "--cert" => set_once_path(&mut cert_path, next_value(&mut iter, "--cert")?)?,
                "--imports" => set_once_path(&mut imports, next_value(&mut iter, "--imports")?)?,
                "--imports-hash" => {
                    let hash = parse_hash_arg(&next_value(&mut iter, "--imports-hash")?)?;
                    set_once_hash(&mut imports_hash, hash)?;
                }
                "--import-dir" => {
                    set_once_path(&mut import_dir, next_value(&mut iter, "--import-dir")?)?
                }
                "--policy" => set_once_path(&mut policy_path, next_value(&mut iter, "--policy")?)?,
                "--policy-hash" => {
                    let hash = parse_hash_arg(&next_value(&mut iter, "--policy-hash")?)?;
                    set_once_hash(&mut policy_hash, hash)?;
                }
                "--output" => {
                    let value = next_value(&mut iter, "--output")?;
                    if value != "json" {
                        return Err(CliError::new("output"));
                    }
                    if output_json {
                        return Err(CliError::new("duplicate_arg"));
                    }
                    output_json = true;
                }
                _ if arg.starts_with('-') => return Err(CliError::new("unknown_arg")),
                _ => set_once_path(&mut cert_path, arg)?,
            }
        }
        Ok(Self {
            cert_path: cert_path.ok_or_else(|| CliError::new("cert"))?,
            imports,
            imports_hash,
            import_dir,
            policy_path,
            policy_hash,
            output_json,
        })
    }
}

fn run_checker(options: CliOptions) -> Result<(String, u8), CliError> {
    if !options.output_json {
        return Err(CliError::new("output"));
    }
    reject_source_path(&options.cert_path)?;
    let cert_bytes = fs::read(&options.cert_path).map_err(|_| CliError::new("cert"))?;
    let policy = load_policy(&options)?;
    let imports = load_import_store(&options)?;
    let decoded = decode_certificate(&cert_bytes).ok();

    Ok(match check_certificate(&cert_bytes, &imports, &policy) {
        ReferenceCheckResult::Checked(module) => {
            let json = raw_checked_json(
                module.module().dotted(),
                module.certificate_hash(),
                module.export_hash(),
                module.axiom_report_hash(),
            );
            (json, 0)
        }
        ReferenceCheckResult::Rejected(error) => {
            let json = raw_rejected_json(&error, decoded.as_ref());
            (json, 1)
        }
    })
}

fn load_policy(options: &CliOptions) -> Result<ReferenceCheckerPolicy, CliError> {
    let Some(path) = &options.policy_path else {
        return Ok(ReferenceCheckerPolicy::default());
    };
    reject_source_path(path)?;
    let bytes = fs::read(path).map_err(|_| CliError::new("policy"))?;
    if let Some(expected) = options.policy_hash {
        let actual = sha256(&bytes);
        if actual != expected {
            return Err(CliError::new("policy_hash"));
        }
    }
    let text = std::str::from_utf8(&bytes).map_err(|_| CliError::new("policy"))?;
    parse_policy_text(text)
}

fn parse_policy_text(text: &str) -> Result<ReferenceCheckerPolicy, CliError> {
    let mut policy = ReferenceCheckerPolicy::default();

    if let Some(mode) = find_string_field(text, &["trust_mode", "mode"])? {
        policy.trust_mode = match mode.as_str() {
            "normal" => ReferenceTrustMode::Normal,
            "high-trust" | "high_trust" => ReferenceTrustMode::HighTrust,
            _ => return Err(CliError::new("policy")),
        };
    }
    if let Some(value) = find_bool_field(text, "deny_sorry")? {
        policy.deny_sorry = value;
    }
    if let Some(value) = find_bool_field(text, "deny_custom_axioms")? {
        policy.deny_custom_axioms = value;
    }

    let allowed_axioms = find_string_array_field(text, "allowed_axioms")?;
    let legacy_allow_axioms = find_string_array_field(text, "allow_axioms")?;
    policy.allowed_axioms = match (allowed_axioms, legacy_allow_axioms) {
        (Some(current), Some(legacy)) if current != legacy => return Err(CliError::new("policy")),
        (Some(current), _) => current,
        (None, Some(legacy)) => legacy,
        (None, None) => Vec::new(),
    };

    Ok(policy)
}

fn find_bool_field(source: &str, field: &str) -> Result<Option<bool>, CliError> {
    let Some(start) = find_field_value_start(source, field) else {
        return Ok(None);
    };
    if source[start..].starts_with("true") && has_policy_bool_delimiter(source, start + 4) {
        Ok(Some(true))
    } else if source[start..].starts_with("false") && has_policy_bool_delimiter(source, start + 5) {
        Ok(Some(false))
    } else {
        Err(CliError::new("policy"))
    }
}

fn find_string_field(source: &str, fields: &[&str]) -> Result<Option<String>, CliError> {
    for field in fields {
        if let Some(start) = find_field_value_start(source, field) {
            let (value, _) = parse_json_string(source, start)?;
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn find_string_array_field(source: &str, field: &str) -> Result<Option<Vec<String>>, CliError> {
    let Some(start) = find_field_value_start(source, field) else {
        return Ok(None);
    };
    parse_string_array(source, start).map(Some)
}

fn find_field_value_start(source: &str, field: &str) -> Option<usize> {
    let quoted = format!("\"{field}\"");
    let bytes = source.as_bytes();
    let mut search_start = 0;
    while let Some(relative) = source[search_start..].find(&quoted) {
        let index = search_start + relative + quoted.len();
        let after_field = skip_policy_ws(bytes, index);
        if bytes.get(after_field) == Some(&b':') {
            return Some(skip_policy_ws(bytes, after_field + 1));
        }
        search_start = index;
    }

    search_start = 0;
    while let Some(relative) = source[search_start..].find(field) {
        let index = search_start + relative;
        let has_left_boundary = index == 0 || !is_policy_ident_byte(bytes[index - 1]);
        let after_name = index + field.len();
        let has_right_boundary = bytes
            .get(after_name)
            .is_none_or(|byte| !is_policy_ident_byte(*byte));
        if has_left_boundary && has_right_boundary {
            let after_field = skip_policy_ws(bytes, after_name);
            if bytes.get(after_field) == Some(&b'=') {
                return Some(skip_policy_ws(bytes, after_field + 1));
            }
        }
        search_start = index + 1;
    }
    None
}

fn is_policy_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn skip_policy_ws(bytes: &[u8], mut index: usize) -> usize {
    while bytes.get(index).is_some_and(u8::is_ascii_whitespace) {
        index += 1;
    }
    index
}

fn has_policy_bool_delimiter(source: &str, index: usize) -> bool {
    source
        .as_bytes()
        .get(index)
        .is_none_or(|byte| byte.is_ascii_whitespace() || matches!(*byte, b',' | b'}' | b']'))
}

fn parse_string_array(source: &str, start: usize) -> Result<Vec<String>, CliError> {
    let bytes = source.as_bytes();
    let start = skip_policy_ws(bytes, start);
    if bytes.get(start) != Some(&b'[') {
        return Err(CliError::new("policy"));
    }
    let mut index = start + 1;
    let mut values = Vec::new();
    loop {
        index = skip_policy_ws(bytes, index);
        match bytes.get(index) {
            Some(b']') => return Ok(values),
            Some(b'"') => {
                let (value, next) = parse_json_string(source, index)?;
                values.push(value);
                index = skip_policy_ws(bytes, next);
                match bytes.get(index) {
                    Some(b',') => index += 1,
                    Some(b']') => return Ok(values),
                    _ => return Err(CliError::new("policy")),
                }
            }
            _ => return Err(CliError::new("policy")),
        }
    }
}

fn load_import_store(options: &CliOptions) -> Result<ReferenceImportStore, CliError> {
    let mut paths = BTreeSet::new();
    if let Some(import_dir) = &options.import_dir {
        collect_cert_paths(import_dir, &mut paths)?;
    }
    if let Some(imports) = &options.imports {
        reject_source_path(imports)?;
        let metadata = fs::metadata(imports).map_err(|_| CliError::new("imports"))?;
        if metadata.is_dir() {
            collect_cert_paths(imports, &mut paths)?;
        } else {
            let bytes = fs::read(imports).map_err(|_| CliError::new("imports"))?;
            if let Some(expected) = options.imports_hash {
                let actual = sha256(&bytes);
                if actual != expected {
                    return Err(CliError::new("imports_hash"));
                }
            }
            let text = std::str::from_utf8(&bytes).map_err(|_| CliError::new("imports"))?;
            for path in import_lock_certificate_paths(text)? {
                paths.insert(PathBuf::from(path));
            }
        }
    }

    let cert_canonical = fs::canonicalize(&options.cert_path).ok();
    let mut bytes = Vec::new();
    for path in paths {
        reject_source_path(&path)?;
        if fs::canonicalize(&path).ok() == cert_canonical {
            continue;
        }
        bytes.push(fs::read(path).map_err(|_| CliError::new("imports"))?);
    }
    ReferenceImportStore::from_source_free_certificates(bytes.iter().map(Vec::as_slice))
        .map_err(|_| CliError::new("imports"))
}

fn collect_cert_paths(dir: &Path, out: &mut BTreeSet<PathBuf>) -> Result<(), CliError> {
    reject_source_path(dir)?;
    let mut entries = fs::read_dir(dir)
        .map_err(|_| CliError::new("import_dir"))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| CliError::new("import_dir"))?;
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type().map_err(|_| CliError::new("import_dir"))?;
        if file_type.is_dir() {
            collect_cert_paths(&path, out)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("npcert") {
            out.insert(path);
        }
    }
    Ok(())
}

fn import_lock_certificate_paths(source: &str) -> Result<Vec<String>, CliError> {
    let mut paths = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0;
    while let Some(relative) = source[index..].find("\"path\"") {
        index += relative + "\"path\"".len();
        while bytes
            .get(index)
            .is_some_and(|byte| byte.is_ascii_whitespace())
        {
            index += 1;
        }
        if bytes.get(index) != Some(&b':') {
            continue;
        }
        index += 1;
        while bytes
            .get(index)
            .is_some_and(|byte| byte.is_ascii_whitespace())
        {
            index += 1;
        }
        if bytes.get(index) != Some(&b'"') {
            continue;
        }
        let (path, next) = parse_json_string(source, index)?;
        if path.ends_with(".npcert") {
            if Path::new(&path).is_absolute() || path.split('/').any(|component| component == "..")
            {
                return Err(CliError::new("imports"));
            }
            paths.push(path);
        }
        index = next;
    }
    Ok(paths)
}

fn parse_json_string(source: &str, start: usize) -> Result<(String, usize), CliError> {
    let bytes = source.as_bytes();
    if bytes.get(start) != Some(&b'"') {
        return Err(CliError::new("json"));
    }
    let mut out = String::new();
    let mut index = start + 1;
    while let Some(byte) = bytes.get(index).copied() {
        match byte {
            b'"' => return Ok((out, index + 1)),
            b'\\' => {
                index += 1;
                let escaped = bytes
                    .get(index)
                    .copied()
                    .ok_or_else(|| CliError::new("json"))?;
                let ch = match escaped {
                    b'"' => '"',
                    b'\\' => '\\',
                    b'/' => '/',
                    b'b' => '\u{0008}',
                    b'f' => '\u{000c}',
                    b'n' => '\n',
                    b'r' => '\r',
                    b't' => '\t',
                    _ => return Err(CliError::new("json")),
                };
                out.push(ch);
            }
            _ => out.push(char::from(byte)),
        }
        index += 1;
    }
    Err(CliError::new("json"))
}

fn raw_checked_json(
    module: String,
    certificate_hash: &ReferenceHash,
    export_hash: &ReferenceHash,
    axiom_report_hash: &ReferenceHash,
) -> String {
    format!(
        "{{\"schema\":\"{}\",\"checker_id\":\"{}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"status\":\"checked\",\"module\":{},\"certificate_hash\":\"{}\",\"export_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}",
        CHECKER_RAW_RESULT_SCHEMA,
        CHECKER_ID,
        env!("CARGO_PKG_VERSION"),
        format_hash(&checker_build_hash()),
        json_string(&module),
        format_hash(certificate_hash),
        format_hash(export_hash),
        format_hash(axiom_report_hash)
    )
}

fn raw_rejected_json(
    error: &ReferenceCheckError,
    decoded: Option<&npa_checker_ref::ReferenceDecodedCertificate>,
) -> String {
    let mut fields = vec![
        format!("\"schema\":\"{}\"", CHECKER_RAW_RESULT_SCHEMA),
        format!("\"checker_id\":\"{}\"", CHECKER_ID),
        format!("\"checker_version\":\"{}\"", env!("CARGO_PKG_VERSION")),
        format!(
            "\"checker_build_hash\":\"{}\"",
            format_hash(&checker_build_hash())
        ),
        "\"status\":\"failed\"".to_owned(),
    ];
    if let Some(decoded) = decoded {
        fields.push(format!(
            "\"module\":{}",
            json_string(&decoded.header().module.dotted())
        ));
        fields.push(format!(
            "\"certificate_hash\":\"{}\"",
            format_hash(&decoded.hashes().certificate_hash)
        ));
    }
    fields.push(format!("\"error\":{}", raw_error_json(error)));
    format!("{{{}}}", fields.join(","))
}

fn raw_error_json(error: &ReferenceCheckError) -> String {
    format!(
        "{{\"kind\":\"{}\",\"section\":{},\"offset\":{}}}",
        raw_error_kind(error),
        json_string(section_name(error.section)),
        error.offset
    )
}

fn raw_internal_error_json(section: &'static str, offset: usize) -> String {
    format!(
        "{{\"schema\":\"{}\",\"checker_id\":\"{}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"status\":\"failed\",\"error\":{{\"kind\":\"checker_internal_error\",\"reason_code\":\"checker_reported_internal_error\",\"section\":{},\"offset\":{}}}}}",
        CHECKER_RAW_RESULT_SCHEMA,
        CHECKER_ID,
        env!("CARGO_PKG_VERSION"),
        format_hash(&checker_build_hash()),
        json_string(section),
        offset
    )
}

fn raw_error_kind(error: &ReferenceCheckError) -> &'static str {
    match error.kind {
        ReferenceCheckErrorKind::EmptyCertificate
        | ReferenceCheckErrorKind::MalformedCertificate => "certificate_decode_error",
        ReferenceCheckErrorKind::HashMismatch => match error.reason {
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::ExportBlock,
            }) => "export_hash_mismatch",
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::AxiomReport,
            }) => "axiom_report_mismatch",
            Some(ReferenceCheckReason::HashMismatch {
                object: ReferenceHashObject::ModuleCertificate,
            }) => "certificate_hash_mismatch",
            Some(ReferenceCheckReason::HashMismatch { .. }) => "declaration_hash_mismatch",
            _ => "certificate_hash_mismatch",
        },
        ReferenceCheckErrorKind::ImportResolution => match error.reason {
            Some(ReferenceCheckReason::ImportExportHashMismatch)
            | Some(ReferenceCheckReason::ImportCertificateHashMismatch) => "import_hash_mismatch",
            _ => "import_not_found",
        },
        ReferenceCheckErrorKind::AxiomReportMismatch => "axiom_report_mismatch",
        ReferenceCheckErrorKind::AxiomPolicy => "forbidden_axiom",
        ReferenceCheckErrorKind::TypeCheck => match error.reason {
            Some(ReferenceCheckReason::NonPositiveOccurrence) => "positivity_failure",
            Some(ReferenceCheckReason::BadConstructorResult)
            | Some(ReferenceCheckReason::BadRecursorRule)
            | Some(ReferenceCheckReason::BadRecursorParam)
            | Some(ReferenceCheckReason::BadRecursorMotive)
            | Some(ReferenceCheckReason::BadRecursorMajor)
            | Some(ReferenceCheckReason::BadRecursorMinor)
            | Some(ReferenceCheckReason::BadRecursorResult)
            | Some(ReferenceCheckReason::BadRecursorType) => "inductive_invalid",
            Some(ReferenceCheckReason::BadUniverseArity)
            | Some(ReferenceCheckReason::DuplicateUniverseParam)
            | Some(ReferenceCheckReason::UnresolvedMetavariable) => "universe_inconsistency",
            _ => "type_mismatch",
        },
        ReferenceCheckErrorKind::UnsupportedSkeleton => "unsupported_schema_version",
        ReferenceCheckErrorKind::UnsupportedCoreFeature => "unsupported_core_feature",
    }
}

fn section_name(section: ReferenceCertificateSection) -> &'static str {
    match section {
        ReferenceCertificateSection::HeaderFormat => "header_format",
        ReferenceCertificateSection::HeaderCoreSpec => "header_core_spec",
        ReferenceCertificateSection::HeaderModule => "header_module",
        ReferenceCertificateSection::Imports => "imports",
        ReferenceCertificateSection::NameTable => "name_table",
        ReferenceCertificateSection::LevelTable => "level_table",
        ReferenceCertificateSection::TermTable => "term_table",
        ReferenceCertificateSection::Declarations => "declarations",
        ReferenceCertificateSection::ExportBlock => "export_block",
        ReferenceCertificateSection::AxiomReport => "axiom_report",
        ReferenceCertificateSection::Hashes => "hashes",
        ReferenceCertificateSection::ImportStore => "import_store",
        ReferenceCertificateSection::FullCertificate => "full_certificate",
    }
}

fn checker_build_hash() -> ReferenceHash {
    sha256(
        format!(
            "{CHECKER_ID}:{}:{REFERENCE_CORE_SPEC}:{REFERENCE_CERTIFICATE_FORMAT}",
            env!("CARGO_PKG_VERSION")
        )
        .as_bytes(),
    )
}

fn set_once_path(slot: &mut Option<PathBuf>, value: String) -> Result<(), CliError> {
    if slot.is_some() {
        return Err(CliError::new("duplicate_arg"));
    }
    *slot = Some(PathBuf::from(value));
    Ok(())
}

fn set_once_hash(slot: &mut Option<ReferenceHash>, value: ReferenceHash) -> Result<(), CliError> {
    if slot.is_some() {
        return Err(CliError::new("duplicate_arg"));
    }
    *slot = Some(value);
    Ok(())
}

fn next_value<I>(iter: &mut std::iter::Peekable<I>, flag: &'static str) -> Result<String, CliError>
where
    I: Iterator<Item = String>,
{
    match iter.next() {
        Some(value) if !value.starts_with('-') => Ok(value),
        _ => Err(CliError::new(flag)),
    }
}

fn parse_hash_arg(value: &str) -> Result<ReferenceHash, CliError> {
    let hex = value
        .strip_prefix("sha256:")
        .ok_or_else(|| CliError::new("hash"))?;
    if hex.len() != 64 {
        return Err(CliError::new("hash"));
    }
    let mut out = [0; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = (hex_nibble(hex.as_bytes()[index * 2])? << 4)
            | hex_nibble(hex.as_bytes()[index * 2 + 1])?;
    }
    Ok(out)
}

fn hex_nibble(byte: u8) -> Result<u8, CliError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(CliError::new("hash")),
    }
}

fn reject_source_path(path: &Path) -> Result<(), CliError> {
    if path.extension().and_then(|ext| ext.to_str()) == Some("npa") {
        return Err(CliError::new("source_mount"));
    }
    Ok(())
}

fn sha256(bytes: &[u8]) -> ReferenceHash {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

fn format_hash(hash: &ReferenceHash) -> String {
    let mut out = String::from("sha256:");
    for byte in hash {
        out.push(hex_char(byte >> 4));
        out.push(hex_char(byte & 0x0f));
    }
    out
}

fn hex_char(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex nibble"),
    }
}

fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000c}' => out.push_str("\\f"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str("\\u00");
                out.push(hex_char((ch as u8) >> 4));
                out.push(hex_char((ch as u8) & 0x0f));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CliError {
    section: &'static str,
    offset: usize,
}

impl CliError {
    const fn new(section: &'static str) -> Self {
        Self { section, offset: 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use npa_cert::{build_module_cert, encode_module_cert, CoreModule, Name};
    use npa_kernel::{Decl, Expr, Level};

    fn temp_dir(name: &str) -> PathBuf {
        let mut path = env::temp_dir();
        path.push(format!("npa-checker-ref-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        path
    }

    fn minimal_certificate(module: &str) -> Vec<u8> {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted(module),
                declarations: Vec::new(),
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn custom_axiom_certificate() -> Vec<u8> {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Policy.Custom"),
                declarations: vec![Decl::Axiom {
                    name: "P".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                }],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    #[test]
    fn cli_checks_certificate_from_fixed_cert_flag() {
        let dir = temp_dir("checked");
        let cert_path = dir.join("Cli.Empty.npcert");
        fs::write(&cert_path, minimal_certificate("Cli.Empty")).unwrap();

        let (json, code) = run_with_args([
            "--json".to_owned(),
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);

        assert_eq!(code, 0);
        assert!(json.contains("\"checker_id\":\"npa-checker-ref\""));
        assert!(json.contains("\"status\":\"checked\""));
        assert!(json.contains("\"module\":\"Cli.Empty\""));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn cli_rejects_malformed_certificate_as_raw_failure() {
        let dir = temp_dir("malformed");
        let cert_path = dir.join("bad.npcert");
        fs::write(&cert_path, b"bad").unwrap();

        let (json, code) = run_with_args([
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);

        assert_eq!(code, 1);
        assert!(json.contains("\"status\":\"failed\""));
        assert!(json.contains("\"kind\":\"certificate_decode_error\""));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn cli_policy_pretty_json_denies_custom_axioms() {
        let dir = temp_dir("policy-deny");
        let cert_path = dir.join("Policy.Custom.npcert");
        let policy_path = dir.join("policy.json");
        fs::write(&cert_path, custom_axiom_certificate()).unwrap();
        fs::write(
            &policy_path,
            r#"{
              "deny_sorry": true,
              "deny_custom_axioms": true,
              "allow_axioms": []
            }"#,
        )
        .unwrap();

        let (json, code) = run_with_args([
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--policy".to_owned(),
            policy_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);

        assert_eq!(code, 1);
        assert!(json.contains("\"kind\":\"forbidden_axiom\""));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn cli_policy_allowlist_accepts_exact_custom_axiom() {
        let dir = temp_dir("policy-allow");
        let cert_path = dir.join("Policy.Custom.npcert");
        let policy_path = dir.join("policy.toml");
        fs::write(&cert_path, custom_axiom_certificate()).unwrap();
        fs::write(
            &policy_path,
            r#"
              deny_custom_axioms = true
              allowed_axioms = ["Policy.Custom.P"]
            "#,
        )
        .unwrap();

        let (json, code) = run_with_args([
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--policy".to_owned(),
            policy_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);

        assert_eq!(code, 0);
        assert!(json.contains("\"status\":\"checked\""));
        assert!(json.contains("\"module\":\"Policy.Custom\""));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn cli_policy_rejects_malformed_bool_literal() {
        assert!(parse_policy_text("deny_custom_axioms = trueish").is_err());
    }

    #[test]
    fn cli_contract_rejects_extra_flags_and_cwd_like_overrides() {
        for flag in ["--binary", "--env", "--cwd", "--source"] {
            let (_, code) = run_with_args([
                flag.to_owned(),
                "x".to_owned(),
                "--output".to_owned(),
                "json".to_owned(),
            ]);
            assert_eq!(code, 2, "{flag} must not enter checker argv");
        }

        let hash = format!("sha256:{}", "00".repeat(32));
        for args in [
            vec![
                "--output".to_owned(),
                "json".to_owned(),
                "--output".to_owned(),
                "json".to_owned(),
            ],
            vec![
                "--imports-hash".to_owned(),
                hash.clone(),
                "--imports-hash".to_owned(),
                hash,
            ],
        ] {
            let (_, code) = run_with_args(args);
            assert_eq!(code, 2, "duplicate runner-owned values must be rejected");
        }
    }
}
