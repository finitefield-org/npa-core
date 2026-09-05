#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;

use npa_checker_ref::{
    check_certificate, decode_certificate, reference_checker_build_hash,
    ReferenceCertificateSection, ReferenceCheckError, ReferenceCheckErrorKind,
    ReferenceCheckImportTarget, ReferenceCheckReason, ReferenceCheckReference,
    ReferenceCheckResolvedImportIdentity, ReferenceCheckResult, ReferenceCheckerPolicy,
    ReferenceHash, ReferenceHashObject, ReferenceImportStore, ReferenceTrustMode,
    REFERENCE_CERTIFICATE_FORMAT, REFERENCE_CHECKER_ID, REFERENCE_CHECKER_VERSION,
    REFERENCE_CORE_SPEC,
};
use sha2::{Digest, Sha256};

#[path = "../../npa-cert/examples/support/policy_toml.rs"]
mod policy_toml;

const CHECKER_RAW_RESULT_SCHEMA: &str = "npa.independent-checker.checker_raw_result.v2";
const MAX_CERTIFICATE_BYTES: usize = 67_108_864;
const MAX_POLICY_BYTES: usize = 67_108_864;
const MAX_IMPORT_LOCK_BYTES: usize = 67_108_864;
const MAX_IMPORT_CANDIDATES: usize = 4_096;
const MAX_IMPORT_DIRECTORY_DEPTH: usize = 128;
const MAX_IMPORT_DIRECTORY_ENTRIES: usize = 16_384;
const MAX_IMPORT_CANDIDATE_BYTES: usize = 67_108_864;

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

#[derive(Clone, Debug, PartialEq, Eq)]
struct ImportLockEntry {
    module: String,
    export_hash: ReferenceHash,
    path: String,
    file_hash: ReferenceHash,
    certificate_hash: ReferenceHash,
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
    // Preserve the decoder's exact one-byte-over structural rejection without
    // permitting a sparse or hostile input to allocate an unbounded buffer.
    let certificate = read_bounded_regular_file_with_identity(
        &options.cert_path,
        MAX_CERTIFICATE_BYTES.saturating_add(1),
        "cert",
    )?;
    let cert_bytes = certificate.bytes;
    let policy = load_policy(&options)?;
    let imports = load_import_store(&options, certificate.identity)?;
    let input_pair = raw_input_pair(&cert_bytes);
    let decoded = decode_certificate(&cert_bytes).ok();

    Ok(match check_certificate(&cert_bytes, &imports, &policy) {
        ReferenceCheckResult::Checked(module) => {
            let json = raw_checked_json(
                module.certificate_format(),
                module.core_spec(),
                module.module().dotted(),
                module.certificate_hash(),
                module.export_hash(),
                module.axiom_report_hash(),
            );
            (json, 0)
        }
        ReferenceCheckResult::Rejected(error) => {
            let json = raw_rejected_json(&error, decoded.as_ref(), input_pair.as_ref());
            (json, 1)
        }
    })
}

fn load_policy(options: &CliOptions) -> Result<ReferenceCheckerPolicy, CliError> {
    let Some(path) = &options.policy_path else {
        return Ok(ReferenceCheckerPolicy::default());
    };
    reject_source_path(path)?;
    let bytes = read_bounded_regular_file(path, MAX_POLICY_BYTES, "policy")?;
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
    let allowed_axioms = policy_toml::parse(text).map_err(|_| CliError::new("policy"))?;
    Ok(ReferenceCheckerPolicy {
        // The runner-owned TOML controls the axiom allowlist only. Import
        // trust is selected by a separately bound checker profile; supplying a
        // policy file must not silently promote the ordinary reference binary
        // to the high-trust closure lane.
        trust_mode: ReferenceTrustMode::Normal,
        allowed_axioms,
        deny_sorry: true,
        deny_custom_axioms: true,
        allow_standard_axiom_exceptions: true,
        supported_core_features: Vec::new(),
    })
}

fn load_import_store(
    options: &CliOptions,
    certificate_identity: FileIdentity,
) -> Result<ReferenceImportStore, CliError> {
    let mut candidates = BTreeMap::<PathBuf, BoundedRegularFile>::new();
    let mut locked_imports = Vec::new();
    if let Some(import_dir) = &options.import_dir {
        let mut visited = 0;
        collect_cert_files(import_dir, &mut candidates, 1, &mut visited, &mut 0)?;
    }
    if let Some(imports) = &options.imports {
        reject_source_path(imports)?;
        if let Ok(directory) = open_directory_no_follow(imports, "imports") {
            let mut visited = 0;
            let mut retained = candidates.values().try_fold(0_usize, |sum, file| {
                sum.checked_add(file.bytes.len())
                    .ok_or_else(|| CliError::new("imports"))
            })?;
            collect_cert_files_from_directory(
                directory,
                imports,
                &mut candidates,
                1,
                &mut visited,
                &mut retained,
            )?;
        } else {
            let bytes = read_bounded_regular_file(imports, MAX_IMPORT_LOCK_BYTES, "imports")?;
            if let Some(expected) = options.imports_hash {
                let actual = sha256(&bytes);
                if actual != expected {
                    return Err(CliError::new("imports_hash"));
                }
            }
            let text = std::str::from_utf8(&bytes).map_err(|_| CliError::new("imports"))?;
            locked_imports = parse_import_lock_manifest(text)?;
            for entry in &locked_imports {
                let path = PathBuf::from(&entry.path);
                if !candidates.contains_key(&path) {
                    let retained = candidates.values().try_fold(0_usize, |sum, file| {
                        sum.checked_add(file.bytes.len())
                            .ok_or_else(|| CliError::new("imports"))
                    })?;
                    let remaining = MAX_IMPORT_CANDIDATE_BYTES
                        .checked_sub(retained)
                        .ok_or_else(|| CliError::new("imports"))?;
                    candidates.insert(
                        path.clone(),
                        read_bounded_regular_file_with_identity(&path, remaining, "imports")?,
                    );
                }
                if candidates.len() > MAX_IMPORT_CANDIDATES {
                    return Err(CliError::new("imports"));
                }
            }
        }
    }

    let mut bytes = Vec::new();
    for (path, candidate) in candidates {
        reject_source_path(&path)?;
        if candidate.identity == certificate_identity {
            if locked_imports
                .iter()
                .any(|entry| Path::new(&entry.path) == path)
            {
                return Err(CliError::new("imports"));
            }
            continue;
        }
        if let Some(expected) = locked_imports
            .iter()
            .find(|entry| Path::new(&entry.path) == path)
        {
            validate_locked_import_candidate(expected, &candidate.bytes)?;
        }
        bytes.push(candidate.bytes);
    }
    ReferenceImportStore::from_source_free_certificates(bytes.iter().map(Vec::as_slice))
        .map_err(|_| CliError::new("imports"))
}

fn validate_locked_import_candidate(
    expected: &ImportLockEntry,
    candidate: &[u8],
) -> Result<(), CliError> {
    if sha256(candidate) != expected.file_hash {
        return Err(CliError::new("imports_hash"));
    }
    let decoded = decode_certificate(candidate).map_err(|_| CliError::new("imports"))?;
    if decoded.header().module.dotted() != expected.module
        || decoded.hashes().export_hash != expected.export_hash
        || decoded.hashes().certificate_hash != expected.certificate_hash
    {
        return Err(CliError::new("imports"));
    }
    Ok(())
}

fn collect_cert_files(
    dir: &Path,
    out: &mut BTreeMap<PathBuf, BoundedRegularFile>,
    depth: usize,
    visited: &mut usize,
    retained_bytes: &mut usize,
) -> Result<(), CliError> {
    reject_source_path(dir)?;
    if depth > MAX_IMPORT_DIRECTORY_DEPTH {
        return Err(CliError::new("import_dir"));
    }
    let directory = open_directory_no_follow(dir, "import_dir")?;
    collect_cert_files_from_directory(directory, dir, out, depth, visited, retained_bytes)
}

fn collect_cert_files_from_directory(
    directory: File,
    display_path: &Path,
    out: &mut BTreeMap<PathBuf, BoundedRegularFile>,
    depth: usize,
    visited: &mut usize,
    retained_bytes: &mut usize,
) -> Result<(), CliError> {
    let mut names = directory_names(&directory, "import_dir")?;
    names.sort();
    for name in names {
        *visited = visited
            .checked_add(1)
            .ok_or_else(|| CliError::new("import_dir"))?;
        if *visited > MAX_IMPORT_DIRECTORY_ENTRIES {
            return Err(CliError::new("import_dir"));
        }
        let path = display_path.join(&name);
        let child = open_child_no_follow(&directory, &name, "import_dir")?;
        let metadata = child.metadata().map_err(|_| CliError::new("import_dir"))?;
        if metadata.is_dir() {
            if depth >= MAX_IMPORT_DIRECTORY_DEPTH {
                return Err(CliError::new("import_dir"));
            }
            collect_cert_files_from_directory(
                child,
                &path,
                out,
                depth + 1,
                visited,
                retained_bytes,
            )?;
        } else if metadata.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("npcert")
        {
            let remaining = MAX_IMPORT_CANDIDATE_BYTES
                .checked_sub(*retained_bytes)
                .ok_or_else(|| CliError::new("imports"))?;
            let candidate = read_bounded_open_file(child, remaining, "imports")?;
            *retained_bytes = retained_bytes
                .checked_add(candidate.bytes.len())
                .ok_or_else(|| CliError::new("imports"))?;
            out.insert(path, candidate);
            if out.len() > MAX_IMPORT_CANDIDATES {
                return Err(CliError::new("imports"));
            }
        } else if !metadata.is_file() {
            return Err(CliError::new("import_dir"));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FileIdentity {
    device: u64,
    inode: u64,
}

struct BoundedRegularFile {
    bytes: Vec<u8>,
    identity: FileIdentity,
}

#[cfg(unix)]
fn file_identity(metadata: &fs::Metadata) -> FileIdentity {
    use std::os::unix::fs::MetadataExt as _;

    FileIdentity {
        device: metadata.dev(),
        inode: metadata.ino(),
    }
}

#[cfg(not(unix))]
fn file_identity(metadata: &fs::Metadata) -> FileIdentity {
    FileIdentity {
        device: metadata.len(),
        inode: 0,
    }
}

fn read_bounded_regular_file(
    path: &Path,
    maximum_bytes: usize,
    section: &'static str,
) -> Result<Vec<u8>, CliError> {
    Ok(read_bounded_regular_file_with_identity(path, maximum_bytes, section)?.bytes)
}

fn read_bounded_regular_file_with_identity(
    path: &Path,
    maximum_bytes: usize,
    section: &'static str,
) -> Result<BoundedRegularFile, CliError> {
    let file = open_regular_no_follow(path, section)?;
    read_bounded_open_file(file, maximum_bytes, section)
}

fn read_bounded_open_file(
    mut file: File,
    maximum_bytes: usize,
    section: &'static str,
) -> Result<BoundedRegularFile, CliError> {
    let metadata = file.metadata().map_err(|_| CliError::new(section))?;
    if !metadata.file_type().is_file() || metadata.len() > maximum_bytes as u64 {
        return Err(CliError::new(section));
    }
    let mut bytes = Vec::with_capacity(
        usize::try_from(metadata.len())
            .unwrap_or(maximum_bytes)
            .min(maximum_bytes),
    );
    std::io::Read::by_ref(&mut file)
        .take(maximum_bytes.saturating_add(1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|_| CliError::new(section))?;
    if bytes.len() > maximum_bytes {
        return Err(CliError::new(section));
    }
    Ok(BoundedRegularFile {
        bytes,
        identity: file_identity(&metadata),
    })
}

#[cfg(unix)]
fn open_regular_no_follow(path: &Path, section: &'static str) -> Result<File, CliError> {
    open_path_no_follow(path, false, section)
}

#[cfg(unix)]
fn open_directory_no_follow(path: &Path, section: &'static str) -> Result<File, CliError> {
    open_path_no_follow(path, true, section)
}

#[cfg(unix)]
fn open_path_no_follow(
    path: &Path,
    expect_directory: bool,
    section: &'static str,
) -> Result<File, CliError> {
    use rustix::fs::{openat, Mode, OFlags, CWD};

    if path.as_os_str().is_empty() {
        return Err(CliError::new(section));
    }
    let absolute = path.is_absolute();
    let mut names = Vec::<OsString>::new();
    for component in path.components() {
        match component {
            Component::RootDir | Component::CurDir => {}
            Component::Normal(name) => names.push(name.to_owned()),
            Component::ParentDir => {
                if !absolute
                    && names
                        .last()
                        .is_none_or(|name| name.as_os_str() == OsStr::new(".."))
                {
                    names.push(OsString::from(".."));
                } else if names.pop().is_none() {
                    return Err(CliError::new(section));
                }
            }
            Component::Prefix(_) => return Err(CliError::new(section)),
        }
    }
    if cfg!(target_os = "macos")
        && absolute
        && names
            .first()
            .is_some_and(|name| name == OsStr::new("var") || name == OsStr::new("tmp"))
    {
        names.insert(0, OsString::from("private"));
    }
    let descriptor = if absolute {
        openat(
            CWD,
            "/",
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::DIRECTORY | OFlags::NOFOLLOW,
            Mode::empty(),
        )
    } else {
        openat(
            CWD,
            ".",
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::DIRECTORY | OFlags::NOFOLLOW,
            Mode::empty(),
        )
    }
    .map_err(|_| CliError::new(section))?;
    let mut current = File::from(descriptor);
    let names_len = names.len();
    for (index, name) in names.into_iter().enumerate() {
        let final_component = index + 1 == names_len;
        let flags = if !final_component || expect_directory {
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::DIRECTORY | OFlags::NOFOLLOW
        } else {
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK
        };
        current = File::from(
            openat(&current, &name, flags, Mode::empty()).map_err(|_| CliError::new(section))?,
        );
    }
    let metadata = current.metadata().map_err(|_| CliError::new(section))?;
    if (expect_directory && !metadata.is_dir()) || (!expect_directory && !metadata.is_file()) {
        return Err(CliError::new(section));
    }
    Ok(current)
}

#[cfg(unix)]
fn open_child_no_follow(
    parent: &File,
    name: &OsStr,
    section: &'static str,
) -> Result<File, CliError> {
    use rustix::fs::{openat, Mode, OFlags};

    // NONBLOCK ensures a hostile FIFO cannot block before its type is known.
    openat(
        parent,
        name,
        OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK,
        Mode::empty(),
    )
    .map(File::from)
    .map_err(|_| CliError::new(section))
}

#[cfg(unix)]
fn directory_names(directory: &File, section: &'static str) -> Result<Vec<OsString>, CliError> {
    use rustix::fs::Dir;

    let descriptor = directory.try_clone().map_err(|_| CliError::new(section))?;
    let reader = Dir::read_from(descriptor).map_err(|_| CliError::new(section))?;
    let mut names = Vec::new();
    for entry in reader {
        let entry = entry.map_err(|_| CliError::new(section))?;
        let bytes = entry.file_name().to_bytes();
        if bytes != b"." && bytes != b".." {
            use std::os::unix::ffi::OsStringExt as _;
            names.push(OsString::from_vec(bytes.to_vec()));
        }
    }
    Ok(names)
}

#[cfg(not(unix))]
fn open_regular_no_follow(path: &Path, section: &'static str) -> Result<File, CliError> {
    let metadata = fs::symlink_metadata(path).map_err(|_| CliError::new(section))?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(CliError::new(section));
    }
    File::open(path).map_err(|_| CliError::new(section))
}

#[cfg(not(unix))]
fn open_directory_no_follow(path: &Path, section: &'static str) -> Result<File, CliError> {
    let metadata = fs::symlink_metadata(path).map_err(|_| CliError::new(section))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err(CliError::new(section));
    }
    File::open(path).map_err(|_| CliError::new(section))
}

#[cfg(not(unix))]
fn open_child_no_follow(
    _parent: &File,
    _name: &OsStr,
    section: &'static str,
) -> Result<File, CliError> {
    Err(CliError::new(section))
}

#[cfg(not(unix))]
fn directory_names(_directory: &File, section: &'static str) -> Result<Vec<OsString>, CliError> {
    Err(CliError::new(section))
}

fn parse_import_lock_manifest(source: &str) -> Result<Vec<ImportLockEntry>, CliError> {
    let value = ImportLockJsonParser::new(source).parse_document()?;
    let members = json_object(value)?;
    let [imports_value, schema_value] = exact_object_fields(members, ["imports", "schema"])?;
    if json_value_string(schema_value)? != "npa.independent-checker.import_lock_manifest.v1" {
        return Err(CliError::new("imports"));
    }
    let values = json_array(imports_value)?;
    if values.len() > MAX_IMPORT_CANDIDATES {
        return Err(CliError::new("imports"));
    }
    let entries = values
        .into_iter()
        .map(parse_import_lock_entry)
        .collect::<Result<Vec<_>, _>>()?;
    validate_import_lock_entries(&entries)?;
    Ok(entries)
}

enum ImportLockJsonValue {
    String(String),
    Array(Vec<ImportLockJsonValue>),
    Object(Vec<(String, ImportLockJsonValue)>),
}

struct ImportLockJsonParser<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> ImportLockJsonParser<'a> {
    const fn new(source: &'a str) -> Self {
        Self { source, offset: 0 }
    }

    fn parse_document(mut self) -> Result<ImportLockJsonValue, CliError> {
        let value = self.value(0)?;
        self.skip_ws();
        if self.offset != self.source.len() {
            return Err(CliError::new("imports"));
        }
        Ok(value)
    }

    fn value(&mut self, depth: usize) -> Result<ImportLockJsonValue, CliError> {
        if depth > 8 {
            return Err(CliError::new("imports"));
        }
        self.skip_ws();
        match self.source.as_bytes().get(self.offset) {
            Some(b'"') => self.string().map(ImportLockJsonValue::String),
            Some(b'[') => self.array(depth + 1),
            Some(b'{') => self.object(depth + 1),
            _ => Err(CliError::new("imports")),
        }
    }

    fn array(&mut self, depth: usize) -> Result<ImportLockJsonValue, CliError> {
        self.expect_byte(b'[')?;
        let mut values = Vec::new();
        if !self.peek_byte(b']') {
            loop {
                if values.len() == MAX_IMPORT_CANDIDATES {
                    return Err(CliError::new("imports"));
                }
                values.push(self.value(depth)?);
                if !self.peek_byte(b',') {
                    break;
                }
                self.expect_byte(b',')?;
            }
        }
        self.expect_byte(b']')?;
        Ok(ImportLockJsonValue::Array(values))
    }

    fn object(&mut self, depth: usize) -> Result<ImportLockJsonValue, CliError> {
        self.expect_byte(b'{')?;
        let mut members = Vec::new();
        if !self.peek_byte(b'}') {
            loop {
                if members.len() == 8 {
                    return Err(CliError::new("imports"));
                }
                let key = self.string()?;
                self.expect_byte(b':')?;
                members.push((key, self.value(depth)?));
                if !self.peek_byte(b',') {
                    break;
                }
                self.expect_byte(b',')?;
            }
        }
        self.expect_byte(b'}')?;
        Ok(ImportLockJsonValue::Object(members))
    }

    fn string(&mut self) -> Result<String, CliError> {
        self.skip_ws();
        if self.take_byte() != Some(b'"') {
            return Err(CliError::new("imports"));
        }
        let mut out = String::new();
        while self.offset < self.source.len() {
            let ch = self.source[self.offset..]
                .chars()
                .next()
                .ok_or_else(|| CliError::new("imports"))?;
            self.offset += ch.len_utf8();
            match ch {
                '"' => return Ok(out),
                '\\' => {
                    let escaped = self.take_byte().ok_or_else(|| CliError::new("imports"))?;
                    match escaped {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => out.push(self.unicode_escape()?),
                        _ => return Err(CliError::new("imports")),
                    }
                }
                '\u{0000}'..='\u{001f}' => return Err(CliError::new("imports")),
                _ => out.push(ch),
            }
        }
        Err(CliError::new("imports"))
    }

    fn unicode_escape(&mut self) -> Result<char, CliError> {
        let high = self.hex_u16()?;
        let scalar = if (0xd800..=0xdbff).contains(&high) {
            if self.take_byte() != Some(b'\\') || self.take_byte() != Some(b'u') {
                return Err(CliError::new("imports"));
            }
            let low = self.hex_u16()?;
            if !(0xdc00..=0xdfff).contains(&low) {
                return Err(CliError::new("imports"));
            }
            0x10000 + ((u32::from(high - 0xd800) << 10) | u32::from(low - 0xdc00))
        } else if (0xdc00..=0xdfff).contains(&high) {
            return Err(CliError::new("imports"));
        } else {
            u32::from(high)
        };
        char::from_u32(scalar).ok_or_else(|| CliError::new("imports"))
    }

    fn hex_u16(&mut self) -> Result<u16, CliError> {
        let mut value = 0_u16;
        for _ in 0..4 {
            let byte = self.take_byte().ok_or_else(|| CliError::new("imports"))?;
            value =
                (value << 4) | u16::from(hex_nibble(byte).map_err(|_| CliError::new("imports"))?);
        }
        Ok(value)
    }

    fn expect_byte(&mut self, expected: u8) -> Result<(), CliError> {
        self.skip_ws();
        (self.take_byte() == Some(expected))
            .then_some(())
            .ok_or_else(|| CliError::new("imports"))
    }

    fn peek_byte(&mut self, expected: u8) -> bool {
        self.skip_ws();
        self.source.as_bytes().get(self.offset) == Some(&expected)
    }

    fn take_byte(&mut self) -> Option<u8> {
        let byte = self.source.as_bytes().get(self.offset).copied()?;
        self.offset += 1;
        Some(byte)
    }

    fn skip_ws(&mut self) {
        while self
            .source
            .as_bytes()
            .get(self.offset)
            .is_some_and(|byte| matches!(byte, b' ' | b'\n' | b'\r' | b'\t'))
        {
            self.offset += 1;
        }
    }
}

fn parse_import_lock_entry(value: ImportLockJsonValue) -> Result<ImportLockEntry, CliError> {
    let members = json_object(value)?;
    let [certificate, export_hash, module] =
        exact_object_fields(members, ["certificate", "export_hash", "module"])?;
    let module = json_value_string(module)?;
    if npa_checker_ref::ReferenceModuleName::from_dotted(&module).is_err() {
        return Err(CliError::new("imports"));
    }
    let export_hash =
        parse_hash_arg(&json_value_string(export_hash)?).map_err(|_| CliError::new("imports"))?;
    let certificate_members = json_object(certificate)?;
    let [certificate_hash, file_hash, kind, path] = exact_object_fields(
        certificate_members,
        ["certificate_hash", "file_hash", "kind", "path"],
    )?;
    if json_value_string(kind)? != "path" {
        return Err(CliError::new("imports"));
    }
    let path = json_value_string(path)?;
    if !valid_workspace_relative_path(&path) {
        return Err(CliError::new("imports"));
    }
    Ok(ImportLockEntry {
        module,
        export_hash,
        path,
        file_hash: parse_hash_arg(&json_value_string(file_hash)?)
            .map_err(|_| CliError::new("imports"))?,
        certificate_hash: parse_hash_arg(&json_value_string(certificate_hash)?)
            .map_err(|_| CliError::new("imports"))?,
    })
}

fn exact_object_fields<const N: usize>(
    members: Vec<(String, ImportLockJsonValue)>,
    expected: [&str; N],
) -> Result<[ImportLockJsonValue; N], CliError> {
    if members.len() != N {
        return Err(CliError::new("imports"));
    }
    let mut slots = expected.map(|_| None);
    for (key, value) in members {
        let Some(index) = expected.iter().position(|expected| *expected == key) else {
            return Err(CliError::new("imports"));
        };
        if slots[index].replace(value).is_some() {
            return Err(CliError::new("imports"));
        }
    }
    let mut values = Vec::with_capacity(N);
    for slot in slots {
        values.push(slot.ok_or_else(|| CliError::new("imports"))?);
    }
    values.try_into().map_err(|_| CliError::new("imports"))
}

fn json_object(value: ImportLockJsonValue) -> Result<Vec<(String, ImportLockJsonValue)>, CliError> {
    match value {
        ImportLockJsonValue::Object(members) => Ok(members),
        _ => Err(CliError::new("imports")),
    }
}

fn json_array(value: ImportLockJsonValue) -> Result<Vec<ImportLockJsonValue>, CliError> {
    match value {
        ImportLockJsonValue::Array(values) => Ok(values),
        _ => Err(CliError::new("imports")),
    }
}

fn json_value_string(value: ImportLockJsonValue) -> Result<String, CliError> {
    match value {
        ImportLockJsonValue::String(value) => Ok(value),
        _ => Err(CliError::new("imports")),
    }
}

fn valid_workspace_relative_path(value: &str) -> bool {
    !value.is_empty()
        && !value.starts_with('/')
        && !value.contains('\\')
        && !value.contains(':')
        && !value.contains("://")
        && !value.bytes().any(|byte| byte <= 0x20 || byte == 0x7f)
        && value
            .split('/')
            .all(|segment| !segment.is_empty() && segment != "." && segment != "..")
}

fn validate_import_lock_entries(entries: &[ImportLockEntry]) -> Result<(), CliError> {
    let mut modules = BTreeSet::new();
    let mut paths = BTreeSet::new();
    let mut certificate_hashes = BTreeSet::new();
    let mut file_hashes = BTreeSet::new();
    for (index, entry) in entries.iter().enumerate() {
        if index != 0 && import_lock_sort_key(&entries[index - 1]) > import_lock_sort_key(entry) {
            return Err(CliError::new("imports"));
        }
        if !modules.insert(&entry.module)
            || !paths.insert(&entry.path)
            || !certificate_hashes.insert(entry.certificate_hash)
            || !file_hashes.insert(entry.file_hash)
        {
            return Err(CliError::new("imports"));
        }
    }
    Ok(())
}

fn import_lock_sort_key(entry: &ImportLockEntry) -> (Vec<u8>, &str, ReferenceHash, ReferenceHash) {
    let mut canonical_name = Vec::new();
    if let Ok(name) = npa_checker_ref::ReferenceModuleName::from_dotted(&entry.module) {
        encode_uvar(&mut canonical_name, name.components().len());
        for component in name.components() {
            encode_uvar(&mut canonical_name, component.len());
            canonical_name.extend_from_slice(component.as_bytes());
        }
    } else {
        canonical_name.extend_from_slice(entry.module.as_bytes());
    }
    (
        canonical_name,
        &entry.path,
        entry.certificate_hash,
        entry.file_hash,
    )
}

fn encode_uvar(out: &mut Vec<u8>, mut value: usize) {
    while value >= 0x80 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn raw_checked_json(
    input_certificate_format: &str,
    input_core_spec: &str,
    module: String,
    certificate_hash: &ReferenceHash,
    export_hash: &ReferenceHash,
    axiom_report_hash: &ReferenceHash,
) -> String {
    format!(
        "{{\"schema\":\"{}\",\"checker_id\":\"{}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"certificate_format\":\"{}\",\"core_spec\":\"{}\",\"input_certificate_format\":{},\"input_core_spec\":{},\"status\":\"checked\",\"module\":{},\"certificate_hash\":\"{}\",\"export_hash\":\"{}\",\"axiom_report_hash\":\"{}\"}}",
        CHECKER_RAW_RESULT_SCHEMA,
        REFERENCE_CHECKER_ID,
        REFERENCE_CHECKER_VERSION,
        format_hash(&reference_checker_build_hash()),
        REFERENCE_CERTIFICATE_FORMAT,
        REFERENCE_CORE_SPEC,
        json_string(input_certificate_format),
        json_string(input_core_spec),
        json_string(&module),
        format_hash(certificate_hash),
        format_hash(export_hash),
        format_hash(axiom_report_hash)
    )
}

fn raw_rejected_json(
    error: &ReferenceCheckError,
    decoded: Option<&npa_checker_ref::ReferenceDecodedCertificate>,
    input_pair: Option<&(String, String)>,
) -> String {
    let mut fields = vec![
        format!("\"schema\":\"{}\"", CHECKER_RAW_RESULT_SCHEMA),
        format!("\"checker_id\":\"{}\"", REFERENCE_CHECKER_ID),
        format!("\"checker_version\":\"{}\"", REFERENCE_CHECKER_VERSION),
        format!(
            "\"checker_build_hash\":\"{}\"",
            format_hash(&reference_checker_build_hash())
        ),
        format!(
            "\"certificate_format\":\"{}\"",
            REFERENCE_CERTIFICATE_FORMAT
        ),
        format!("\"core_spec\":\"{}\"", REFERENCE_CORE_SPEC),
    ];
    if let Some((certificate_format, core_spec)) = input_pair {
        fields.push(format!(
            "\"input_certificate_format\":{}",
            json_string(certificate_format)
        ));
        fields.push(format!("\"input_core_spec\":{}", json_string(core_spec)));
    }
    fields.push("\"status\":\"failed\"".to_owned());
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

fn raw_input_pair(bytes: &[u8]) -> Option<(String, String)> {
    fn string_at(bytes: &[u8], offset: &mut usize) -> Option<String> {
        let start = *offset;
        let mut value = 0_u64;
        let mut shift = 0_u32;
        loop {
            let byte = *bytes.get(*offset)?;
            *offset += 1;
            value |= u64::from(byte & 0x7f).checked_shl(shift)?;
            if byte & 0x80 == 0 {
                break;
            }
            shift = shift.checked_add(7)?;
            if shift >= 64 {
                return None;
            }
        }
        let length_bytes = &bytes[start..*offset];
        let mut canonical = Vec::new();
        let mut remaining = value;
        loop {
            let mut byte = (remaining & 0x7f) as u8;
            remaining >>= 7;
            if remaining != 0 {
                byte |= 0x80;
            }
            canonical.push(byte);
            if remaining == 0 {
                break;
            }
        }
        if canonical != length_bytes {
            return None;
        }
        let len = usize::try_from(value).ok()?;
        let end = offset.checked_add(len)?;
        let value = std::str::from_utf8(bytes.get(*offset..end)?)
            .ok()?
            .to_owned();
        *offset = end;
        Some(value)
    }

    let mut offset = 0;
    let format = string_at(bytes, &mut offset)?;
    let core_spec = string_at(bytes, &mut offset)?;
    // This header-only observation is untrusted rejection metadata. Recognizing
    // a known pair here does not select a semantic decoder; `decode_certificate`
    // still accepts only the exact current pair.
    matches!(
        (format.as_str(), core_spec.as_str()),
        ("NPA-CERT-0.4.0", "NPA-Core-0.4.0")
            | ("NPA-CERT-0.3.0", "NPA-Core-0.3.0")
            | ("NPA-CERT-0.2.0", "NPA-Core-0.2.0")
            | ("NPA-CERT-0.1.2", "NPA-Core-0.1.2")
            | ("NPA-CERT-0.1", "NPA-Core-0.1")
    )
    .then_some((format, core_spec))
}

fn raw_error_json(error: &ReferenceCheckError) -> String {
    let mut fields = vec![format!("\"kind\":\"{}\"", raw_error_kind(error))];
    let reason_code = match error.reason {
        Some(ReferenceCheckReason::HashMismatch {
            object:
                ReferenceHashObject::DeclInterface
                | ReferenceHashObject::DeclInterfaceDependencyMaterial,
        }) => Some("decl_interface_hash_mismatch"),
        Some(ReferenceCheckReason::HashMismatch {
            object:
                ReferenceHashObject::DeclCertificate
                | ReferenceHashObject::DeclCertificateDependencyMaterial,
        }) => Some("decl_certificate_hash_mismatch"),
        Some(ReferenceCheckReason::ConstructorUniverseBoundViolation) => {
            Some("constructor_universe_bound_violation")
        }
        Some(ReferenceCheckReason::UnknownReference) => Some("unknown_reference"),
        Some(ReferenceCheckReason::ResourceLimit) => Some("resource_limit"),
        Some(ReferenceCheckReason::WrongReferenceKind) => Some("wrong_reference_kind"),
        Some(ReferenceCheckReason::TargetNotEarlier) => Some("target_not_earlier"),
        Some(ReferenceCheckReason::TargetNotOpaque) => Some("target_not_opaque"),
        Some(ReferenceCheckReason::InterfaceHashMismatch) => Some("interface_hash_mismatch"),
        Some(ReferenceCheckReason::CertificateHashMismatch) => Some("certificate_hash_mismatch"),
        Some(ReferenceCheckReason::MissingImplementationDependency) => {
            Some("missing_implementation_dependency")
        }
        Some(ReferenceCheckReason::SurplusImplementationDependency) => {
            Some("surplus_implementation_dependency")
        }
        _ => None,
    };
    if let Some(reason_code) = reason_code {
        fields.push(format!("\"reason_code\":\"{reason_code}\""));
    }
    if let Some(reference) = &error.reference {
        let (declaration, core_path) = reference_projection(reference);
        if let Some(declaration) = declaration {
            fields.push(format!("\"declaration\":{}", json_string(&declaration)));
        }
        if !core_path.is_empty() {
            fields.push(format!(
                "\"core_path\":[{}]",
                core_path
                    .iter()
                    .map(|token| json_string(token))
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
    }
    if let Some(limit) = error.structural_limit {
        fields.push(format!(
            "\"expected_value\":{}",
            json_string(&format!("{}<={}", limit.kind.as_str(), limit.limit))
        ));
        fields.push(format!(
            "\"actual_value\":{}",
            json_string(&limit.observed.to_string())
        ));
    }
    fields.push(format!(
        "\"section\":{}",
        json_string(section_name(error.section))
    ));
    fields.push(format!("\"offset\":{}", error.offset));
    format!("{{{}}}", fields.join(","))
}

fn append_import_identity(path: &mut Vec<String>, identity: &ReferenceCheckResolvedImportIdentity) {
    path.push(format!("module={}", identity.module.dotted()));
    path.push(format!(
        "export_hash={}",
        format_hash(&identity.export_hash)
    ));
}

fn append_import_target(path: &mut Vec<String>, target: &ReferenceCheckImportTarget) {
    match target {
        ReferenceCheckImportTarget::Unresolved { import_index, .. } => {
            path.push(format!("imports[{import_index}]"));
        }
        ReferenceCheckImportTarget::Resolved(identity) => {
            path.push(format!("imports[{}]", identity.import_index));
            append_import_identity(path, identity);
        }
        _ => {}
    }
}

fn append_owner_import_path(
    path: &mut Vec<String>,
    owner_import: &ReferenceCheckResolvedImportIdentity,
) {
    path.push(format!("imports[{}]", owner_import.import_index));
    append_import_identity(path, owner_import);
    path.push("public_environment".to_owned());
}

fn reference_projection(reference: &ReferenceCheckReference) -> (Option<String>, Vec<String>) {
    match reference {
        ReferenceCheckReference::Builtin { declaration, .. } => (
            Some(declaration.dotted()),
            vec!["reference".to_owned(), "builtin".to_owned()],
        ),
        ReferenceCheckReference::Imported {
            owner_import,
            import,
            declaration,
            ..
        } => {
            let mut path = vec!["reference".to_owned(), "imported".to_owned()];
            if let Some(owner_import) = owner_import {
                append_owner_import_path(&mut path, owner_import);
            }
            append_import_target(&mut path, import);
            (Some(declaration.dotted()), path)
        }
        ReferenceCheckReference::Local {
            owner_import,
            declaration_index,
            declaration,
            ..
        } => {
            let mut path = if let Some(owner_import) = owner_import {
                let mut path = vec!["reference".to_owned(), "imported".to_owned()];
                append_owner_import_path(&mut path, owner_import);
                path.push("local".to_owned());
                path
            } else {
                vec!["reference".to_owned(), "local".to_owned()]
            };
            path.push(format!("declarations[{declaration_index}]"));
            (declaration.as_ref().map(|name| name.dotted()), path)
        }
        ReferenceCheckReference::LocalGenerated {
            owner_import,
            declaration_index,
            declaration,
            ..
        } => {
            let mut path = if let Some(owner_import) = owner_import {
                let mut path = vec!["reference".to_owned(), "imported".to_owned()];
                append_owner_import_path(&mut path, owner_import);
                path.push("local_generated".to_owned());
                path
            } else {
                vec!["reference".to_owned(), "local_generated".to_owned()]
            };
            path.push(format!("declarations[{declaration_index}]"));
            (Some(declaration.dotted()), path)
        }
        _ => (None, Vec::new()),
    }
}

fn raw_internal_error_json(section: &'static str, offset: usize) -> String {
    format!(
        "{{\"schema\":\"{}\",\"checker_id\":\"{}\",\"checker_version\":\"{}\",\"checker_build_hash\":\"{}\",\"certificate_format\":\"{}\",\"core_spec\":\"{}\",\"status\":\"failed\",\"error\":{{\"kind\":\"checker_internal_error\",\"reason_code\":\"checker_reported_internal_error\",\"section\":{},\"offset\":{}}}}}",
        CHECKER_RAW_RESULT_SCHEMA,
        REFERENCE_CHECKER_ID,
        REFERENCE_CHECKER_VERSION,
        format_hash(&reference_checker_build_hash()),
        REFERENCE_CERTIFICATE_FORMAT,
        REFERENCE_CORE_SPEC,
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
                object:
                    ReferenceHashObject::DeclInterfaceDependencyMaterial
                    | ReferenceHashObject::DeclCertificateDependencyMaterial,
            }) => "dependency_hash_mismatch",
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
            | Some(ReferenceCheckReason::UnresolvedMetavariable)
            | Some(ReferenceCheckReason::ConstructorUniverseBoundViolation) => {
                "universe_inconsistency"
            }
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
        let mut path = fs::canonicalize(env::temp_dir()).unwrap();
        path.push(format!("npa-checker-ref-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        path
    }

    #[cfg(unix)]
    #[test]
    fn no_follow_open_accepts_parent_relative_directories() {
        use std::os::unix::fs::MetadataExt as _;

        let current = env::current_dir().unwrap();
        let current_name = current.file_name().unwrap();
        let selected = PathBuf::from("..").join(current_name);
        let reopened = open_directory_no_follow(&selected, "test").unwrap();
        let reopened = reopened.metadata().unwrap();
        let retained = fs::metadata(".").unwrap();

        assert_eq!(
            (reopened.dev(), reopened.ino()),
            (retained.dev(), retained.ino())
        );
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

    fn import_lock_entry(module: &str, path: &str, bytes: &[u8]) -> String {
        let decoded = decode_certificate(bytes).unwrap();
        format!(
            "{{\"certificate\":{{\"certificate_hash\":\"{}\",\"file_hash\":\"{}\",\"kind\":\"path\",\"path\":{}}},\"export_hash\":\"{}\",\"module\":{}}}",
            format_hash(&decoded.hashes().certificate_hash),
            format_hash(&sha256(bytes)),
            json_string(path),
            format_hash(&decoded.hashes().export_hash),
            json_string(module),
        )
    }

    fn import_lock_manifest(entries: &[String]) -> String {
        format!(
            "{{\"imports\":[{}],\"schema\":\"npa.independent-checker.import_lock_manifest.v1\"}}",
            entries.join(",")
        )
    }

    #[test]
    fn import_lock_parser_accepts_the_closed_canonical_contract() {
        let logic = minimal_certificate("Std.Logic");
        let nat = minimal_certificate("Std.Nat");
        let manifest = import_lock_manifest(&[
            import_lock_entry("Std.Nat", "build/certs/Std/Nat", &nat),
            import_lock_entry("Std.Logic", "build/certs/Std/Logic", &logic),
        ]);

        let parsed = parse_import_lock_manifest(&manifest).unwrap();
        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0].module, "Std.Nat");
        assert_eq!(parsed[0].path, "build/certs/Std/Nat");
        assert_eq!(parsed[0].file_hash, sha256(&nat));
        assert_eq!(parsed[1].module, "Std.Logic");

        // Object member order is JSON-insignificant, while domain order is
        // the canonical module-name/path/hash order frozen by the API.
        let reordered_members = manifest.replace(
            "{\"imports\":[",
            "{\"schema\":\"npa.independent-checker.import_lock_manifest.v1\",\"imports\":[",
        );
        let reordered_members = reordered_members.replace(
            "],\"schema\":\"npa.independent-checker.import_lock_manifest.v1\"}",
            "]}",
        );
        assert_eq!(
            parse_import_lock_manifest(&reordered_members).unwrap(),
            parsed
        );
    }

    #[test]
    fn import_lock_parser_rejects_schema_shape_and_domain_drift() {
        let a = minimal_certificate("A.Module");
        let b = minimal_certificate("B.Module");
        let first = import_lock_entry("A.Module", "build/certs/a.bin", &a);
        let second = import_lock_entry("B.Module", "build/certs/b.bin", &b);
        let valid = import_lock_manifest(&[first.clone(), second.clone()]);
        for invalid in [
            valid.replace("import_lock_manifest.v1", "import_lock_manifest.v2"),
            valid.replace("\"schema\":", "\"unknown\":\"x\",\"schema\":"),
            valid.replace(
                "\"module\":\"A.Module\"",
                "\"module\":\"A.Module\",\"module\":\"A.Module\"",
            ),
            valid.replace("\"kind\":\"path\",", ""),
            valid.replace("build/certs/a.bin", "../a.bin"),
            import_lock_manifest(&[second, first]),
        ] {
            assert!(parse_import_lock_manifest(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn import_lock_entry_identity_is_bound_to_actual_certificate_bytes() {
        let bytes = minimal_certificate("Locked.Module");
        let entry = parse_import_lock_manifest(&import_lock_manifest(&[import_lock_entry(
            "Locked.Module",
            "build/certs/locked.bin",
            &bytes,
        )]))
        .unwrap()
        .pop()
        .unwrap();
        let decoded = decode_certificate(&bytes).unwrap();
        assert_eq!(sha256(&bytes), entry.file_hash);
        assert_eq!(decoded.header().module.dotted(), entry.module);
        assert_eq!(decoded.hashes().export_hash, entry.export_hash);
        assert_eq!(decoded.hashes().certificate_hash, entry.certificate_hash);
        validate_locked_import_candidate(&entry, &bytes).unwrap();

        let mut changed = bytes;
        changed.push(0);
        assert_ne!(sha256(&changed), entry.file_hash);
        assert_eq!(
            validate_locked_import_candidate(&entry, &changed)
                .unwrap_err()
                .section,
            "imports_hash"
        );

        let mut wrong_module = entry.clone();
        wrong_module.module = "Other.Module".to_owned();
        let mut wrong_export = entry.clone();
        wrong_export.export_hash[0] ^= 1;
        let mut wrong_certificate = entry;
        wrong_certificate.certificate_hash[0] ^= 1;
        for mismatched in [wrong_module, wrong_export, wrong_certificate] {
            assert!(
                validate_locked_import_candidate(&mismatched, &changed[..changed.len() - 1])
                    .is_err()
            );
        }
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

        assert_eq!(code, 0, "{json}");
        assert!(json.contains("\"schema\":\"npa.independent-checker.checker_raw_result.v2\""));
        assert!(json.contains("\"checker_id\":\"npa-checker-ref\""));
        assert!(json.contains("\"certificate_format\":\"NPA-CERT-0.4.0\""));
        assert!(json.contains("\"core_spec\":\"NPA-Core-0.4.0\""));
        assert!(json.contains("\"input_certificate_format\":\"NPA-CERT-0.4.0\""));
        assert!(json.contains("\"input_core_spec\":\"NPA-Core-0.4.0\""));
        assert!(json.contains("\"status\":\"checked\""));
        assert!(json.contains("\"module\":\"Cli.Empty\""));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn cli_reports_old_pair_only_as_untrusted_rejection_metadata() {
        let dir = temp_dir("old-pair");
        let cert_path = dir.join("Cli.OldPair.npcert");
        let mut bytes = minimal_certificate("Cli.OldPair");
        let format_offset = bytes
            .windows(REFERENCE_CERTIFICATE_FORMAT.len())
            .position(|window| window == REFERENCE_CERTIFICATE_FORMAT.as_bytes())
            .unwrap();
        bytes[format_offset..format_offset + REFERENCE_CERTIFICATE_FORMAT.len()]
            .copy_from_slice(b"NPA-CERT-0.3.0");
        let core_offset = bytes
            .windows(REFERENCE_CORE_SPEC.len())
            .position(|window| window == REFERENCE_CORE_SPEC.as_bytes())
            .unwrap();
        bytes[core_offset..core_offset + REFERENCE_CORE_SPEC.len()]
            .copy_from_slice(b"NPA-Core-0.3.0");
        fs::write(&cert_path, bytes).unwrap();

        let (json, code) = run_with_args([
            "--json".to_owned(),
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);

        assert_eq!(code, 1, "{json}");
        assert!(json.contains("\"certificate_format\":\"NPA-CERT-0.4.0\""));
        assert!(json.contains("\"core_spec\":\"NPA-Core-0.4.0\""));
        assert!(json.contains("\"input_certificate_format\":\"NPA-CERT-0.3.0\""));
        assert!(json.contains("\"input_core_spec\":\"NPA-Core-0.3.0\""));
        assert!(json.contains("\"status\":\"failed\""));
        assert!(json.contains("\"kind\":\"certificate_decode_error\""));
        assert!(json.contains("\"section\":\"header_format\""));
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
    fn cli_policy_rejects_legacy_json_and_caller_overrides() {
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

        assert_eq!(code, 2);
        assert!(json.contains("\"kind\":\"checker_internal_error\""));
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
              format = "npa.independent-checker.axiom_policy.v1"
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
    fn cli_policy_requires_the_closed_axiom_schema_without_elevating_import_trust() {
        let valid = r#"format = "npa.independent-checker.axiom_policy.v1"
allowed_axioms = []
"#;
        let policy = parse_policy_text(valid).unwrap();
        assert_eq!(policy.trust_mode, ReferenceTrustMode::Normal);
        assert!(policy.deny_sorry);
        assert!(policy.deny_custom_axioms);
        assert!(policy.allow_standard_axiom_exceptions);
        for invalid in [
            "allowed_axioms = []",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = []\ndeny_custom_axioms = false",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = []\nallowed_axioms = []",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallow_axioms = []",
            "format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = null",
        ] {
            assert!(parse_policy_text(invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn raw_error_reports_constructor_universe_bound_reason() {
        let json = raw_error_json(&ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 17,
            reason: Some(ReferenceCheckReason::ConstructorUniverseBoundViolation),
            reference: None,
            structural_limit: None,
        });

        assert!(json.contains("\"kind\":\"universe_inconsistency\""));
        assert!(json.contains("\"reason_code\":\"constructor_universe_bound_violation\""));
    }

    #[test]
    fn raw_dependency_hash_mismatch_preserves_declaration_role() {
        for (object, expected_reason) in [
            (
                ReferenceHashObject::DeclInterfaceDependencyMaterial,
                "decl_interface_hash_mismatch",
            ),
            (
                ReferenceHashObject::DeclCertificateDependencyMaterial,
                "decl_certificate_hash_mismatch",
            ),
        ] {
            let error = ReferenceCheckError {
                kind: ReferenceCheckErrorKind::HashMismatch,
                section: ReferenceCertificateSection::Declarations,
                offset: 17,
                reason: Some(ReferenceCheckReason::HashMismatch { object }),
                reference: None,
                structural_limit: None,
            };
            let json = raw_error_json(&error);
            assert!(json.contains("\"kind\":\"dependency_hash_mismatch\""));
            assert!(json.contains(&format!("\"reason_code\":\"{expected_reason}\"")));
        }
    }

    fn reference_name(value: &str) -> npa_checker_ref::ReferenceModuleName {
        npa_checker_ref::ReferenceModuleName::from_dotted(value).unwrap()
    }

    #[test]
    fn raw_unknown_reference_projects_nested_import_identity() {
        let owner = ReferenceCheckResolvedImportIdentity::new(
            0,
            reference_name("Owner.Module"),
            [0xab; 32],
        );
        let target = ReferenceCheckResolvedImportIdentity::new(
            3,
            reference_name("Std.Logic.Eq"),
            [0xcd; 32],
        );
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 417,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(ReferenceCheckReference::Imported {
                owner_import: Some(owner),
                import: ReferenceCheckImportTarget::Resolved(target),
                declaration: reference_name("Std.Logic.Eq.rec"),
                decl_interface_hash: [0xef; 32],
            }),
            structural_limit: None,
        };

        assert_eq!(
            raw_error_json(&error),
            format!(
                "{{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"declaration\":\"Std.Logic.Eq.rec\",\"core_path\":[\"reference\",\"imported\",\"imports[0]\",\"module=Owner.Module\",\"export_hash={}\",\"public_environment\",\"imports[3]\",\"module=Std.Logic.Eq\",\"export_hash={}\"],\"section\":\"declarations\",\"offset\":417}}",
                format_hash(&[0xab; 32]),
                format_hash(&[0xcd; 32]),
            )
        );
    }

    #[test]
    fn raw_unknown_reference_omits_unavailable_import_identity() {
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 29,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(ReferenceCheckReference::Imported {
                owner_import: None,
                import: ReferenceCheckImportTarget::Unresolved { import_index: 7 },
                declaration: reference_name("Missing.value"),
                decl_interface_hash: [0x11; 32],
            }),
            structural_limit: None,
        };

        assert_eq!(
            raw_error_json(&error),
            "{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"declaration\":\"Missing.value\",\"core_path\":[\"reference\",\"imported\",\"imports[7]\"],\"section\":\"declarations\",\"offset\":29}"
        );
    }

    #[test]
    fn raw_unknown_reference_projects_builtin_local_and_generated_lanes() {
        let cases = [
            (
                ReferenceCheckReference::Builtin {
                    declaration: reference_name("Eq.refl"),
                    decl_interface_hash: [0x01; 32],
                },
                "\"declaration\":\"Eq.refl\",\"core_path\":[\"reference\",\"builtin\"]",
            ),
            (
                ReferenceCheckReference::Local {
                    owner_import: None,
                    declaration_index: 2,
                    declaration: Some(reference_name("Current.local")),
                },
                "\"declaration\":\"Current.local\",\"core_path\":[\"reference\",\"local\",\"declarations[2]\"]",
            ),
            (
                ReferenceCheckReference::LocalGenerated {
                    owner_import: None,
                    declaration_index: 4,
                    declaration: reference_name("Current.generated"),
                },
                "\"declaration\":\"Current.generated\",\"core_path\":[\"reference\",\"local_generated\",\"declarations[4]\"]",
            ),
        ];

        for (reference, expected) in cases {
            let error = ReferenceCheckError {
                kind: ReferenceCheckErrorKind::TypeCheck,
                section: ReferenceCertificateSection::Declarations,
                offset: 5,
                reason: Some(ReferenceCheckReason::UnknownReference),
                reference: Some(reference),
                structural_limit: None,
            };
            assert!(raw_error_json(&error).contains(expected));
        }
    }

    #[test]
    fn raw_unknown_reference_projects_imported_environment_local_lanes() {
        let owner = ReferenceCheckResolvedImportIdentity::new(
            2,
            reference_name("Owner.Module"),
            [0x22; 32],
        );
        let cases = [
            (
                ReferenceCheckReference::Local {
                    owner_import: Some(owner.clone()),
                    declaration_index: 6,
                    declaration: None,
                },
                format!(
                    "\"core_path\":[\"reference\",\"imported\",\"imports[2]\",\"module=Owner.Module\",\"export_hash={}\",\"public_environment\",\"local\",\"declarations[6]\"]",
                    format_hash(&[0x22; 32])
                ),
                None,
            ),
            (
                ReferenceCheckReference::LocalGenerated {
                    owner_import: Some(owner),
                    declaration_index: 8,
                    declaration: reference_name("Imported.generated"),
                },
                format!(
                    "\"core_path\":[\"reference\",\"imported\",\"imports[2]\",\"module=Owner.Module\",\"export_hash={}\",\"public_environment\",\"local_generated\",\"declarations[8]\"]",
                    format_hash(&[0x22; 32])
                ),
                Some("\"declaration\":\"Imported.generated\""),
            ),
        ];

        for (reference, expected_path, expected_declaration) in cases {
            let error = ReferenceCheckError {
                kind: ReferenceCheckErrorKind::TypeCheck,
                section: ReferenceCertificateSection::Declarations,
                offset: 5,
                reason: Some(ReferenceCheckReason::UnknownReference),
                reference: Some(reference),
                structural_limit: None,
            };
            let json = raw_error_json(&error);
            assert!(json.contains(&expected_path), "{json}");
            if let Some(expected_declaration) = expected_declaration {
                assert!(json.contains(expected_declaration), "{json}");
            } else {
                assert!(!json.contains("\"declaration\""), "{json}");
            }
        }
    }

    #[test]
    fn raw_context_free_universe_unknown_reference_emits_only_reason_and_location() {
        let error = ReferenceCheckError {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section: ReferenceCertificateSection::Declarations,
            offset: 13,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: None,
            structural_limit: None,
        };

        assert_eq!(
            raw_error_json(&error),
            "{\"kind\":\"type_mismatch\",\"reason_code\":\"unknown_reference\",\"section\":\"declarations\",\"offset\":13}"
        );
        assert_eq!(json_string("a\"b\\c\n"), "\"a\\\"b\\\\c\\n\"");
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

    #[test]
    fn cli_input_files_are_bounded_before_allocation() {
        let dir = temp_dir("bounded-inputs");
        let cert_path = dir.join("oversized.npcert");
        let policy_path = dir.join("oversized-policy.json");
        let imports_path = dir.join("oversized-lock.json");
        for (path, length, args) in [
            (
                &cert_path,
                MAX_CERTIFICATE_BYTES as u64 + 2,
                vec![
                    "--cert".to_owned(),
                    cert_path.display().to_string(),
                    "--output".to_owned(),
                    "json".to_owned(),
                ],
            ),
            (
                &policy_path,
                MAX_POLICY_BYTES as u64 + 1,
                vec![
                    "--cert".to_owned(),
                    dir.join("small.npcert").display().to_string(),
                    "--policy".to_owned(),
                    policy_path.display().to_string(),
                    "--output".to_owned(),
                    "json".to_owned(),
                ],
            ),
            (
                &imports_path,
                MAX_IMPORT_LOCK_BYTES as u64 + 1,
                vec![
                    "--cert".to_owned(),
                    dir.join("small.npcert").display().to_string(),
                    "--imports".to_owned(),
                    imports_path.display().to_string(),
                    "--output".to_owned(),
                    "json".to_owned(),
                ],
            ),
        ] {
            let file = File::create(path).unwrap();
            file.set_len(length).unwrap();
            fs::write(dir.join("small.npcert"), minimal_certificate("Cli.Small")).unwrap();
            assert_eq!(run_with_args(args).1, 2, "{}", path.display());
        }
        let _ = fs::remove_dir_all(dir);
    }

    #[cfg(unix)]
    #[test]
    fn cli_import_directory_rejects_symbolic_links() {
        use std::os::unix::fs::symlink;

        let dir = temp_dir("symlink-imports");
        let cert_path = dir.join("Cli.Empty.npcert");
        let import_dir = dir.join("imports");
        fs::create_dir(&import_dir).unwrap();
        fs::write(&cert_path, minimal_certificate("Cli.Empty")).unwrap();
        let outside = dir.join("outside.npcert");
        fs::write(&outside, minimal_certificate("Cli.Outside")).unwrap();
        symlink(&outside, import_dir.join("linked.npcert")).unwrap();

        let (_, code) = run_with_args([
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--import-dir".to_owned(),
            import_dir.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);
        assert_eq!(code, 2);
        assert!(outside.exists());
        let _ = fs::remove_dir_all(dir);
    }

    #[cfg(unix)]
    #[test]
    fn cli_inputs_reject_intermediate_symlinks_and_directory_swap_out() {
        use std::os::unix::fs::symlink;

        let dir = fs::canonicalize(temp_dir("intermediate-symlink-inputs")).unwrap();
        let outside = fs::canonicalize(temp_dir("intermediate-symlink-inputs-outside")).unwrap();
        fs::write(
            outside.join("certificate.npcert"),
            minimal_certificate("Cli.Outside"),
        )
        .unwrap();
        symlink(&outside, dir.join("linked")).unwrap();
        let (_, code) = run_with_args([
            "--cert".to_owned(),
            dir.join("linked/certificate.npcert").display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);
        assert_eq!(code, 2);

        let import_dir = dir.join("imports");
        fs::create_dir(&import_dir).unwrap();
        let candidate = import_dir.join("candidate.npcert");
        fs::write(&candidate, minimal_certificate("Cli.Candidate")).unwrap();
        let mut files = BTreeMap::new();
        let mut visited = 0;
        let mut retained = 0;
        let directory = open_directory_no_follow(&import_dir, "import_dir").unwrap();
        fs::rename(&import_dir, dir.join("relocated")).unwrap();
        fs::create_dir(&import_dir).unwrap();
        fs::write(import_dir.join("replacement.npcert"), b"replacement").unwrap();
        collect_cert_files_from_directory(
            directory,
            &import_dir,
            &mut files,
            1,
            &mut visited,
            &mut retained,
        )
        .unwrap();
        assert_eq!(files.len(), 1);
        assert!(files.contains_key(&candidate));
        assert_eq!(
            files[&candidate].bytes,
            minimal_certificate("Cli.Candidate")
        );

        let _ = fs::remove_dir_all(dir);
        let _ = fs::remove_dir_all(outside);
    }

    #[cfg(unix)]
    #[test]
    fn cli_import_lock_rejects_intermediate_symlink_certificate_paths() {
        use std::os::unix::fs::symlink;

        let dir = fs::canonicalize(temp_dir("import-lock-symlink")).unwrap();
        let outside = fs::canonicalize(temp_dir("import-lock-symlink-outside")).unwrap();
        let cert_path = dir.join("leaf.npcert");
        let import_bytes = minimal_certificate("Imported.Module");
        fs::write(&cert_path, minimal_certificate("Cli.Leaf")).unwrap();
        fs::write(outside.join("import.npcert"), &import_bytes).unwrap();
        symlink(&outside, dir.join("linked")).unwrap();
        let manifest_path = dir.join("imports.json");
        fs::write(
            &manifest_path,
            import_lock_manifest(&[import_lock_entry(
                "Imported.Module",
                dir.join("linked/import.npcert").to_str().unwrap(),
                &import_bytes,
            )]),
        )
        .unwrap();

        let (_, code) = run_with_args([
            "--cert".to_owned(),
            cert_path.display().to_string(),
            "--imports".to_owned(),
            manifest_path.display().to_string(),
            "--output".to_owned(),
            "json".to_owned(),
        ]);
        assert_eq!(code, 2);

        let _ = fs::remove_dir_all(dir);
        let _ = fs::remove_dir_all(outside);
    }
}
