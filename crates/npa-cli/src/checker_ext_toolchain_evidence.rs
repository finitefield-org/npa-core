//! Deterministic evidence support for the current external-checker toolchain gate.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::os::unix::fs::{symlink, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use npa_api::{JsonDocument, JsonValue, JsonValueKind};
use sha2::{Digest, Sha256};

const SCHEMA: &str = "npa.checker_ext.toolchain_v0_7";
const POLICY_ID: &str = "npa-checker-ext-toolchain-v0-7-compat";
const EXTERNAL_BINARY_ID: &str = "npa-checker-ext-toolchain-v0-7-real";
const RUNNER_ID: &str = "npa-cli-package-external-runner";
const RUNNER_VERSION: &str = "0.1.0";
const IDENTITY_PATH: &str = "ci/checker-identity-manifest.json";
const POLICY_PATH: &str = "ci/runner.release.json";
const REGISTRY_PATH: &str = "ci/checker-binaries.json";
const AXIOM_POLICY_PATH: &str = "ci/axiom-policy.toml";
const CHECKER_PATH: &str = "tools/checkers/npa-checker-ext";
const RETAINED_JSON: [&str; 6] = [
    "axiom-report.json",
    "package-lock.json",
    "publish-plan.json",
    "theorem-index.json",
    "theorem-premise-report.json",
    "verified-export-summary.json",
];
const MUTABLE_PREFIXES: [&str; 2] = ["generated/checker-imports/", "generated/checker-results/"];

/// Failure returned by the evidence policy and schema layer.
#[derive(Debug)]
pub struct EvidenceError(pub String);

impl std::fmt::Display for EvidenceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for EvidenceError {}

type Result<T> = std::result::Result<T, EvidenceError>;

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    fn parse_file(path: &Path) -> Result<Self> {
        let source = fs::read_to_string(path).map_err(|error| {
            EvidenceError(format!("cannot read JSON {}: {error}", path.display()))
        })?;
        let document = JsonDocument::parse(&source).map_err(|error| {
            EvidenceError(format!(
                "cannot parse JSON {} at byte {}",
                path.display(),
                error.offset
            ))
        })?;
        convert_json(document.root(), "$", path)
    }

    fn object(entries: impl IntoIterator<Item = (impl Into<String>, Value)>) -> Self {
        Self::Object(
            entries
                .into_iter()
                .map(|(key, value)| (key.into(), value))
                .collect(),
        )
    }

    fn string(value: impl Into<String>) -> Self {
        Self::String(value.into())
    }

    fn get(&self, key: &str) -> Option<&Self> {
        match self {
            Self::Object(entries) => entries.get(key),
            _ => None,
        }
    }

    fn get_mut(&mut self, key: &str) -> Option<&mut Self> {
        match self {
            Self::Object(entries) => entries.get_mut(key),
            _ => None,
        }
    }

    fn as_object(&self) -> Option<&BTreeMap<String, Self>> {
        match self {
            Self::Object(entries) => Some(entries),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<&[Self]> {
        match self {
            Self::Array(values) => Some(values),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    fn canonical(&self) -> String {
        let mut output = String::new();
        render_json(self, &mut output);
        output.push('\n');
        output
    }
}

fn convert_json(value: &JsonValue<'_>, pointer: &str, path: &Path) -> Result<Value> {
    match value.kind() {
        JsonValueKind::Null => Ok(Value::Null),
        JsonValueKind::Bool => Ok(Value::Bool(value.bool_value().unwrap())),
        JsonValueKind::Number => Ok(Value::Number(value.number_raw().unwrap().to_owned())),
        JsonValueKind::String => Ok(Value::String(value.string_value().unwrap().to_owned())),
        JsonValueKind::Array => value
            .array_elements()
            .unwrap()
            .iter()
            .enumerate()
            .map(|(index, child)| convert_json(child, &format!("{pointer}[{index}]"), path))
            .collect::<Result<Vec<_>>>()
            .map(Value::Array),
        JsonValueKind::Object => {
            let mut entries = BTreeMap::new();
            for member in value.object_members().unwrap() {
                if entries.contains_key(member.key()) {
                    return Err(EvidenceError(format!(
                        "duplicate JSON field in {} at {pointer}.{}",
                        path.display(),
                        member.key()
                    )));
                }
                entries.insert(
                    member.key().to_owned(),
                    convert_json(member.value(), &format!("{pointer}.{}", member.key()), path)?,
                );
            }
            Ok(Value::Object(entries))
        }
    }
}

fn render_json(value: &Value, output: &mut String) {
    match value {
        Value::Null => output.push_str("null"),
        Value::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        Value::Number(value) => output.push_str(value),
        Value::String(value) => {
            output.push('"');
            for character in value.chars() {
                match character {
                    '"' => output.push_str("\\\""),
                    '\\' => output.push_str("\\\\"),
                    '\n' => output.push_str("\\n"),
                    '\r' => output.push_str("\\r"),
                    '\t' => output.push_str("\\t"),
                    value if value < '\u{20}' => {
                        write!(output, "\\u{:04x}", u32::from(value)).unwrap()
                    }
                    value => output.push(value),
                }
            }
            output.push('"');
        }
        Value::Array(values) => {
            output.push('[');
            for (index, value) in values.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                render_json(value, output);
            }
            output.push(']');
        }
        Value::Object(entries) => {
            output.push('{');
            for (index, (key, value)) in entries.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                render_json(&Value::String(key.clone()), output);
                output.push(':');
                render_json(value, output);
            }
            output.push('}');
        }
    }
}

fn sha256_bytes(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn read_bytes(path: &Path) -> Result<Vec<u8>> {
    fs::read(path)
        .map_err(|error| EvidenceError(format!("cannot read {}: {error}", path.display())))
}

fn write_json(path: &Path, value: &Value) -> Result<Vec<u8>> {
    let bytes = value.canonical().into_bytes();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| EvidenceError(error.to_string()))?;
    }
    fs::write(path, &bytes).map_err(|error| EvidenceError(error.to_string()))?;
    Ok(bytes)
}

fn require(condition: bool, message: impl Into<String>) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(EvidenceError(message.into()))
    }
}

fn canonical(path: &Path) -> Result<PathBuf> {
    path.canonicalize()
        .map_err(|error| EvidenceError(format!("cannot resolve {}: {error}", path.display())))
}

fn run_git(root: &Path, args: &[&str], environment: &[(&str, &str)]) -> Result<String> {
    let mut command = Command::new("/usr/bin/git");
    command.arg("-C").arg(root).args(args);
    command.envs(environment.iter().copied());
    let result = command
        .output()
        .map_err(|error| EvidenceError(error.to_string()))?;
    require(
        result.status.success(),
        format!(
            "git command failed: {}",
            String::from_utf8_lossy(&result.stderr).trim()
        ),
    )?;
    Ok(String::from_utf8_lossy(&result.stdout).trim().to_owned())
}

fn parse_version_record(bytes: &[u8]) -> Result<BTreeMap<String, String>> {
    let text = std::str::from_utf8(bytes)
        .map_err(|_| EvidenceError("checker --version output is not UTF-8".into()))?;
    require(
        text.ends_with('\n') && !text.ends_with("\n\n"),
        "checker --version must have exactly one final LF",
    )?;
    let lines = text.trim_end_matches('\n').split('\n').collect::<Vec<_>>();
    require(
        lines.len() == 9,
        format!(
            "checker --version must have nine lines, got {}",
            lines.len()
        ),
    )?;
    let literals = [
        (0, "npa-checker-ext 0.2.0"),
        (2, "certificate_format NPA-CERT-0.2.0"),
        (3, "core_spec NPA-Core-0.2.0"),
        (4, "implementation_profile ocaml-clean-room"),
        (5, "project_directory checkers/npa-checker-ext/"),
        (
            6,
            "feature_policy_contract m0-05:first-release-empty-core-feature-set",
        ),
        (
            7,
            "vendored_sha256_source_identity vendored-sha256-source:v1",
        ),
        (8, "checker_identity_manifest_signature_required false"),
    ];
    for (index, literal) in literals {
        require(
            lines[index] == literal,
            format!("checker --version line {} mismatch", index + 1),
        )?;
    }
    let build_hash = lines[1]
        .strip_prefix("checker_build_hash ")
        .ok_or_else(|| EvidenceError("checker --version build hash is invalid".into()))?;
    require(
        build_hash.len() == 71
            && build_hash.starts_with("sha256:")
            && build_hash[7..]
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()),
        "checker --version build hash is invalid",
    )?;
    Ok(BTreeMap::from([
        ("checker_id".into(), "npa-checker-ext".into()),
        ("checker_version".into(), "0.2.0".into()),
        ("checker_build_hash".into(), build_hash.into()),
        ("version_text_sha256".into(), sha256_bytes(bytes)),
    ]))
}

fn fixture_hash(label: &str) -> String {
    sha256_bytes(label.as_bytes())
}

/// Prepare the current v0.7 checker identity, registry, axiom policy, and runner policy.
pub fn prepare_inputs(root: &Path, checker: &Path, version_file: &Path) -> Result<String> {
    let root = canonical(root)?;
    require(
        root.is_dir(),
        format!("package root is not a directory: {}", root.display()),
    )?;
    let checker_bytes = read_bytes(checker)?;
    let version_bytes = read_bytes(version_file)?;
    let observed = parse_version_record(&version_bytes)?;
    let checker_target = root.join(CHECKER_PATH);
    fs::create_dir_all(checker_target.parent().unwrap())
        .map_err(|error| EvidenceError(error.to_string()))?;
    fs::write(&checker_target, &checker_bytes).map_err(|error| EvidenceError(error.to_string()))?;
    fs::set_permissions(&checker_target, fs::Permissions::from_mode(0o755))
        .map_err(|error| EvidenceError(error.to_string()))?;
    let checker_hash = sha256_bytes(&checker_bytes);

    let axiom_bytes =
        b"format = \"npa.independent-checker.axiom_policy.v1\"\nallowed_axioms = []\n";
    let axiom_path = root.join(AXIOM_POLICY_PATH);
    fs::create_dir_all(axiom_path.parent().unwrap())
        .map_err(|error| EvidenceError(error.to_string()))?;
    fs::write(&axiom_path, axiom_bytes).map_err(|error| EvidenceError(error.to_string()))?;
    let axiom_hash = sha256_bytes(axiom_bytes);
    let label = "npa-checker-ext-toolchain-v0.7.0-fixture";
    let runner_build_hash = fixture_hash(&format!("{RUNNER_ID}:{RUNNER_VERSION}"));
    let fast_binary_hash = fixture_hash(&format!("{label}:fast-kernel:binary"));
    let fast_build_hash = fixture_hash(&format!("{label}:fast-kernel:build"));
    let reference_binary_hash = fixture_hash(&format!("{label}:reference:binary"));
    let reference_build_hash = fixture_hash(&format!("{label}:reference:build"));
    let observed_value = |key: &str| Value::string(observed.get(key).unwrap());
    let checker_record =
        |profile: &str, id: &str, binary_id: &str, binary_hash: &str, build_hash: &str| {
            Value::object([
                ("binary_hash", Value::string(binary_hash)),
                ("binary_id", Value::string(binary_id)),
                ("build_hash", Value::string(build_hash)),
                ("checker_id", Value::string(id)),
                ("profile", Value::string(profile)),
            ])
        };
    let identity = Value::object([
        (
            "checkers",
            Value::Array(vec![
                Value::object([
                    ("binary_hash", Value::string(&checker_hash)),
                    ("binary_id", Value::string(EXTERNAL_BINARY_ID)),
                    ("build_hash", observed_value("checker_build_hash")),
                    ("checker_id", observed_value("checker_id")),
                    ("checker_version", observed_value("checker_version")),
                    ("profile", Value::string("external")),
                ]),
                checker_record(
                    "fast-kernel",
                    "npa-fast-kernel",
                    "npa-fast-kernel-toolchain-v0-7-fixture",
                    &fast_binary_hash,
                    &fast_build_hash,
                ),
                checker_record(
                    "reference",
                    "npa-checker-ref",
                    "npa-checker-ref-toolchain-v0-7-fixture",
                    &reference_binary_hash,
                    &reference_build_hash,
                ),
            ]),
        ),
        (
            "generated_by",
            Value::object([
                ("runner_build_hash", Value::string(&runner_build_hash)),
                ("runner_id", Value::string(RUNNER_ID)),
                ("runner_version", Value::string(RUNNER_VERSION)),
            ]),
        ),
        (
            "schema",
            Value::string("npa.independent-checker.checker_identity_manifest.v1"),
        ),
    ]);
    let identity_bytes = write_json(&root.join(IDENTITY_PATH), &identity)?;
    let identity_hash = sha256_bytes(&identity_bytes);
    let registry = Value::object([
        (
            "entries",
            Value::Array(vec![Value::object([
                ("binary_id", Value::string(EXTERNAL_BINARY_ID)),
                ("path", Value::string(CHECKER_PATH)),
            ])]),
        ),
        ("root_kind", Value::string("workspace")),
        (
            "schema",
            Value::string("npa.independent-checker.checker_binary_registry.v1"),
        ),
    ]);
    let registry_bytes = write_json(&root.join(REGISTRY_PATH), &registry)?;
    let registry_hash = sha256_bytes(&registry_bytes);
    let budget = || {
        Value::object([
            ("max_memory_mb", Value::Number("2048".into())),
            ("max_steps", Value::Number("10000000".into())),
            ("timeout_ms", Value::Number("60000".into())),
        ])
    };
    let allow = |profile: &str,
                 id: &str,
                 binary_id: &str,
                 binary_hash: &str,
                 build_hash: &str,
                 args: Vec<Value>| {
        Value::object([
            ("allowed_args", Value::Array(args)),
            ("binary_hash", Value::string(binary_hash)),
            ("binary_id", Value::string(binary_id)),
            ("build_hash", Value::string(build_hash)),
            ("checker_id", Value::string(id)),
            ("profile", Value::string(profile)),
        ])
    };
    let policy = Value::object([
        (
            "axiom_policy",
            Value::object([
                ("hash", Value::string(&axiom_hash)),
                ("path", Value::string(AXIOM_POLICY_PATH)),
            ]),
        ),
        (
            "budgets",
            Value::object([
                ("external", budget()),
                ("fast-kernel", budget()),
                ("reference", budget()),
            ]),
        ),
        (
            "checker_allowlist",
            Value::Array(vec![
                allow(
                    "external",
                    observed.get("checker_id").unwrap(),
                    EXTERNAL_BINARY_ID,
                    &checker_hash,
                    observed.get("checker_build_hash").unwrap(),
                    vec![],
                ),
                allow(
                    "fast-kernel",
                    "npa-fast-kernel",
                    "npa-fast-kernel-toolchain-v0-7-fixture",
                    &fast_binary_hash,
                    &fast_build_hash,
                    vec![Value::string("--json"), Value::string("--canonical-only")],
                ),
                allow(
                    "reference",
                    "npa-checker-ref",
                    "npa-checker-ref-toolchain-v0-7-fixture",
                    &reference_binary_hash,
                    &reference_build_hash,
                    vec![Value::string("--json"), Value::string("--canonical-only")],
                ),
            ]),
        ),
        (
            "checker_identity_manifest",
            Value::object([
                ("kind", Value::string("file")),
                ("manifest_hash", Value::string(&identity_hash)),
                ("path", Value::string(IDENTITY_PATH)),
            ]),
        ),
        ("id", Value::string(POLICY_ID)),
        (
            "import_policy",
            Value::object([
                ("mode", Value::string("locked_store")),
                ("network", Value::string("forbidden")),
                ("require_import_lock_hash", Value::Bool(true)),
            ]),
        ),
        ("on_missing_required_checker", Value::string("fail")),
        (
            "on_profile_requested_by_ai",
            Value::string("ignore_unless_policy_allows"),
        ),
        ("on_resource_exhausted", Value::string("fail")),
        ("optional_checker_profiles", Value::Array(vec![])),
        (
            "required_checker_profiles",
            Value::Array(vec![
                Value::string("fast-kernel"),
                Value::string("reference"),
                Value::string("external"),
            ]),
        ),
        (
            "schema",
            Value::string("npa.independent-checker.runner_policy.v1"),
        ),
        ("trust_mode", Value::string("release")),
        ("version", Value::Number("1".into())),
    ]);
    let policy_bytes = write_json(&root.join(POLICY_PATH), &policy)?;
    let mut entries = vec![
        (
            "axiom_policy_path".to_owned(),
            Value::string(AXIOM_POLICY_PATH),
        ),
        ("axiom_policy_sha256".to_owned(), Value::string(&axiom_hash)),
        (
            "checker_binary_path".to_owned(),
            Value::string(CHECKER_PATH),
        ),
        (
            "checker_binary_sha256".to_owned(),
            Value::string(&checker_hash),
        ),
        (
            "checker_registry_path".to_owned(),
            Value::string(REGISTRY_PATH),
        ),
        (
            "checker_registry_sha256".to_owned(),
            Value::string(&registry_hash),
        ),
        (
            "identity_manifest_path".to_owned(),
            Value::string(IDENTITY_PATH),
        ),
        (
            "identity_manifest_sha256".to_owned(),
            Value::string(&identity_hash),
        ),
        ("root".to_owned(), Value::string(root.to_string_lossy())),
        (
            "runner_policy_file_sha256".to_owned(),
            Value::string(sha256_bytes(&policy_bytes)),
        ),
        ("runner_policy_path".to_owned(), Value::string(POLICY_PATH)),
        (
            "schema".to_owned(),
            Value::string(format!("{SCHEMA}.prepared_inputs.v1")),
        ),
    ];
    entries.extend(
        observed
            .into_iter()
            .map(|(key, value)| (key, Value::string(value))),
    );
    Ok(Value::object(entries).canonical())
}

fn copy_tree(source: &Path, destination: &Path) -> Result<()> {
    fs::create_dir(destination).map_err(|error| EvidenceError(error.to_string()))?;
    let mut entries = fs::read_dir(source)
        .map_err(|error| EvidenceError(error.to_string()))?
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|error| EvidenceError(error.to_string()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let target = destination.join(entry.file_name());
        let metadata =
            fs::symlink_metadata(&path).map_err(|error| EvidenceError(error.to_string()))?;
        if metadata.file_type().is_symlink() {
            symlink(
                fs::read_link(path).map_err(|error| EvidenceError(error.to_string()))?,
                target,
            )
            .map_err(|error| EvidenceError(error.to_string()))?;
        } else if metadata.is_dir() {
            copy_tree(&path, &target)?;
        } else if metadata.is_file() {
            fs::copy(path, target).map_err(|error| EvidenceError(error.to_string()))?;
        }
    }
    Ok(())
}

/// Build the deterministic temporary source fixture used by the v0.7 gate.
pub fn prepare_fixture(run_dir: &Path, fixture: &Path, core_root: &Path) -> Result<String> {
    let run_dir = if run_dir.exists() {
        canonical(run_dir)?
    } else {
        run_dir.to_path_buf()
    };
    if run_dir.exists() {
        require(
            fs::read_dir(&run_dir)
                .map_err(|error| EvidenceError(error.to_string()))?
                .next()
                .is_none(),
            format!("run directory is not empty: {}", run_dir.display()),
        )?;
    } else {
        fs::create_dir_all(&run_dir).map_err(|error| EvidenceError(error.to_string()))?;
    }
    let fixture = canonical(fixture)?;
    let core_root = canonical(core_root)?;
    let source = run_dir.join("source");
    let package = source.join("proofs");
    fs::create_dir(&source).map_err(|error| EvidenceError(error.to_string()))?;
    for path in [run_dir.join("evidence"), run_dir.join("assets")] {
        fs::create_dir(path).map_err(|error| EvidenceError(error.to_string()))?;
    }
    for label in ["facade", "direct-1", "direct-final"] {
        fs::create_dir(run_dir.join("evidence").join(label))
            .map_err(|error| EvidenceError(error.to_string()))?;
    }
    copy_tree(&fixture, &package)?;
    let generated = package.join("generated");
    let mut actual = fs::read_dir(&generated)
        .map_err(|error| EvidenceError(error.to_string()))?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            entry.path().is_file() && entry.path().extension().is_some_and(|ext| ext == "json")
        })
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    actual.sort();
    require(
        actual == RETAINED_JSON,
        format!("fixture top-level generated JSON mismatch: got {actual:?}"),
    )?;
    for prefix in MUTABLE_PREFIXES {
        require(
            !package.join(prefix.trim_end_matches('/')).exists(),
            format!("fixture contains pre-existing mutable tree: {prefix}"),
        )?;
    }
    let sentinels = [
        ("Downstream/MathlibBasic/replay.json", "replay"),
        ("Downstream/MathlibBasic/meta.json", "meta"),
        ("Downstream/MathlibBasic/ai-trace.json", "ai"),
        ("plugins/forbidden-plugin.json", "plugin"),
    ];
    for (locator, label) in sentinels {
        let path = package.join(locator);
        fs::create_dir_all(path.parent().unwrap())
            .map_err(|error| EvidenceError(error.to_string()))?;
        fs::write(
            path,
            format!("{{\"forbidden\":\"npa-checker-ext-toolchain-v0.7.0:{label}\"}}\n"),
        )
        .map_err(|error| EvidenceError(error.to_string()))?;
    }
    fs::write(
        source.join(".gitignore"),
        "/npa-core\n/proofs/ci/\n/proofs/tools/\n/proofs/generated/\n",
    )
    .map_err(|error| EvidenceError(error.to_string()))?;
    run_git(&source, &["init", "--object-format=sha1", "--quiet"], &[])?;
    run_git(
        &source,
        &["config", "user.name", "NPA Checker Compatibility"],
        &[],
    )?;
    run_git(
        &source,
        &["config", "user.email", "npa-checker-ext@invalid"],
        &[],
    )?;
    run_git(&source, &["add", "--all"], &[])?;
    run_git(
        &source,
        &[
            "commit",
            "--quiet",
            "-m",
            "npa-checker-ext toolchain v0.7.0 compatibility fixture",
        ],
        &[
            ("GIT_AUTHOR_DATE", "2000-01-01T00:00:00Z"),
            ("GIT_COMMITTER_DATE", "2000-01-01T00:00:00Z"),
        ],
    )?;
    let head = run_git(&source, &["rev-parse", "HEAD"], &[])?;
    require(
        head.len() == 40 && head.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "temporary source commit is not SHA-1",
    )?;
    require(
        run_git(
            &source,
            &["status", "--porcelain=v1", "--untracked-files=all"],
            &[],
        )?
        .is_empty(),
        "temporary source repository is not clean after commit",
    )?;
    symlink(core_root, source.join("npa-core"))
        .map_err(|error| EvidenceError(error.to_string()))?;
    let lock = Value::parse_file(&generated.join("package-lock.json"))?;
    require(
        lock.get("package").and_then(Value::as_str) == Some("npa-mathlib-downstream")
            && lock.get("version").and_then(Value::as_str) == Some("0.1.0"),
        "fixture package lock identity mismatch",
    )?;
    let entries = lock
        .get("entries")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("package lock entries must be an array".into()))?;
    let mut by_module = BTreeMap::new();
    for entry in entries {
        let module = entry
            .get("module")
            .and_then(Value::as_str)
            .ok_or_else(|| EvidenceError("package lock entry has invalid module".into()))?;
        require(
            by_module.insert(module.to_owned(), entry).is_none(),
            format!("duplicate package lock module: {module}"),
        )?;
    }
    let order = ["Mathlib.Logic.Basic", "Downstream.MathlibBasic"];
    require(
        by_module
            .keys()
            .all(|module| order.contains(&module.as_str())),
        "fixture package lock module mismatch",
    )?;
    let artifacts = order.iter().map(|module| Value::string(format!("generated/checker-results/npa-mathlib-downstream/0.1.0/{module}/external/result.json"))).collect();
    let mut proofs = BTreeMap::new();
    for module in order {
        let entry = by_module[module];
        let identity = [
            "certificate",
            "certificate_file_hash",
            "certificate_hash",
            "export_hash",
            "axiom_report_hash",
        ]
        .into_iter()
        .map(|field| {
            (
                field.to_owned(),
                entry.get(field).cloned().unwrap_or(Value::Null),
            )
        })
        .collect();
        proofs.insert(module.to_owned(), Value::Object(identity));
    }
    Ok(Value::object([
        ("artifact_paths", Value::Array(artifacts)),
        (
            "assets_root",
            Value::string(run_dir.join("assets").to_string_lossy()),
        ),
        ("diagnostic_count", Value::Number("4".into())),
        (
            "evidence_root",
            Value::string(run_dir.join("evidence").to_string_lossy()),
        ),
        (
            "module_order",
            Value::Array(order.into_iter().map(Value::string).collect()),
        ),
        ("package_root", Value::string(package.to_string_lossy())),
        ("package_root_locator", Value::string("proofs")),
        ("proof_identities", Value::Object(proofs)),
        (
            "retained_generated_paths",
            Value::Array(
                RETAINED_JSON
                    .into_iter()
                    .map(|name| Value::string(format!("generated/{name}")))
                    .collect(),
            ),
        ),
        ("run_dir", Value::string(run_dir.to_string_lossy())),
        ("schema", Value::string(format!("{SCHEMA}.fixture.v1"))),
        (
            "sentinel_paths",
            Value::Array(
                sentinels
                    .into_iter()
                    .map(|(path, _)| Value::string(path))
                    .collect(),
            ),
        ),
        ("source_commit", Value::string(head)),
        ("source_root", Value::string(source.to_string_lossy())),
    ])
    .canonical())
}

fn walk_files(root: &Path, path: &Path, output: &mut BTreeMap<String, Value>) -> Result<()> {
    let mut entries = fs::read_dir(path)
        .map_err(|error| EvidenceError(error.to_string()))?
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|error| EvidenceError(error.to_string()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let relative = path
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        if relative == ".git"
            || relative.starts_with(".git/")
            || MUTABLE_PREFIXES.iter().any(|prefix| {
                relative == prefix.trim_end_matches('/') || relative.starts_with(prefix)
            })
        {
            continue;
        }
        let metadata =
            fs::symlink_metadata(&path).map_err(|error| EvidenceError(error.to_string()))?;
        if metadata.file_type().is_symlink() {
            output.insert(
                relative,
                Value::object([
                    ("kind", Value::string("symlink")),
                    (
                        "target",
                        Value::string(
                            fs::read_link(path)
                                .map_err(|error| EvidenceError(error.to_string()))?
                                .to_string_lossy(),
                        ),
                    ),
                ]),
            );
        } else if metadata.is_dir() {
            walk_files(root, &path, output)?;
        } else if metadata.is_file() {
            output.insert(
                relative,
                Value::object([
                    ("kind", Value::string("file")),
                    ("sha256", Value::string(sha256_bytes(&read_bytes(&path)?))),
                ]),
            );
        }
    }
    Ok(())
}

/// Inventory protected package files and explicitly named host artifacts.
pub fn inventory(root: &Path, extras: &[PathBuf]) -> Result<String> {
    let root = canonical(root)?;
    require(
        root.is_dir(),
        format!("inventory root is not a directory: {}", root.display()),
    )?;
    let mut files = BTreeMap::new();
    walk_files(&root, &root, &mut files)?;
    let mut extra_files = BTreeMap::new();
    for extra in extras {
        let resolved = canonical(extra)?;
        require(
            resolved.is_file(),
            format!("inventory extra is not a file: {}", extra.display()),
        )?;
        extra_files.insert(
            resolved.to_string_lossy().into_owned(),
            Value::object([
                ("kind", Value::string("file")),
                (
                    "sha256",
                    Value::string(sha256_bytes(&read_bytes(&resolved)?)),
                ),
            ]),
        );
    }
    Ok(Value::object([
        ("extra_files", Value::Object(extra_files)),
        ("files", Value::Object(files)),
        ("root", Value::string(root.to_string_lossy())),
        ("schema", Value::string(format!("{SCHEMA}.inventory.v1"))),
    ])
    .canonical())
}

fn safe_artifact_path(root: &Path, locator: &str) -> Result<PathBuf> {
    require(
        !locator.is_empty() && !locator.contains('\\'),
        format!("artifact locator is not canonical: {locator:?}"),
    )?;
    let path = Path::new(locator);
    require(
        !path.is_absolute()
            && path
                .components()
                .all(|part| matches!(part, Component::Normal(_))),
        format!("artifact locator is not canonical: {locator:?}"),
    )?;
    let candidate = root.join(path);
    let parent = canonical(candidate.parent().unwrap())?;
    require(
        parent.starts_with(canonical(root)?),
        format!("artifact locator escapes package root: {locator:?}"),
    )?;
    Ok(candidate)
}

fn hex_decode(value: &str) -> Result<Vec<u8>> {
    require(
        value.len().is_multiple_of(2) && value.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "raw checker output is not hex",
    )?;
    (0..value.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&value[index..index + 2], 16)
                .map_err(|error| EvidenceError(error.to_string()))
        })
        .collect()
}

fn remove_object_field(value: &mut Value, key: &str) -> Result<()> {
    match value {
        Value::Object(entries) => require(
            entries.remove(key).is_some(),
            format!("machine result lacks {key}"),
        ),
        _ => Err(EvidenceError("machine result is not an object".into())),
    }
}

fn validate_machine_result(
    machine: &Value,
    raw: &Value,
    module: &str,
    proof: &Value,
    preflight: &Value,
) -> Result<()> {
    require(
        machine.get("schema").and_then(Value::as_str)
            == Some("npa.independent-checker.machine_check_result.v1")
            && machine.get("module").and_then(Value::as_str) == Some(module)
            && machine.get("status").and_then(Value::as_str) == Some("checked"),
        format!("machine result mismatch for {module}"),
    )?;
    for field in ["certificate_hash", "export_hash", "axiom_report_hash"] {
        require(
            machine.get(field) == proof.get(field),
            format!("machine result {field} mismatch for {module}"),
        )?;
        require(
            raw.get(field) == proof.get(field),
            format!("raw checker {field} mismatch for {module}"),
        )?;
    }
    let checker = machine
        .get("checker")
        .ok_or_else(|| EvidenceError(format!("machine checker identity missing for {module}")))?;
    for (field, preflight_field, expected) in [
        ("profile", "", Some("external")),
        ("binary_id", "checker_binary_id", None),
        ("binary_hash", "checker_binary_sha256", None),
        ("id", "checker_id", None),
        ("version", "checker_version", None),
        ("build_hash", "checker_build_hash", None),
    ] {
        let wanted = expected.or_else(|| preflight.get(preflight_field).and_then(Value::as_str));
        require(
            checker.get(field).and_then(Value::as_str) == wanted,
            format!("machine checker identity mismatch for {module}"),
        )?;
    }
    let policy = machine
        .get("policy")
        .ok_or_else(|| EvidenceError(format!("machine policy identity missing for {module}")))?;
    require(
        policy.get("id").and_then(Value::as_str) == Some(POLICY_ID)
            && policy.get("version") == Some(&Value::Number("1".into()))
            && policy.get("hash") == preflight.get("runner_policy_sha256"),
        format!("machine policy identity mismatch for {module}"),
    )?;
    let runner = machine
        .get("runner")
        .ok_or_else(|| EvidenceError(format!("machine runner identity missing for {module}")))?;
    for (field, preflight_field) in [
        ("id", "runner_id"),
        ("version", "runner_version"),
        ("build_hash", "runner_build_hash"),
    ] {
        require(
            runner.get(field) == preflight.get(preflight_field),
            format!("machine runner identity mismatch for {module}"),
        )?;
    }
    let process = machine
        .get("process")
        .ok_or_else(|| EvidenceError(format!("machine process record missing for {module}")))?;
    require(
        process.get("launched") == Some(&Value::Bool(true))
            && process.get("exit_code") == Some(&Value::Number("0".into()))
            && matches!(process.get("termination_reason"), None | Some(Value::Null)),
        format!("checker process result mismatch for {module}"),
    )?;
    let usage = machine
        .get("resource_usage")
        .ok_or_else(|| EvidenceError(format!("resource usage missing for {module}")))?;
    let elapsed = usage.get("elapsed_ms").and_then(|value| match value {
        Value::Number(number) => number.parse::<u64>().ok(),
        _ => None,
    });
    require(
        usage.get("steps") == Some(&Value::Number("0".into()))
            && usage.get("memory_peak_mb") == Some(&Value::Number("0".into()))
            && elapsed.is_some(),
        format!("resource usage mismatch for {module}"),
    )?;
    require(
        raw.get("schema").and_then(Value::as_str)
            == Some("npa.independent-checker.checker_raw_result.v1")
            && raw.get("status").and_then(Value::as_str) == Some("checked")
            && raw.get("module").and_then(Value::as_str) == Some(module)
            && raw.get("checker_id") == preflight.get("checker_id")
            && raw.get("checker_version") == preflight.get("checker_version")
            && raw.get("checker_build_hash") == preflight.get("checker_build_hash"),
        format!("raw checker identity mismatch for {module}"),
    )
}

/// Copy and validate one verification run into its evidence directory.
pub fn capture_run(
    root: &Path,
    command_result: &Path,
    evidence_dir: &Path,
    fixture_record: &Path,
    preflight_path: &Path,
) -> Result<String> {
    let root = canonical(root)?;
    let command_bytes = read_bytes(command_result)?;
    let command = Value::parse_file(command_result)?;
    let fixture = Value::parse_file(fixture_record)?;
    let preflight = Value::parse_file(preflight_path)?;
    require(
        command.get("schema").and_then(Value::as_str) == Some("npa.package.command_result.v0.3"),
        "command result schema mismatch",
    )?;
    require(
        preflight.get("schema").and_then(Value::as_str)
            == Some("npa.checker_ext.toolchain_v0_7.policy_preflight.v1"),
        "policy preflight schema mismatch",
    )?;
    require(
        command.get("command").and_then(Value::as_str) == Some("package verify-certs")
            && command.get("root").and_then(Value::as_str) == Some("proofs")
            && command.get("status").and_then(Value::as_str) == Some("passed"),
        "command result contract mismatch",
    )?;
    require(
        command.get("timings").is_none(),
        "command timings must be off",
    )?;
    let modules = fixture
        .get("module_order")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("fixture module order mismatch".into()))?;
    let artifact_paths = fixture
        .get("artifact_paths")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("fixture artifacts invalid".into()))?;
    require(
        modules.len() == 2 && artifact_paths.len() == 2,
        "fixture artifacts invalid",
    )?;
    let diagnostics = command
        .get("diagnostics")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("diagnostics missing".into()))?;
    require(diagnostics.len() == 4, "diagnostic count mismatch")?;
    require(
        diagnostics[0].get("kind").and_then(Value::as_str) == Some("ExternalVerifier")
            && diagnostics[0].get("reason_code").and_then(Value::as_str)
                == Some("package_verified")
            && diagnostics[0].get("checker").and_then(Value::as_str)
                == Some("npa-checker-ext")
            && diagnostics[0].get("actual_value").and_then(Value::as_str)
                == Some("mode=external;verdict_source=npa-checker-ext;reference_checker_verdict=false;modules=2"),
        "aggregate diagnostic mismatch",
    )?;
    let artifacts = command
        .get("artifacts")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("artifact count mismatch".into()))?;
    require(artifacts.len() == 2, "artifact count mismatch")?;
    let lock_hash = sha256_bytes(&read_bytes(&root.join("generated/package-lock.json"))?);
    require(
        diagnostics[1].get("kind").and_then(Value::as_str) == Some("PackageLock")
            && diagnostics[1].get("reason_code").and_then(Value::as_str)
                == Some("package_lock_checked")
            && diagnostics[1].get("actual_value").and_then(Value::as_str)
                == Some(&format!("mode=checked;hash={lock_hash}")),
        "checked-lock provenance mismatch",
    )?;
    let mut seen_artifacts = BTreeSet::new();
    fs::create_dir_all(evidence_dir.join("machine-results"))
        .map_err(|error| EvidenceError(error.to_string()))?;
    fs::create_dir_all(evidence_dir.join("raw-results"))
        .map_err(|error| EvidenceError(error.to_string()))?;
    fs::write(evidence_dir.join("command-result.json"), &command_bytes)
        .map_err(|error| EvidenceError(error.to_string()))?;
    let mut records = Vec::new();
    for index in 0..2 {
        let module = modules[index]
            .as_str()
            .ok_or_else(|| EvidenceError("fixture module invalid".into()))?;
        let locator = artifacts[index]
            .get("path")
            .and_then(Value::as_str)
            .ok_or_else(|| EvidenceError("artifact locator is not a string".into()))?;
        require(
            Some(locator) == artifact_paths[index].as_str(),
            "artifact order or locator mismatch",
        )?;
        require(seen_artifacts.insert(locator), "duplicate artifact locator")?;
        require(
            diagnostics[index + 2].get("kind").and_then(Value::as_str) == Some("ExternalVerifier")
                && diagnostics[index + 2]
                    .get("reason_code")
                    .and_then(Value::as_str)
                    == Some("module_verified")
                && diagnostics[index + 2].get("module").and_then(Value::as_str) == Some(module)
                && diagnostics[index + 2]
                    .get("checker")
                    .and_then(Value::as_str)
                    == Some("npa-checker-ext")
                && diagnostics[index + 2]
                    .get("actual_value")
                    .and_then(Value::as_str)
                    == Some("checked"),
            format!("module diagnostic mismatch for {module}"),
        )?;
        let machine_path = safe_artifact_path(&root, locator)?;
        let machine_bytes = read_bytes(&machine_path)?;
        let machine = Value::parse_file(&machine_path)?;
        let raw_hex = machine
            .get("raw_checker_output_hex")
            .and_then(Value::as_str)
            .ok_or_else(|| {
                EvidenceError(format!("machine result raw output missing for {module}"))
            })?;
        let raw_bytes = hex_decode(raw_hex)?;
        let raw_source = std::str::from_utf8(&raw_bytes)
            .map_err(|_| EvidenceError(format!("raw checker output is invalid for {module}")))?;
        let raw_document = JsonDocument::parse(raw_source)
            .map_err(|_| EvidenceError(format!("raw checker output is invalid for {module}")))?;
        let raw = convert_json(raw_document.root(), "$", &machine_path)?;
        let proof = fixture
            .get("proof_identities")
            .and_then(|proofs| proofs.get(module))
            .ok_or_else(|| EvidenceError(format!("proof identity missing for {module}")))?;
        validate_machine_result(&machine, &raw, module, proof, &preflight)?;
        let name = format!("{index:02}-{module}.json");
        fs::write(
            evidence_dir.join("machine-results").join(&name),
            &machine_bytes,
        )
        .map_err(|error| EvidenceError(error.to_string()))?;
        fs::write(evidence_dir.join("raw-results").join(&name), &raw_bytes)
            .map_err(|error| EvidenceError(error.to_string()))?;
        records.push(Value::object([
            ("artifact_path", Value::string(locator)),
            (
                "machine_file",
                Value::string(format!("machine-results/{name}")),
            ),
            (
                "machine_sha256",
                Value::string(sha256_bytes(&machine_bytes)),
            ),
            ("module", Value::string(module)),
            ("raw_file", Value::string(format!("raw-results/{name}"))),
            ("raw_sha256", Value::string(sha256_bytes(&raw_bytes))),
        ]));
    }
    let record = Value::object([
        ("command_result_file", Value::string("command-result.json")),
        (
            "command_result_sha256",
            Value::string(sha256_bytes(&command_bytes)),
        ),
        ("modules", Value::Array(records)),
        ("package_lock_sha256", Value::string(lock_hash)),
        ("schema", Value::string(format!("{SCHEMA}.capture.v1"))),
    ]);
    write_json(&evidence_dir.join("capture.json"), &record)?;
    Ok(record.canonical())
}

/// Compare facade and direct-run evidence after removing only nondeterministic fields.
pub fn compare_runs(runs: &[PathBuf]) -> Result<String> {
    require(
        runs.len() == 3,
        "compare-runs requires facade, direct-1, and direct-final evidence",
    )?;
    let captures = runs
        .iter()
        .map(|run| Value::parse_file(&run.join("capture.json")))
        .collect::<Result<Vec<_>>>()?;
    let commands = runs
        .iter()
        .zip(&captures)
        .map(|(run, capture)| {
            read_bytes(
                &run.join(
                    capture
                        .get("command_result_file")
                        .and_then(Value::as_str)
                        .unwrap_or(""),
                ),
            )
        })
        .collect::<Result<Vec<_>>>()?;
    require(
        commands.windows(2).all(|pair| pair[0] == pair[1]),
        "command-result bytes differ between compatibility runs",
    )?;
    let modules = captures[0]
        .get("modules")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("capture modules missing".into()))?;
    let names = modules
        .iter()
        .map(|item| {
            item.get("module")
                .and_then(Value::as_str)
                .unwrap_or("")
                .to_owned()
        })
        .collect::<Vec<_>>();
    for (index, module) in names.iter().enumerate() {
        let mut raw = Vec::new();
        let mut normalized = Vec::new();
        for (run, capture) in runs.iter().zip(&captures) {
            let record = &capture
                .get("modules")
                .and_then(Value::as_array)
                .ok_or_else(|| EvidenceError("capture modules missing".into()))?[index];
            raw.push(read_bytes(&run.join(
                record.get("raw_file").and_then(Value::as_str).unwrap_or(""),
            ))?);
            let mut machine = Value::parse_file(
                &run.join(
                    record
                        .get("machine_file")
                        .and_then(Value::as_str)
                        .unwrap_or(""),
                ),
            )?;
            remove_object_field(&mut machine, "run_artifact_hash")?;
            let usage = machine.get_mut("resource_usage").ok_or_else(|| {
                EvidenceError("machine result lacks resource_usage.elapsed_ms".into())
            })?;
            remove_object_field(usage, "elapsed_ms")?;
            normalized.push(machine);
        }
        require(
            raw.windows(2).all(|pair| pair[0] == pair[1]),
            format!("raw checker bytes differ for {module}"),
        )?;
        require(
            normalized.windows(2).all(|pair| pair[0] == pair[1]),
            format!("normalized machine results differ for {module}"),
        )?;
    }
    Ok(Value::object([
        (
            "command_result_sha256",
            Value::string(sha256_bytes(&commands[0])),
        ),
        (
            "modules",
            Value::Array(names.into_iter().map(Value::string).collect()),
        ),
        (
            "normalization",
            Value::Array(vec![
                Value::string("resource_usage.elapsed_ms"),
                Value::string("run_artifact_hash"),
            ]),
        ),
        (
            "runs",
            Value::Array(
                runs.iter()
                    .map(|path| {
                        Value::string(
                            canonical(path)
                                .unwrap_or_else(|_| path.clone())
                                .to_string_lossy(),
                        )
                    })
                    .collect(),
            ),
        ),
        ("schema", Value::string(format!("{SCHEMA}.comparison.v1"))),
        ("status", Value::string("matched")),
    ])
    .canonical())
}

fn required_string<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| EvidenceError(format!("missing string field: {field}")))
}

fn required_value(value: &Value, field: &str) -> Result<Value> {
    value
        .get(field)
        .cloned()
        .ok_or_else(|| EvidenceError(format!("missing field: {field}")))
}

fn resolve_core_identity(core_root: &Path, require_clean: bool) -> Result<Value> {
    let core_root = canonical(core_root)?;
    let top = canonical(Path::new(&run_git(
        &core_root,
        &["rev-parse", "--show-toplevel"],
        &[],
    )?))?;
    let dirty = run_git(
        &top,
        &["status", "--porcelain=v1", "--untracked-files=all"],
        &[],
    )?;
    require(
        !require_clean || dirty.is_empty(),
        "full release identity requires a clean candidate checkout",
    )?;
    let checkout = run_git(&top, &["rev-parse", "HEAD"], &[])?;
    require(
        checkout.len() == 40 && checkout.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "core checkout revision is not 40 lower hex",
    )?;
    let (kind, tree) = if core_root == top {
        (
            "standalone",
            run_git(&core_root, &["rev-parse", "HEAD^{tree}"], &[])?,
        )
    } else {
        require(
            core_root.strip_prefix(&top).ok() == Some(Path::new("npa-core")),
            "aggregate core root must be the npa-core subtree",
        )?;
        (
            "aggregate",
            run_git(&top, &["rev-parse", "HEAD:npa-core"], &[])?,
        )
    };
    Ok(Value::object([
        (
            "candidate_clean",
            Value::string(dirty.is_empty().to_string()),
        ),
        ("npa_core_checkout_revision", Value::string(checkout)),
        ("npa_core_git_root", Value::string(top.to_string_lossy())),
        ("npa_core_source_kind", Value::string(kind)),
        ("npa_core_tree_hash", Value::string(tree)),
    ]))
}

fn rust_identity() -> Result<(String, String)> {
    let output = Command::new("rustc")
        .arg("-vV")
        .output()
        .map_err(|error| EvidenceError(error.to_string()))?;
    require(
        output.status.success(),
        format!(
            "rustc -vV failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ),
    )?;
    let text = String::from_utf8(output.stdout)
        .map_err(|_| EvidenceError("rustc -vV output is not UTF-8".into()))?;
    let mut lines = text.lines();
    let toolchain = lines
        .next()
        .filter(|line| line.starts_with("rustc "))
        .ok_or_else(|| EvidenceError("rustc -vV lacks its toolchain identity line".into()))?
        .to_owned();
    let hosts = text
        .lines()
        .filter_map(|line| line.strip_prefix("host: "))
        .collect::<Vec<_>>();
    require(
        hosts.len() == 1 && !hosts[0].is_empty(),
        "rustc -vV lacks one host triple",
    )?;
    Ok((toolchain, hosts[0].to_owned()))
}

/// Collect the Git, Cargo, Rust, host, and checker identities bound into a release.
pub fn collect_build(
    core_root: &Path,
    source_root: &Path,
    fixture_record: &Path,
    metadata_path: &Path,
    preflight_path: &Path,
    checker_path: &Path,
    require_clean: bool,
) -> Result<String> {
    let core_root = canonical(core_root)?;
    let source_root = canonical(source_root)?;
    let fixture = Value::parse_file(fixture_record)?;
    let metadata = Value::parse_file(metadata_path)?;
    let preflight = Value::parse_file(preflight_path)?;
    require(
        preflight.get("schema").and_then(Value::as_str)
            == Some("npa.checker_ext.toolchain_v0_7.policy_preflight.v1"),
        "policy preflight schema mismatch",
    )?;
    let source_commit = run_git(&source_root, &["rev-parse", "HEAD"], &[])?;
    require(
        fixture.get("source_commit").and_then(Value::as_str) == Some(&source_commit),
        "temporary source HEAD changed after fixture preparation",
    )?;
    require(
        run_git(
            &source_root,
            &["status", "--porcelain=v1", "--untracked-files=all"],
            &[],
        )?
        .is_empty(),
        "temporary source repository is not clean",
    )?;
    require(
        canonical(&source_root.join("npa-core/Cargo.toml"))?
            == canonical(&core_root.join("Cargo.toml"))?,
        "temporary source npa-core link does not select the real core root",
    )?;
    check_metadata(metadata_path)?;
    let packages = metadata
        .get("packages")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("Cargo metadata packages are invalid".into()))?;
    let versions = packages
        .iter()
        .filter_map(|package| {
            Some((
                package.get("name")?.as_str()?.to_owned(),
                package.get("version")?.as_str()?.to_owned(),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let target_directory = required_string(&metadata, "target_directory")?;
    let host_path = canonical(&Path::new(target_directory).join("debug/npa"))?;
    let checker_path = canonical(checker_path)?;
    let checker_hash = sha256_bytes(&read_bytes(&checker_path)?);
    require(
        preflight
            .get("checker_binary_sha256")
            .and_then(Value::as_str)
            == Some(&checker_hash),
        "real and copied checker executable bytes differ",
    )?;
    let package_root = source_root.join("proofs");
    let paths = BTreeMap::from([
        ("axiom_policy", package_root.join(AXIOM_POLICY_PATH)),
        ("checker_binary", package_root.join(CHECKER_PATH)),
        ("checker_registry", package_root.join(REGISTRY_PATH)),
        ("identity_manifest", package_root.join(IDENTITY_PATH)),
        ("runner_policy_file", package_root.join(POLICY_PATH)),
        ("cargo_lock", core_root.join("Cargo.lock")),
        ("host_executable", host_path.clone()),
        ("real_checker", checker_path.clone()),
    ]);
    let hashes = paths
        .iter()
        .map(|(name, path)| {
            Ok((
                (*name).to_owned(),
                Value::string(sha256_bytes(&read_bytes(path)?)),
            ))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    for (name, field) in [
        ("axiom_policy", "axiom_policy_sha256"),
        ("checker_binary", "checker_binary_sha256"),
        ("checker_registry", "checker_registry_sha256"),
        ("identity_manifest", "identity_manifest_sha256"),
        ("runner_policy_file", "runner_policy_file_sha256"),
    ] {
        require(
            hashes.get(name).and_then(Value::as_str)
                == preflight.get(field).and_then(Value::as_str),
            format!("preflight {name} bytes changed"),
        )?;
    }
    let core = resolve_core_identity(&core_root, require_clean)?;
    let mut result = core.as_object().unwrap().clone();
    let (toolchain, target) = rust_identity()?;
    result.extend(BTreeMap::from([
        (
            "cargo_lock_path".into(),
            Value::string("npa-core/Cargo.lock"),
        ),
        ("cargo_lock_sha256".into(), hashes["cargo_lock"].clone()),
        (
            "cargo_manifest_path".into(),
            Value::string("npa-core/Cargo.toml"),
        ),
        ("cargo_profile".into(), Value::string("dev")),
        (
            "cargo_target_directory".into(),
            Value::string(canonical(Path::new(target_directory))?.to_string_lossy()),
        ),
        (
            "checker_executable_path".into(),
            Value::string(checker_path.to_string_lossy()),
        ),
        ("host_executable_name".into(), Value::string("npa")),
        (
            "host_executable_path".into(),
            Value::string(host_path.to_string_lossy()),
        ),
        (
            "host_executable_sha256".into(),
            hashes["host_executable"].clone(),
        ),
        (
            "npa_cli_crate_version".into(),
            Value::string(&versions["npa-cli"]),
        ),
        (
            "npa_core_ref".into(),
            core.get("npa_core_checkout_revision").unwrap().clone(),
        ),
        ("protected_build_inputs".into(), Value::Object(hashes)),
        ("rust_target".into(), Value::string(target)),
        ("rust_toolchain".into(), Value::string(toolchain)),
        (
            "schema".into(),
            Value::string(format!("{SCHEMA}.build_identity.v1")),
        ),
        ("source_commit".into(), Value::string(source_commit)),
    ]));
    Ok(Value::Object(result).canonical())
}

fn quoted_trace_strings(line: &str) -> Result<Vec<String>> {
    let bytes = line.as_bytes();
    let mut values = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'"' {
            index += 1;
            continue;
        }
        index += 1;
        let mut value = String::new();
        while index < bytes.len() && bytes[index] != b'"' {
            if bytes[index] == b'\\' && index + 1 < bytes.len() {
                index += 1;
                value.push(match bytes[index] {
                    b'n' => '\n',
                    b'r' => '\r',
                    b't' => '\t',
                    other => char::from(other),
                });
            } else {
                value.push(char::from(bytes[index]));
            }
            index += 1;
        }
        require(
            index < bytes.len(),
            "undecodable quoted string in trace record",
        )?;
        index += 1;
        values.push(value);
    }
    Ok(values)
}

fn joined_trace_lines(path: &Path, text: &str) -> Result<Vec<String>> {
    let mut output = Vec::new();
    let mut pending: Option<(String, String)> = None;
    for (index, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(prefix) = line.strip_suffix("<unfinished ...>") {
            require(
                pending.is_none(),
                format!(
                    "nested unfinished syscall in {}:{}",
                    path.display(),
                    index + 1
                ),
            )?;
            let name = prefix
                .split_once('(')
                .map(|pair| pair.0)
                .filter(|name| !name.is_empty())
                .ok_or_else(|| {
                    EvidenceError(format!(
                        "undecodable unfinished syscall in {}:{}",
                        path.display(),
                        index + 1
                    ))
                })?;
            pending = Some((name.to_owned(), prefix.to_owned()));
            continue;
        }
        if let Some(resumed) = line.strip_prefix("<... ") {
            let (name, suffix) = resumed.split_once(" resumed>").ok_or_else(|| {
                EvidenceError(format!(
                    "undecodable resumed syscall in {}:{}",
                    path.display(),
                    index + 1
                ))
            })?;
            let (pending_name, prefix) = pending.take().ok_or_else(|| {
                EvidenceError(format!(
                    "unmatched resumed syscall in {}:{}",
                    path.display(),
                    index + 1
                ))
            })?;
            require(
                pending_name == name,
                format!(
                    "unmatched resumed syscall in {}:{}",
                    path.display(),
                    index + 1
                ),
            )?;
            output.push(format!("{prefix}{suffix}"));
            continue;
        }
        require(
            pending.is_none(),
            format!(
                "unfinished syscall not resumed in {}:{}",
                path.display(),
                index + 1
            ),
        )?;
        output.push(line.to_owned());
    }
    require(
        pending.is_none(),
        format!("unfinished syscall at end of {}", path.display()),
    )?;
    Ok(output)
}

fn lexical_path(path: &Path) -> PathBuf {
    let mut output = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                output.pop();
            }
            other => output.push(other.as_os_str()),
        }
    }
    output
}

fn trace_path(line: &str, value: &str, default_root: &Path) -> Result<PathBuf> {
    if value.ends_with("...") {
        return Err(EvidenceError("truncated path in trace record".into()));
    }
    let value_path = Path::new(value);
    if value_path.is_absolute() {
        return Ok(lexical_path(value_path));
    }
    let quoted = format!("\"{value}");
    let prefix = line.split_once(&quoted).map_or(line, |parts| parts.0);
    let descriptor_root = prefix.rfind('<').and_then(|start| {
        prefix[start + 1..]
            .find('>')
            .map(|length| &prefix[start + 1..start + 1 + length])
            .filter(|target| target.starts_with('/'))
    });
    Ok(lexical_path(
        &descriptor_root
            .map(PathBuf::from)
            .unwrap_or_else(|| default_root.to_path_buf())
            .join(value_path),
    ))
}

fn descriptor_target(line: &str) -> Option<&str> {
    let start = line.find('<')?;
    let end = line[start + 1..].find('>')? + start + 1;
    Some(&line[start + 1..end])
}

fn versioned_shared_object(name: &str, stem: &str) -> bool {
    name.strip_prefix(stem).is_some_and(|suffix| {
        suffix.is_empty()
            || suffix.strip_prefix('.').is_some_and(|versions| {
                !versions.is_empty()
                    && versions.split('.').all(|version| {
                        !version.is_empty() && version.bytes().all(|b| b.is_ascii_digit())
                    })
            })
    })
}

fn checker_runtime_path_allowed(path: &Path) -> bool {
    let text = path.to_string_lossy();
    if text == "/etc/ld.so.cache"
        || text == "/etc/ld.so.preload"
        || text == "/usr/lib/ocaml/ld.conf"
    {
        return true;
    }
    if let Some(descriptor) = text.strip_prefix("/proc/self/fd/") {
        return !descriptor.is_empty() && descriptor.bytes().all(|byte| byte.is_ascii_digit());
    }
    let Some(relative) = ["/lib/", "/lib64/", "/usr/lib/"]
        .into_iter()
        .find_map(|prefix| text.strip_prefix(prefix))
    else {
        return false;
    };
    let Some(name) = Path::new(relative)
        .file_name()
        .and_then(|name| name.to_str())
    else {
        return false;
    };
    versioned_shared_object(name, "libc.so")
        || versioned_shared_object(name, "libm.so")
        || name.split_once(".so").is_some_and(|(stem, suffix)| {
            stem.starts_with("ld-linux")
                && (suffix.is_empty()
                    || suffix.strip_prefix('.').is_some_and(|versions| {
                        !versions.is_empty()
                            && versions.split('.').all(|version| {
                                !version.is_empty()
                                    && version.bytes().all(|byte| byte.is_ascii_digit())
                            })
                    }))
        })
}

/// Audit Linux per-PID strace logs for source-free and mutation boundaries.
pub fn check_trace(
    trace_prefix: &Path,
    source_root: &Path,
    package_root: &Path,
    fixture_record: &Path,
) -> Result<String> {
    let source_root = canonical(source_root)?;
    let package_root = canonical(package_root)?;
    let fixture = Value::parse_file(fixture_record)?;
    let prefix_name = trace_prefix
        .file_name()
        .ok_or_else(|| EvidenceError("trace prefix has no name".into()))?
        .to_string_lossy();
    let parent = trace_prefix.parent().unwrap_or(Path::new("."));
    let mut trace_files = fs::read_dir(parent)
        .map_err(|error| EvidenceError(error.to_string()))?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            entry
                .file_name()
                .to_string_lossy()
                .strip_prefix(&format!("{prefix_name}."))
                .is_some_and(|suffix| suffix.bytes().all(|byte| byte.is_ascii_digit()))
        })
        .map(|entry| entry.path())
        .collect::<Vec<_>>();
    trace_files.sort();
    require(
        !trace_files.is_empty(),
        format!("no per-PID trace logs found for {}", trace_prefix.display()),
    )?;
    let sentinels = fixture
        .get("sentinel_paths")
        .and_then(Value::as_array)
        .unwrap_or(&[])
        .iter()
        .filter_map(Value::as_str)
        .map(|path| package_root.join(path))
        .collect::<BTreeSet<_>>();
    let expected_checkers = fixture
        .get("module_order")
        .and_then(Value::as_array)
        .map_or(0, <[Value]>::len);
    let mut calls = BTreeMap::<u64, Vec<String>>::new();
    let mut checker_argv = BTreeMap::<u64, BTreeMap<String, PathBuf>>::new();
    let mut parent_of = BTreeMap::<u64, u64>::new();
    for path in &trace_files {
        let text = fs::read_to_string(path).map_err(|error| {
            EvidenceError(format!("cannot read trace log {}: {error}", path.display()))
        })?;
        let lines = joined_trace_lines(path, &text)?;
        let pid = path
            .extension()
            .and_then(|value| value.to_str())
            .and_then(|value| value.parse::<u64>().ok())
            .ok_or_else(|| {
                EvidenceError(format!("trace file lacks numeric PID: {}", path.display()))
            })?;
        for line in &lines {
            let syscall = line.split_once('(').map(|parts| parts.0).unwrap_or("");
            if ["clone", "clone3", "fork", "vfork"].contains(&syscall) {
                if let Some(result) = line.split_once(") = ").map(|parts| parts.1) {
                    if let Some(child) = result
                        .split_whitespace()
                        .next()
                        .and_then(|value| value.parse::<u64>().ok())
                    {
                        parent_of.insert(child, pid);
                    }
                }
            }
            if ["execve", "execveat"].contains(&syscall)
                && (line.starts_with("execve(\"/proc/self/fd/")
                    || line.starts_with("execveat(\"/proc/self/fd/"))
                && line
                    .split_once(") = ")
                    .is_some_and(|parts| parts.1.starts_with('0'))
            {
                let values = quoted_trace_strings(line)?;
                let mut observed = BTreeMap::new();
                for flag in ["--cert", "--import-dir", "--policy"] {
                    let matches = values
                        .iter()
                        .enumerate()
                        .filter(|(_, value)| value.as_str() == flag)
                        .collect::<Vec<_>>();
                    require(
                        matches.len() == 1,
                        format!("checker exec in PID {pid} has invalid {flag}"),
                    )?;
                    let value = values.get(matches[0].0 + 1).ok_or_else(|| {
                        EvidenceError(format!("checker exec in PID {pid} lacks {flag} value"))
                    })?;
                    observed.insert(flag.to_owned(), lexical_path(&package_root.join(value)));
                }
                checker_argv.insert(pid, observed);
            }
        }
        calls.insert(pid, lines);
    }
    require(
        checker_argv.len() == expected_checkers,
        format!(
            "checker PID count mismatch: expected {expected_checkers}, got {}",
            checker_argv.len()
        ),
    )?;
    for pid in calls.keys() {
        let mut ancestor = parent_of.get(pid).copied();
        while let Some(parent_pid) = ancestor {
            require(
                !checker_argv.contains_key(&parent_pid) || checker_argv.contains_key(pid),
                format!("unexpected checker descendant PID {pid}"),
            )?;
            ancestor = parent_of.get(&parent_pid).copied();
        }
    }

    let proof_files = fixture
        .get("proof_identities")
        .and_then(Value::as_object)
        .into_iter()
        .flat_map(|proofs| proofs.values())
        .filter_map(|proof| proof.get("certificate").and_then(Value::as_str))
        .map(|path| package_root.join(path))
        .collect::<BTreeSet<_>>();
    let mut host_allowed = proof_files;
    for path in [
        "npa-package.toml",
        "generated/package-lock.json",
        POLICY_PATH,
        REGISTRY_PATH,
        AXIOM_POLICY_PATH,
        CHECKER_PATH,
    ] {
        host_allowed.insert(package_root.join(path));
    }
    let mutable_roots = MUTABLE_PREFIXES
        .iter()
        .map(|prefix| package_root.join(prefix.trim_end_matches('/')))
        .collect::<Vec<_>>();
    let mut required_reads = BTreeMap::<u64, BTreeSet<PathBuf>>::new();
    let mut checker_reads = 0_u64;
    let mut import_reads = 0_u64;
    let mut mutations = 0_u64;
    let mut host_accesses = 0_u64;
    for (pid, lines) in &calls {
        let checker = checker_argv.get(pid);
        let mut cwd = if checker.is_some() {
            package_root.clone()
        } else {
            source_root.clone()
        };
        for line in lines.iter().map(String::as_str) {
            if line.starts_with("--- SIG") || line.starts_with("+++") {
                continue;
            }
            let syscall = line.split_once('(').map(|pair| pair.0).ok_or_else(|| {
                EvidenceError(format!("undecodable trace record for PID {pid}: {line}"))
            })?;
            if [
                "socket",
                "socketpair",
                "connect",
                "bind",
                "listen",
                "accept",
                "accept4",
                "send",
                "sendto",
                "recv",
                "recvfrom",
                "sendmsg",
                "recvmsg",
            ]
            .contains(&syscall)
                && !(checker.is_none() && (line.contains("AF_UNIX") || line.contains("<UNIX")))
            {
                return Err(EvidenceError(format!(
                    "forbidden network syscall by PID {pid}: {syscall}"
                )));
            }
            let quoted = quoted_trace_strings(line)?;
            if syscall == "chdir" && !line.contains(" = -1") {
                if let Some(value) = quoted.first() {
                    cwd = trace_path(line, value, &cwd)?;
                }
                continue;
            }
            let mutating = [
                "creat",
                "mkdir",
                "mkdirat",
                "rename",
                "renameat",
                "renameat2",
                "unlink",
                "unlinkat",
                "truncate",
                "symlink",
                "symlinkat",
                "link",
                "linkat",
                "chmod",
                "fchmodat",
                "utimensat",
            ]
            .contains(&syscall)
                || (["open", "openat", "openat2"].contains(&syscall)
                    && [
                        "O_WRONLY",
                        "O_RDWR",
                        "O_CREAT",
                        "O_TRUNC",
                        "O_APPEND",
                        "O_TMPFILE",
                    ]
                    .iter()
                    .any(|flag| line.contains(flag)));

            if [
                "write",
                "writev",
                "pwrite64",
                "pwritev",
                "pwritev2",
                "ftruncate",
            ]
            .contains(&syscall)
            {
                let target = descriptor_target(line).ok_or_else(|| {
                    EvidenceError(format!("unknown write FD in {syscall} by PID {pid}"))
                })?;
                if target.starts_with('/') {
                    let path = lexical_path(Path::new(target));
                    if path.starts_with(&package_root) {
                        require(
                            mutable_roots.iter().any(|root| path.starts_with(root)),
                            format!("forbidden package write by PID {pid}: {}", path.display()),
                        )?;
                        mutations += 1;
                    } else if checker.is_some() {
                        return Err(EvidenceError(format!(
                            "checker wrote non-package file: {}",
                            path.display()
                        )));
                    } else {
                        host_accesses += 1;
                    }
                } else if checker.is_some() && !target.starts_with("pipe:") {
                    return Err(EvidenceError(format!(
                        "checker wrote forbidden descriptor target: {target}"
                    )));
                } else if checker.is_none()
                    && !(target.starts_with("pipe:")
                        || target.starts_with("memfd:npa-checker-ext")
                        || target.starts_with("UNIX")
                        || target.starts_with("anon_inode:")
                        || target == "/dev/null")
                {
                    return Err(EvidenceError(format!(
                        "host wrote unknown descriptor target: {target}"
                    )));
                }
                continue;
            }
            if ["execve", "execveat", "getcwd"].contains(&syscall) {
                continue;
            }
            for value in quoted {
                let candidate = trace_path(line, &value, &cwd)?;
                if candidate.starts_with(&package_root) {
                    require(
                        !sentinels.iter().any(|sentinel| {
                            candidate == *sentinel || candidate.starts_with(sentinel)
                        }),
                        format!(
                            "forbidden package probe by PID {pid}: {}",
                            candidate.display()
                        ),
                    )?;
                    if mutating {
                        require(
                            mutable_roots.iter().any(|root| {
                                candidate.starts_with(root) || root.starts_with(&candidate)
                            }),
                            format!(
                                "forbidden package mutation by PID {pid}: {}",
                                candidate.display()
                            ),
                        )?;
                        mutations += 1;
                    }
                    let allowed = if let Some(argv) = checker {
                        let cert = &argv["--cert"];
                        let policy = &argv["--policy"];
                        let imports = &argv["--import-dir"];
                        candidate == *cert
                            || candidate == *policy
                            || candidate == *imports
                            || (candidate.starts_with(imports)
                                && (candidate.is_dir()
                                    || candidate
                                        .file_name()
                                        .is_some_and(|name| name == "certificate.npcert")))
                            || cert.starts_with(&candidate)
                            || policy.starts_with(&candidate)
                            || imports.starts_with(&candidate)
                    } else {
                        host_allowed
                            .iter()
                            .any(|target| candidate == *target || target.starts_with(&candidate))
                            || mutable_roots.iter().any(|root| {
                                candidate.starts_with(root) || root.starts_with(&candidate)
                            })
                    };
                    require(
                        allowed,
                        format!(
                            "forbidden package probe by {} PID {pid}: {}",
                            if checker.is_some() { "checker" } else { "host" },
                            candidate.display()
                        ),
                    )?;
                    if checker.is_some()
                        && ["open", "openat", "openat2"].contains(&syscall)
                        && !line.contains(" = -1")
                        && !mutating
                        && !line.contains("O_PATH")
                    {
                        checker_reads += 1;
                        required_reads
                            .entry(*pid)
                            .or_default()
                            .insert(candidate.clone());
                        if let Some(argv) = checker {
                            if candidate
                                .file_name()
                                .is_some_and(|name| name == "certificate.npcert")
                                && candidate.starts_with(&argv["--import-dir"])
                            {
                                import_reads += 1;
                            }
                        }
                    }
                } else if checker.is_some()
                    && candidate.is_absolute()
                    && !checker_runtime_path_allowed(&candidate)
                {
                    return Err(EvidenceError(format!(
                        "checker runtime path is not allowlisted: {}",
                        candidate.display()
                    )));
                } else if checker.is_none() {
                    host_accesses += 1;
                }
            }
        }
    }
    for (pid, argv) in &checker_argv {
        let reads = required_reads.get(pid).cloned().unwrap_or_default();
        require(
            reads.contains(&argv["--cert"]) && reads.contains(&argv["--policy"]),
            format!("checker PID {pid} did not read its certificate and policy"),
        )?;
    }
    require(
        import_reads > 0,
        "checker trace did not read a required import certificate",
    )?;
    Ok(Value::object([
        (
            "checker_pids",
            Value::Array(
                checker_argv
                    .keys()
                    .map(|pid| Value::Number(pid.to_string()))
                    .collect(),
            ),
        ),
        (
            "checker_read_count",
            Value::Number(checker_reads.to_string()),
        ),
        (
            "host_orchestration_access_count",
            Value::Number(host_accesses.to_string()),
        ),
        ("import_read_count", Value::Number(import_reads.to_string())),
        (
            "permitted_mutation_count",
            Value::Number(mutations.to_string()),
        ),
        ("schema", Value::string(format!("{SCHEMA}.trace_audit.v1"))),
        ("status", Value::string("passed")),
        (
            "trace_prefix",
            Value::string(
                canonical(parent)?
                    .join(prefix_name.as_ref())
                    .to_string_lossy(),
            ),
        ),
    ])
    .canonical())
}

fn direct_command(policy_hash: &str) -> String {
    [
        "cargo",
        "run",
        "--locked",
        "--offline",
        "-q",
        "--manifest-path",
        "npa-core/Cargo.toml",
        "-p",
        "npa-cli",
        "--",
        "package",
        "verify-certs",
        "--root",
        "proofs",
        "--package-lock",
        "checked",
        "--checker",
        "external",
        "--audit-cache",
        "off",
        "--verifier-memo",
        "off",
        "--jobs",
        "1",
        "--runner-policy",
        POLICY_PATH,
        "--runner-policy-hash",
        policy_hash,
        "--checker-registry",
        REGISTRY_PATH,
        "--json",
    ]
    .join(" ")
}

fn write_octal(field: &mut [u8], value: u64) -> Result<()> {
    let digits = field.len() - 1;
    let encoded = format!("{value:0digits$o}\0");
    require(encoded.len() == field.len(), "tar numeric field overflow")?;
    field.copy_from_slice(encoded.as_bytes());
    Ok(())
}

fn tar_header(name: &str, mode: u32, size: u64, kind: u8) -> Result<[u8; 512]> {
    let mut header = [0_u8; 512];
    let name_bytes = name.as_bytes();
    header[..name_bytes.len().min(100)].copy_from_slice(&name_bytes[..name_bytes.len().min(100)]);
    write_octal(&mut header[100..108], u64::from(mode & 0o7777))?;
    write_octal(&mut header[108..116], 0)?;
    write_octal(&mut header[116..124], 0)?;
    write_octal(&mut header[124..136], size)?;
    write_octal(&mut header[136..148], 0)?;
    header[148..156].fill(b' ');
    header[156] = kind;
    header[257..265].copy_from_slice(b"ustar  \0");
    let checksum = header.iter().map(|byte| u64::from(*byte)).sum::<u64>();
    let encoded = format!("{checksum:06o}\0");
    require(encoded.len() == 7, "tar checksum overflow")?;
    header[148..155].copy_from_slice(encoded.as_bytes());
    Ok(header)
}

fn append_tar_payload(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(bytes);
    let remainder = bytes.len() % 512;
    if remainder != 0 {
        output.resize(output.len() + 512 - remainder, 0);
    }
}

fn append_tar_entry(
    output: &mut Vec<u8>,
    name: &str,
    mode: u32,
    kind: u8,
    bytes: &[u8],
) -> Result<()> {
    if name.len() > 100 {
        let mut long_name = name.as_bytes().to_vec();
        long_name.push(0);
        output.extend_from_slice(&tar_header(
            "././@LongLink",
            0,
            long_name.len() as u64,
            b'L',
        )?);
        append_tar_payload(output, &long_name);
    }
    output.extend_from_slice(&tar_header(name, mode, bytes.len() as u64, kind)?);
    append_tar_payload(output, bytes);
    Ok(())
}

fn collect_archive_paths(directory: &Path, output: &mut Vec<PathBuf>) -> Result<()> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| EvidenceError(format!("cannot read archive input: {error}")))?
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|error| EvidenceError(format!("cannot read archive input: {error}")))?;
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| EvidenceError(format!("cannot inspect archive input: {error}")))?;
        require(
            metadata.is_dir() || metadata.is_file(),
            format!(
                "archive input has unsupported file type: {}",
                path.display()
            ),
        )?;
        output.push(path.clone());
        if metadata.is_dir() {
            collect_archive_paths(&path, output)?;
        }
    }
    Ok(())
}

fn write_deterministic_generated_archive(generated: &Path, archive: &Path) -> Result<()> {
    require(generated.is_dir(), "final generated tree is missing")?;
    let mut paths = vec![generated.to_path_buf()];
    collect_archive_paths(generated, &mut paths)?;
    let mut tar_bytes = Vec::new();
    for path in paths {
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| EvidenceError(format!("cannot inspect archive input: {error}")))?;
        let relative = path.strip_prefix(generated).unwrap();
        let mut name = Path::new("proofs/generated")
            .join(relative)
            .to_string_lossy()
            .replace('\\', "/");
        if metadata.is_dir() {
            if !name.ends_with('/') {
                name.push('/');
            }
            append_tar_entry(&mut tar_bytes, &name, 0o755, b'5', &[])?;
        } else {
            append_tar_entry(&mut tar_bytes, &name, 0o644, b'0', &read_bytes(&path)?)?;
        }
    }
    tar_bytes.resize(tar_bytes.len() + 1024, 0);
    let remainder = tar_bytes.len() % 10_240;
    if remainder != 0 {
        tar_bytes.resize(tar_bytes.len() + 10_240 - remainder, 0);
    }
    let tar_path = archive.with_extension("tar.tmp");
    fs::write(&tar_path, tar_bytes).map_err(|error| EvidenceError(error.to_string()))?;
    let compressed = Command::new("gzip")
        .args(["-9n", "-c"])
        .arg(&tar_path)
        .output()
        .map_err(|error| EvidenceError(format!("cannot execute gzip: {error}")))?;
    let _ = fs::remove_file(&tar_path);
    require(
        compressed.status.success(),
        format!(
            "gzip failed: {}",
            String::from_utf8_lossy(&compressed.stderr).trim()
        ),
    )?;
    let mut gzip_bytes = compressed.stdout;
    require(
        gzip_bytes.len() >= 10 && gzip_bytes[..3] == [0x1f, 0x8b, 0x08],
        "gzip output has an invalid header",
    )?;
    gzip_bytes[8] = 2;
    gzip_bytes[9] = 255;
    fs::write(archive, gzip_bytes).map_err(|error| EvidenceError(error.to_string()))
}

fn rehash_build_inputs(source_root: &Path, core_root: &Path, build: &Value) -> Result<()> {
    let package_root = source_root.join("proofs");
    let expected = build
        .get("protected_build_inputs")
        .and_then(Value::as_object)
        .ok_or_else(|| EvidenceError("build identity lacks protected input hashes".into()))?;
    let paths = BTreeMap::from([
        ("axiom_policy", package_root.join(AXIOM_POLICY_PATH)),
        ("checker_binary", package_root.join(CHECKER_PATH)),
        ("checker_registry", package_root.join(REGISTRY_PATH)),
        ("identity_manifest", package_root.join(IDENTITY_PATH)),
        ("runner_policy_file", package_root.join(POLICY_PATH)),
        ("cargo_lock", core_root.join("Cargo.lock")),
        (
            "host_executable",
            PathBuf::from(required_string(build, "host_executable_path")?),
        ),
        (
            "real_checker",
            PathBuf::from(required_string(build, "checker_executable_path")?),
        ),
    ]);
    for (name, path) in paths {
        require(
            expected.get(name).and_then(Value::as_str) == Some(&sha256_bytes(&read_bytes(&path)?)),
            format!("protected build input changed: {name}"),
        )?;
    }
    require(
        run_git(source_root, &["rev-parse", "HEAD"], &[])?
            == required_string(build, "source_commit")?,
        "temporary source HEAD changed",
    )?;
    require(
        run_git(
            source_root,
            &["status", "--porcelain=v1", "--untracked-files=all"],
            &[],
        )?
        .is_empty(),
        "temporary source repository became dirty",
    )?;
    let core_now = resolve_core_identity(core_root, true)?;
    for field in [
        "npa_core_source_kind",
        "npa_core_checkout_revision",
        "npa_core_tree_hash",
    ] {
        require(
            core_now.get(field) == build.get(field),
            format!("core identity changed: {field}"),
        )?;
    }
    Ok(())
}

/// Build deterministic generated artifacts, checksum, and the v0.2 release manifest.
#[allow(clippy::too_many_arguments)]
pub fn build_release(
    source_root: &Path,
    core_root: &Path,
    package_root: &Path,
    assets_root: &Path,
    fixture_record: &Path,
    preflight_path: &Path,
    build_record: &Path,
    final_evidence: &Path,
    generated_at_utc: &str,
) -> Result<String> {
    let source_root = canonical(source_root)?;
    let core_root = canonical(core_root)?;
    let package_root = canonical(package_root)?;
    require(
        package_root == source_root.join("proofs"),
        "release package root must be literal proofs",
    )?;
    require(
        generated_at_utc.len() == 20
            && generated_at_utc.ends_with('Z')
            && generated_at_utc.as_bytes()[4] == b'-'
            && generated_at_utc.as_bytes()[10] == b'T',
        "generated timestamp must use YYYY-MM-DDTHH:MM:SSZ",
    )?;
    let _fixture = Value::parse_file(fixture_record)?;
    let preflight = Value::parse_file(preflight_path)?;
    let build = Value::parse_file(build_record)?;
    let capture = Value::parse_file(&final_evidence.join("capture.json"))?;
    rehash_build_inputs(&source_root, &core_root, &build)?;
    let generated = package_root.join("generated");
    let mut top_json = fs::read_dir(&generated)
        .map_err(|error| EvidenceError(error.to_string()))?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            entry.path().is_file() && entry.path().extension().is_some_and(|ext| ext == "json")
        })
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    top_json.sort();
    require(
        top_json == RETAINED_JSON,
        format!("retained top-level JSON mismatch: got {top_json:?}"),
    )?;
    let command_file = final_evidence.join(required_string(&capture, "command_result_file")?);
    let command_bytes = read_bytes(&command_file)?;
    require(
        sha256_bytes(&command_bytes) == required_string(&capture, "command_result_sha256")?,
        "final command result differs from its capture",
    )?;
    let command_result = Value::parse_file(&command_file)?;
    require(
        command_result.get("schema").and_then(Value::as_str)
            == Some("npa.package.command_result.v0.3"),
        "command result schema mismatch",
    )?;
    fs::create_dir_all(assets_root).map_err(|error| EvidenceError(error.to_string()))?;
    require(
        fs::read_dir(assets_root)
            .map_err(|error| EvidenceError(error.to_string()))?
            .next()
            .is_none(),
        format!(
            "release assets directory is not empty: {}",
            assets_root.display()
        ),
    )?;
    let archive_name = "npa-mathlib-downstream-proofs-generated-toolchain-v0.7.0-compat.tar.gz";
    let checksum_name = "npa-mathlib-downstream-proofs-generated-toolchain-v0.7.0-compat.sha256";
    let manifest_name =
        "npa-mathlib-downstream-proofs-generated-toolchain-v0.7.0-compat-manifest.json";
    let archive = assets_root.join(archive_name);
    write_deterministic_generated_archive(&generated, &archive)?;
    let generated_files = RETAINED_JSON
        .into_iter()
        .map(|name| {
            Ok(Value::object([
                ("path", Value::string(format!("proofs/generated/{name}"))),
                (
                    "sha256",
                    Value::string(sha256_hex(&read_bytes(&generated.join(name))?)),
                ),
            ]))
        })
        .collect::<Result<Vec<_>>>()?;
    let mut checksum_text = String::new();
    for entry in &generated_files {
        writeln!(
            &mut checksum_text,
            "{}  {}",
            required_string(entry, "sha256")?,
            required_string(entry, "path")?
        )
        .unwrap();
    }
    writeln!(
        &mut checksum_text,
        "{}  {archive_name}",
        sha256_hex(&read_bytes(&archive)?)
    )
    .unwrap();
    let checksum = assets_root.join(checksum_name);
    fs::write(&checksum, checksum_text).map_err(|error| EvidenceError(error.to_string()))?;
    let command = direct_command(required_string(&preflight, "runner_policy_sha256")?);
    let external = Value::object([
        (
            "checker_binary_sha256",
            required_value(&preflight, "checker_binary_sha256")?,
        ),
        (
            "checker_build_hash",
            required_value(&preflight, "checker_build_hash")?,
        ),
        ("checker_id", required_value(&preflight, "checker_id")?),
        (
            "checker_registry_path",
            required_value(&preflight, "checker_registry_path")?,
        ),
        (
            "checker_registry_sha256",
            required_value(&preflight, "checker_registry_sha256")?,
        ),
        (
            "checker_version",
            required_value(&preflight, "checker_version")?,
        ),
        (
            "runner_policy_path",
            required_value(&preflight, "runner_policy_path")?,
        ),
        (
            "runner_policy_sha256",
            required_value(&preflight, "runner_policy_sha256")?,
        ),
    ]);
    let verification = Value::object([
        (
            "cargo_lock_path",
            required_value(&build, "cargo_lock_path")?,
        ),
        (
            "cargo_lock_sha256",
            required_value(&build, "cargo_lock_sha256")?,
        ),
        (
            "cargo_manifest_path",
            required_value(&build, "cargo_manifest_path")?,
        ),
        ("cargo_profile", required_value(&build, "cargo_profile")?),
        ("checker_mode", Value::string("external")),
        ("command", Value::string(&command)),
        ("command_result", command_result),
        ("external_checker", external),
        (
            "host_executable_name",
            required_value(&build, "host_executable_name")?,
        ),
        (
            "host_executable_sha256",
            required_value(&build, "host_executable_sha256")?,
        ),
        (
            "npa_cli_crate_version",
            required_value(&build, "npa_cli_crate_version")?,
        ),
        (
            "npa_core_checkout_revision",
            required_value(&build, "npa_core_checkout_revision")?,
        ),
        (
            "npa_core_source_kind",
            required_value(&build, "npa_core_source_kind")?,
        ),
        (
            "npa_core_tree_hash",
            required_value(&build, "npa_core_tree_hash")?,
        ),
        ("package_lock_mode", Value::string("checked")),
        (
            "package_lock_path",
            Value::string("proofs/generated/package-lock.json"),
        ),
        (
            "package_lock_sha256",
            Value::string(sha256_bytes(&read_bytes(
                &generated.join("package-lock.json"),
            )?)),
        ),
        ("rust_target", required_value(&build, "rust_target")?),
        ("rust_toolchain", required_value(&build, "rust_toolchain")?),
        ("verdict_source", Value::string("npa-checker-ext")),
    ]);
    let manifest = Value::object([
        (
            "archive",
            Value::object([
                ("path", Value::string(archive_name)),
                ("sha256", Value::string(sha256_hex(&read_bytes(&archive)?))),
            ]),
        ),
        (
            "check_commands",
            Value::Array(vec![Value::string(&command)]),
        ),
        ("generated_at_utc", Value::string(generated_at_utc)),
        ("generated_files", Value::Array(generated_files)),
        ("generator_commands", Value::Array(vec![])),
        ("npa_core_ref", required_value(&build, "npa_core_ref")?),
        ("omitted_files", Value::Array(vec![])),
        ("package", Value::string("npa-mathlib-downstream")),
        ("package_root", Value::string("proofs")),
        (
            "schema",
            Value::string("npa.generated_artifact_release_manifest.v0.2"),
        ),
        ("source_commit", required_value(&build, "source_commit")?),
        ("tag", Value::string("toolchain-v0.7.0-compat")),
        ("verification", verification),
    ]);
    let manifest_path = assets_root.join(manifest_name);
    write_json(&manifest_path, &manifest)?;
    rehash_build_inputs(&source_root, &core_root, &build)?;
    Ok(Value::object([
        ("archive", Value::string(archive.to_string_lossy())),
        (
            "archive_sha256",
            Value::string(sha256_bytes(&read_bytes(&archive)?)),
        ),
        ("checksum", Value::string(checksum.to_string_lossy())),
        ("command", Value::string(command)),
        ("generated_at_utc", Value::string(generated_at_utc)),
        ("manifest", Value::string(manifest_path.to_string_lossy())),
        (
            "manifest_sha256",
            Value::string(sha256_bytes(&read_bytes(&manifest_path)?)),
        ),
        (
            "schema",
            Value::string(format!("{SCHEMA}.release_assets.v1")),
        ),
        ("status", Value::string("passed")),
    ])
    .canonical())
}

/// Read a scalar field from a duplicate-free JSON document for Shell orchestration.
pub fn json_field(path: &Path, field: &str) -> Result<String> {
    let value = Value::parse_file(path)?;
    match value.get(field) {
        Some(Value::String(value)) | Some(Value::Number(value)) => Ok(format!("{value}\n")),
        Some(Value::Bool(value)) => Ok(format!("{value}\n")),
        _ => Err(EvidenceError(format!("JSON field is not scalar: {field}"))),
    }
}

/// Validate the workspace package-version axes used by the v0.7 gate.
pub fn check_metadata(path: &Path) -> Result<String> {
    let metadata = Value::parse_file(path)?;
    let packages = metadata
        .get("packages")
        .and_then(Value::as_array)
        .ok_or_else(|| EvidenceError("cargo metadata packages missing".into()))?;
    let versions = packages
        .iter()
        .filter_map(|package| {
            Some((
                package.get("name")?.as_str()?,
                package.get("version")?.as_str()?,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    require(
        versions
            .get("npa-cli")
            .is_some_and(|version| version.starts_with("0.7.")),
        "npa-cli metadata is not 0.7.x",
    )?;
    require(
        versions.get("npa-frontend") == Some(&"0.3.0"),
        "npa-frontend metadata left its 0.3.0 axis",
    )?;
    for name in ["npa-api", "npa-cert", "npa-package"] {
        require(
            versions.get(name) == Some(&"0.3.0"),
            format!("{name} metadata left its 0.3.0 axis"),
        )?;
    }
    require(
        versions.get("npa-checker-ref") == Some(&"0.3.0"),
        "npa-checker-ref metadata left its 0.3.0 axis",
    )?;
    for name in ["npa-kernel", "npa-tactic"] {
        require(
            versions.get(name) == Some(&"0.2.0"),
            format!("{name} metadata left its 0.2.0 axis"),
        )?;
    }
    Ok(Value::object([
        (
            "schema",
            Value::string(format!("{SCHEMA}.metadata_check.v1")),
        ),
        ("status", Value::string("passed")),
    ])
    .canonical())
}

/// Report the fixed current compatibility schema identities.
pub fn contract() -> String {
    Value::object([
        (
            "command_result_schema",
            Value::string("npa.package.command_result.v0.3"),
        ),
        (
            "policy_preflight_schema",
            Value::string(format!("{SCHEMA}.policy_preflight.v1")),
        ),
        (
            "preflight_schema",
            Value::string(format!("{SCHEMA}.prepared_inputs.v1")),
        ),
        ("toolchain_tag", Value::string("toolchain-v0.7.0-compat")),
    ])
    .canonical()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp(label: &str) -> PathBuf {
        let id = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!("npa-evidence-{label}-{id}"));
        fs::create_dir(&path).unwrap();
        path
    }

    #[test]
    fn duplicate_fields_are_rejected() {
        let source = "{\"x\":1,\"x\":2}";
        let document = JsonDocument::parse(source).unwrap();
        assert!(convert_json(document.root(), "$", Path::new("input.json"))
            .unwrap_err()
            .to_string()
            .contains("duplicate JSON field"));
    }

    #[test]
    fn contract_is_v0_7_only() {
        let contract = contract();
        assert!(contract.contains("toolchain-v0.7.0-compat"));
        assert!(!contract.contains("toolchain-v0.4"));
        assert!(!contract.contains("toolchain-v0.5"));
    }

    #[test]
    fn joins_split_strace_records() {
        let lines = joined_trace_lines(
            Path::new("trace.1"),
            "openat(AT_FDCWD, \"proofs/generated\", O_RDONLY <unfinished ...>\n<... openat resumed>) = 3\n",
        )
        .unwrap();
        assert_eq!(
            lines,
            ["openat(AT_FDCWD, \"proofs/generated\", O_RDONLY ) = 3"]
        );
    }

    #[test]
    fn checker_runtime_allowlist_is_limited_to_required_loader_files() {
        for path in [
            "/lib/x86_64-linux-gnu/libc.so.6",
            "/usr/lib/aarch64-linux-gnu/libm.so.6",
            "/lib64/ld-linux-x86-64.so.2",
            "/proc/self/fd/7",
        ] {
            assert!(checker_runtime_path_allowed(Path::new(path)), "{path}");
        }
        for path in [
            "/usr/lib/source.npa",
            "/usr/lib/ocaml/compiler-libs/ocamlcommon.cma",
            "/lib/x86_64-linux-gnu/libcrypto.so.3",
            "/proc/self/fd/not-a-number",
        ] {
            assert!(!checker_runtime_path_allowed(Path::new(path)), "{path}");
        }
    }

    #[test]
    fn trace_audit_accepts_required_reads_and_rejects_protected_write() {
        let source = temp("trace");
        let package = source.join("proofs");
        let cert = package.join("M/certificate.npcert");
        let policy = package.join("ci/axiom-policy.toml");
        let imported = package.join("generated/checker-imports/M/certificate.npcert");
        for path in [&cert, &policy, &imported] {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, "fixture").unwrap();
        }
        fs::write(package.join("npa-package.toml"), "fixture").unwrap();
        let fixture = source.join("fixture.json");
        write_json(
            &fixture,
            &Value::object([
                ("module_order", Value::Array(vec![Value::string("M")])),
                (
                    "proof_identities",
                    Value::object([(
                        "M",
                        Value::object([("certificate", Value::string("M/certificate.npcert"))]),
                    )]),
                ),
                ("sentinel_paths", Value::Array(vec![])),
            ]),
        )
        .unwrap();
        let prefix = source.join("trace");
        let trace = source.join("trace.100");
        let required = "execve(\"/proc/self/fd/3\", [\"checker\", \"--cert\", \"M/certificate.npcert\", \"--import-dir\", \"generated/checker-imports/M\", \"--policy\", \"ci/axiom-policy.toml\"], []) = 0\nopenat(AT_FDCWD, \"M/certificate.npcert\", O_RDONLY) = 4\nopenat(AT_FDCWD, \"ci/axiom-policy.toml\", O_RDONLY) = 5\nopenat(AT_FDCWD, \"generated/checker-imports/M/certificate.npcert\", O_RDONLY) = 6\n".to_owned();
        fs::write(&trace, &required).unwrap();
        assert!(check_trace(&prefix, &source, &package, &fixture).is_ok());
        fs::write(
            &trace,
            format!(
                "{required}write(7<{}>, \"x\", 1) = 1\n",
                canonical(&package)
                    .unwrap()
                    .join("npa-package.toml")
                    .display()
            ),
        )
        .unwrap();
        let error = check_trace(&prefix, &source, &package, &fixture).unwrap_err();
        assert!(
            error.to_string().contains("forbidden package write"),
            "{error}"
        );
        fs::remove_dir_all(source).unwrap();
    }

    #[test]
    fn archive_matches_frozen_python_gnu_tar_gzip_bytes() {
        let root = temp("archive");
        let generated = root.join("proofs/generated");
        let result = generated.join(
            "checker-results/npa-mathlib-downstream/0.1.0/Downstream.MathlibBasic/external/result.json",
        );
        fs::create_dir_all(result.parent().unwrap()).unwrap();
        fs::write(generated.join("package-lock.json"), "{\"a\":1}\n").unwrap();
        fs::write(&result, "{\"status\":\"checked\"}\n").unwrap();
        let first = root.join("first.tar.gz");
        let second = root.join("second.tar.gz");
        write_deterministic_generated_archive(&generated, &first).unwrap();
        write_deterministic_generated_archive(&generated, &second).unwrap();
        let first_bytes = fs::read(&first).unwrap();
        assert_eq!(first_bytes, fs::read(&second).unwrap());
        assert_eq!(
            sha256_hex(&first_bytes),
            "409a42cd7707b80f4f8cc17353c9dd6a733ed33c37ed56df2c0c17efb5552047"
        );
        fs::remove_dir_all(root).unwrap();
    }
}
