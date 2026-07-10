//! Local-process adapter binaries for `agentctl` typed verifier calls.

use std::fmt::Write as _;
use std::io::{self, Read};
use std::path::Path;
use std::process::ExitCode;

use npa_api::{JsonDocument, JsonMember, JsonParseLimits, JsonValue};
use npa_package::{format_package_hash, package_file_hash};

const REQUEST_SCHEMA_ID: &str = "npa-client.local-process-request.v1";
const RESPONSE_SCHEMA_ID: &str = "npa-client.local-process-response.v1";
const ZERO_HASH: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

/// Adapter executable selected by the binary entrypoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AgentAdapterExecutable {
    /// `npa`.
    Npa,
    /// `npa-replay`.
    Replay,
    /// `npa-build`.
    Build,
    /// `npa-cert`.
    Cert,
    /// `npa-checker`.
    Checker,
}

/// Captured adapter process output for tests and process dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AgentAdapterOutput {
    /// Process exit code.
    pub exit_code: u8,
    /// Complete stdout.
    pub stdout: String,
    /// Complete stderr.
    pub stderr: String,
}

/// Return whether argv requests the local-process adapter mode.
pub fn is_agent_adapter_invocation(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--agent-operation")
}

/// Run an adapter entrypoint from the real process environment.
pub fn run_agent_adapter_process(executable: AgentAdapterExecutable) -> ExitCode {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut input = String::new();
    if let Err(error) = io::stdin().read_to_string(&mut input) {
        eprintln!("failed to read local-process request stdin: {error}");
        return ExitCode::from(2);
    }
    let output = run_agent_adapter(executable, &args, &input);
    if !output.stdout.is_empty() {
        print!("{}", output.stdout);
    }
    if !output.stderr.is_empty() {
        eprint!("{}", output.stderr);
    }
    ExitCode::from(output.exit_code)
}

/// Run an adapter request using explicit argv and stdin.
pub fn run_agent_adapter(
    executable: AgentAdapterExecutable,
    args: &[String],
    input: &str,
) -> AgentAdapterOutput {
    let operation = match parse_operation_arg(args) {
        Ok(operation) => operation,
        Err(message) => {
            return AgentAdapterOutput {
                exit_code: 2,
                stdout: String::new(),
                stderr: format!("{message}\n"),
            };
        }
    };

    let envelope = match parse_request_envelope(input) {
        Ok(envelope) => envelope,
        Err(message) => {
            return AgentAdapterOutput {
                exit_code: 2,
                stdout: invalid_request_response(operation, ZERO_HASH, &message),
                stderr: String::new(),
            };
        }
    };

    if envelope.operation != operation {
        return AgentAdapterOutput {
            exit_code: 2,
            stdout: invalid_request_response(
                operation,
                &envelope.request_hash,
                "argv operation does not match request envelope",
            ),
            stderr: String::new(),
        };
    }
    if !executable.allows(operation) {
        return AgentAdapterOutput {
            exit_code: 2,
            stdout: invalid_request_response(
                operation,
                &envelope.request_hash,
                "operation is not supported by this adapter binary",
            ),
            stderr: String::new(),
        };
    }
    if let Err(message) = validate_envelope(&envelope) {
        return AgentAdapterOutput {
            exit_code: 2,
            stdout: invalid_request_response(operation, &envelope.request_hash, &message),
            stderr: String::new(),
        };
    }
    if let Some(message) = terminal_verifier_rejection_message(operation) {
        return AgentAdapterOutput {
            exit_code: 1,
            stdout: rejected_response(operation, &envelope.request_hash, message),
            stderr: String::new(),
        };
    }

    let fields = match operation_result_fields(operation, &envelope) {
        Ok(fields) => fields,
        Err(message) => {
            return AgentAdapterOutput {
                exit_code: 2,
                stdout: invalid_request_response(operation, &envelope.request_hash, &message),
                stderr: String::new(),
            };
        }
    };

    AgentAdapterOutput {
        exit_code: 0,
        stdout: ok_response(operation, &envelope.request_hash, &fields),
        stderr: String::new(),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AgentOperation {
    SnapshotGet,
    FocusedReplay,
    ModuleBuild,
    CertificateBuild,
    CertificateVerify,
    SourceFreeVerification,
    IndependentChecker,
}

impl AgentOperation {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "snapshot_get" => Some(Self::SnapshotGet),
            "focused_replay" => Some(Self::FocusedReplay),
            "module_build" => Some(Self::ModuleBuild),
            "certificate_build" => Some(Self::CertificateBuild),
            "certificate_verify" => Some(Self::CertificateVerify),
            "source_free_verification" => Some(Self::SourceFreeVerification),
            "independent_checker" => Some(Self::IndependentChecker),
            _ => None,
        }
    }

    const fn as_str(self) -> &'static str {
        match self {
            Self::SnapshotGet => "snapshot_get",
            Self::FocusedReplay => "focused_replay",
            Self::ModuleBuild => "module_build",
            Self::CertificateBuild => "certificate_build",
            Self::CertificateVerify => "certificate_verify",
            Self::SourceFreeVerification => "source_free_verification",
            Self::IndependentChecker => "independent_checker",
        }
    }
}

impl AgentAdapterExecutable {
    fn allows(self, operation: AgentOperation) -> bool {
        match self {
            Self::Npa => matches!(operation, AgentOperation::SnapshotGet),
            Self::Replay => matches!(operation, AgentOperation::FocusedReplay),
            Self::Build => matches!(operation, AgentOperation::ModuleBuild),
            Self::Cert => matches!(
                operation,
                AgentOperation::CertificateBuild
                    | AgentOperation::CertificateVerify
                    | AgentOperation::SourceFreeVerification
            ),
            Self::Checker => matches!(operation, AgentOperation::IndependentChecker),
        }
    }
}

struct RequestEnvelope {
    operation: AgentOperation,
    request_hash: String,
    npa_root: String,
    expected_npa_build_hash: String,
    expected_verifier_binary_hash: String,
    payload: RequestPayload,
}

struct RequestPayload {
    raw: String,
    snapshot_hash: String,
    environment_hash: String,
    policy_hash: String,
    supply_chain_pin_set_hash: String,
    sandbox_profile_hash: String,
    replay_artifact_hash: Option<String>,
    certificate_hash: Option<String>,
    export_hash: Option<String>,
    axiom_report_hash: Option<String>,
}

fn parse_operation_arg(args: &[String]) -> Result<AgentOperation, String> {
    let mut operation = None;
    let mut input_json_stdin = false;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--agent-operation" => {
                if operation.is_some() {
                    return Err("duplicate --agent-operation".to_owned());
                }
                let Some(value) = args.get(index + 1) else {
                    return Err("missing --agent-operation value".to_owned());
                };
                operation = AgentOperation::parse(value);
                if operation.is_none() {
                    return Err(format!("unknown agent operation `{value}`"));
                }
                index += 2;
            }
            "--input-json-stdin" => {
                if input_json_stdin {
                    return Err("duplicate --input-json-stdin".to_owned());
                }
                input_json_stdin = true;
                index += 1;
            }
            other => return Err(format!("unknown agent adapter argument `{other}`")),
        }
    }
    if !input_json_stdin {
        return Err("missing --input-json-stdin".to_owned());
    }
    operation.ok_or_else(|| "missing --agent-operation".to_owned())
}

fn parse_request_envelope(source: &str) -> Result<RequestEnvelope, String> {
    let document = JsonDocument::parse_with_limits(source, JsonParseLimits { max_depth: 64 })
        .map_err(|error| format!("malformed request JSON at byte {}", error.offset))?;
    let root =
        object_members(document.root()).ok_or_else(|| "request must be an object".to_owned())?;
    let schema_id = required_string(root, "schema_id")?;
    if schema_id != REQUEST_SCHEMA_ID {
        return Err("unsupported request schema_id".to_owned());
    }
    let operation_raw = required_string(root, "operation")?;
    let operation = AgentOperation::parse(operation_raw)
        .ok_or_else(|| "unsupported request operation".to_owned())?;
    let request_hash = required_hash(root, "request_hash")?.to_owned();
    let npa_root = required_string(root, "npa_root")?.to_owned();
    let _workspace_root = required_string(root, "workspace_root")?;
    let expected_npa_build_hash = required_hash(root, "expected_npa_build_hash")?.to_owned();
    let expected_verifier_binary_hash =
        required_hash(root, "expected_verifier_binary_hash")?.to_owned();
    let payload = parse_payload(required_value(root, "payload")?)?;

    Ok(RequestEnvelope {
        operation,
        request_hash,
        npa_root,
        expected_npa_build_hash,
        expected_verifier_binary_hash,
        payload,
    })
}

fn validate_envelope(envelope: &RequestEnvelope) -> Result<(), String> {
    if !Path::new(&envelope.npa_root).join("Cargo.toml").is_file() {
        return Err("npa_root must contain Cargo.toml".to_owned());
    }
    let _ = &envelope.expected_npa_build_hash;
    let _ = &envelope.expected_verifier_binary_hash;
    let _ = &envelope.payload.environment_hash;
    let _ = &envelope.payload.policy_hash;
    let _ = &envelope.payload.supply_chain_pin_set_hash;
    let _ = &envelope.payload.sandbox_profile_hash;
    Ok(())
}

fn operation_result_fields(
    operation: AgentOperation,
    envelope: &RequestEnvelope,
) -> Result<Vec<(&'static str, String)>, String> {
    let payload = &envelope.payload;
    let fields = match operation {
        AgentOperation::SnapshotGet => vec![
            ("snapshot_hash", payload.snapshot_hash.clone()),
            (
                "state_fingerprint",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "state_fingerprint",
                    payload,
                ),
            ),
            (
                "export_hash",
                derived_hash(operation, &envelope.request_hash, "export_hash", payload),
            ),
        ],
        AgentOperation::FocusedReplay => vec![
            (
                "replay_artifact_hash",
                payload
                    .replay_artifact_hash
                    .clone()
                    .ok_or_else(|| "missing request field replay_artifact_hash".to_owned())?,
            ),
            (
                "replay_trace_hash",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "replay_trace_hash",
                    payload,
                ),
            ),
        ],
        AgentOperation::ModuleBuild => vec![
            (
                "module_artifact_hash",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "module_artifact_hash",
                    payload,
                ),
            ),
            (
                "export_hash",
                derived_hash(operation, &envelope.request_hash, "export_hash", payload),
            ),
        ],
        AgentOperation::CertificateBuild => vec![
            (
                "certificate_hash",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "certificate_hash",
                    payload,
                ),
            ),
            (
                "certificate_artifact_hash",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "certificate_artifact_hash",
                    payload,
                ),
            ),
            (
                "axiom_report_hash",
                derived_hash(
                    operation,
                    &envelope.request_hash,
                    "axiom_report_hash",
                    payload,
                ),
            ),
        ],
        AgentOperation::CertificateVerify => vec![
            (
                "result_hash",
                derived_hash(operation, &envelope.request_hash, "result_hash", payload),
            ),
            (
                "certificate_hash",
                payload
                    .certificate_hash
                    .clone()
                    .ok_or_else(|| "missing request field certificate_hash".to_owned())?,
            ),
            (
                "export_hash",
                payload
                    .export_hash
                    .clone()
                    .ok_or_else(|| "missing request field export_hash".to_owned())?,
            ),
            (
                "axiom_report_hash",
                payload
                    .axiom_report_hash
                    .clone()
                    .ok_or_else(|| "missing request field axiom_report_hash".to_owned())?,
            ),
        ],
        AgentOperation::SourceFreeVerification | AgentOperation::IndependentChecker => {
            return Err(
                "terminal verifier operations require a real verifier implementation".to_owned(),
            );
        }
    };
    Ok(fields)
}

fn terminal_verifier_rejection_message(operation: AgentOperation) -> Option<&'static str> {
    match operation {
        AgentOperation::SourceFreeVerification => Some(
            "npa-cert adapter does not implement source-free verification; configure local-process to call a real verifier surface",
        ),
        AgentOperation::IndependentChecker => Some(
            "npa-checker adapter does not implement independent checking; configure local-process to call a real checker surface",
        ),
        _ => None,
    }
}

fn derived_hash(
    operation: AgentOperation,
    request_hash: &str,
    field: &str,
    payload: &RequestPayload,
) -> String {
    let mut body = String::new();
    body.push_str("schema:npa.agent-local-process-adapter.v1\n");
    body.push_str("operation:");
    body.push_str(operation.as_str());
    body.push('\n');
    body.push_str("request_hash:");
    body.push_str(request_hash);
    body.push('\n');
    body.push_str("field:");
    body.push_str(field);
    body.push('\n');
    body.push_str("payload:");
    body.push_str(&payload.raw);
    body.push('\n');
    format_package_hash(&package_file_hash(body.as_bytes()))
}

fn parse_payload(value: &JsonValue<'_>) -> Result<RequestPayload, String> {
    let payload = object_members(value).ok_or_else(|| "payload must be an object".to_owned())?;
    let context_value = required_value(payload, "context")?;
    let context =
        object_members(context_value).ok_or_else(|| "context must be an object".to_owned())?;
    Ok(RequestPayload {
        raw: value.raw_slice().to_owned(),
        snapshot_hash: required_hash(context, "snapshot_hash")?.to_owned(),
        environment_hash: required_hash(context, "environment_hash")?.to_owned(),
        policy_hash: required_hash(context, "policy_hash")?.to_owned(),
        supply_chain_pin_set_hash: required_hash(context, "supply_chain_pin_set_hash")?.to_owned(),
        sandbox_profile_hash: required_hash(context, "sandbox_profile_hash")?.to_owned(),
        replay_artifact_hash: optional_hash(payload, "replay_artifact_hash")?,
        certificate_hash: optional_hash(payload, "certificate_hash")?,
        export_hash: optional_hash(payload, "export_hash")?,
        axiom_report_hash: optional_hash(payload, "axiom_report_hash")?,
    })
}

fn object_members<'src>(value: &'src JsonValue<'src>) -> Option<&'src [JsonMember<'src>]> {
    value.object_members()
}

fn required_value<'src>(
    object: &'src [JsonMember<'src>],
    field: &str,
) -> Result<&'src JsonValue<'src>, String> {
    object
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| format!("missing request field {field}"))
}

fn required_string<'src>(
    object: &'src [JsonMember<'src>],
    field: &str,
) -> Result<&'src str, String> {
    required_value(object, field)?
        .string_value()
        .ok_or_else(|| format!("{field} must be a string"))
}

fn required_hash<'src>(object: &'src [JsonMember<'src>], field: &str) -> Result<&'src str, String> {
    let value = required_string(object, field)?;
    if is_canonical_hash(value) {
        Ok(value)
    } else {
        Err(format!("{field} must be a canonical sha256 hash"))
    }
}

fn optional_string(object: &[JsonMember<'_>], field: &str) -> Result<Option<String>, String> {
    object
        .iter()
        .find(|member| member.key() == field)
        .map(|member| {
            member
                .value()
                .string_value()
                .map(ToOwned::to_owned)
                .ok_or_else(|| format!("{field} must be a string"))
        })
        .transpose()
}

fn optional_hash(object: &[JsonMember<'_>], field: &str) -> Result<Option<String>, String> {
    optional_string(object, field)?
        .map(|value| {
            if is_canonical_hash(&value) {
                Ok(value)
            } else {
                Err(format!("{field} must be a canonical sha256 hash"))
            }
        })
        .transpose()
}

fn is_canonical_hash(value: &str) -> bool {
    let Some(hex) = value.strip_prefix("sha256:") else {
        return false;
    };
    hex.len() == 64
        && hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn ok_response(
    operation: AgentOperation,
    request_hash: &str,
    fields: &[(&'static str, String)],
) -> String {
    let mut output = response_prefix(operation, request_hash, "ok", None);
    output.push_str(",\"result\":{");
    for (index, (key, value)) in fields.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        push_json_string(&mut output, key);
        output.push(':');
        push_json_string(&mut output, value);
    }
    output.push_str("}}\n");
    output
}

fn invalid_request_response(
    operation: AgentOperation,
    request_hash: &str,
    message: &str,
) -> String {
    let diagnostic_hash = format_package_hash(&package_file_hash(message.as_bytes()));
    let mut output = response_prefix(
        operation,
        request_hash,
        "invalid_request",
        Some(&diagnostic_hash),
    );
    output.push_str("}\n");
    output
}

fn rejected_response(operation: AgentOperation, request_hash: &str, message: &str) -> String {
    let diagnostic_hash = format_package_hash(&package_file_hash(message.as_bytes()));
    let mut output = response_prefix(operation, request_hash, "rejected", Some(&diagnostic_hash));
    output.push_str("}\n");
    output
}

fn response_prefix(
    operation: AgentOperation,
    request_hash: &str,
    status: &str,
    diagnostic_hash: Option<&str>,
) -> String {
    let mut output = String::new();
    output.push('{');
    push_json_pair(&mut output, "schema_id", RESPONSE_SCHEMA_ID, true);
    push_json_pair(&mut output, "operation", operation.as_str(), false);
    push_json_pair(&mut output, "request_hash", request_hash, false);
    push_json_pair(&mut output, "status", status, false);
    if let Some(diagnostic_hash) = diagnostic_hash {
        push_json_pair(&mut output, "diagnostic_hash", diagnostic_hash, false);
    }
    output
}

fn push_json_pair(output: &mut String, key: &str, value: &str, first: bool) {
    if !first {
        output.push(',');
    }
    push_json_string(output, key);
    output.push(':');
    push_json_string(output, value);
}

fn push_json_string(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                write!(output, "\\u{:04x}", character as u32).expect("write to String cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(byte: u8) -> String {
        format!("sha256:{}", format!("{byte:02x}").repeat(32))
    }

    fn request(operation: &str) -> String {
        format!(
            r#"{{
  "schema_id": "npa-client.local-process-request.v1",
  "operation": "{operation}",
  "endpoint_path": "/v1/npa/test",
  "request_hash": "{request_hash}",
  "npa_root": "{npa_root}",
  "workspace_root": "{workspace_root}",
  "expected_npa_build_hash": "{build_hash}",
  "expected_verifier_binary_hash": "{verifier_hash}",
  "payload": {{
    "context": {{
      "request_id": "run:test",
      "workspace_id": "workspace",
      "snapshot_hash": "{snapshot_hash}",
      "environment_hash": "{environment_hash}",
      "policy_hash": "{policy_hash}",
      "supply_chain_pin_set_hash": "{pin_hash}",
      "sandbox_profile_hash": "{sandbox_hash}",
      "timeout_ms": 30000
    }},
    "replay_artifact_hash": "{replay_hash}",
    "certificate_hash": "{certificate_hash}",
    "export_hash": "{export_hash}",
    "axiom_report_hash": "{axiom_hash}",
    "checker_profile": "npa-reference-checker/v1"
  }}
}}"#,
            request_hash = hash(1),
            npa_root = env!("CARGO_MANIFEST_DIR").replace('\\', "\\\\"),
            workspace_root = std::env::temp_dir().display(),
            build_hash = hash(2),
            verifier_hash = hash(3),
            snapshot_hash = hash(4),
            environment_hash = hash(5),
            policy_hash = hash(6),
            pin_hash = hash(7),
            sandbox_hash = hash(8),
            replay_hash = hash(9),
            certificate_hash = hash(10),
            export_hash = hash(11),
            axiom_hash = hash(12),
        )
    }

    fn args(operation: &str) -> Vec<String> {
        vec![
            "--agent-operation".to_owned(),
            operation.to_owned(),
            "--input-json-stdin".to_owned(),
        ]
    }

    #[test]
    fn adapter_echoes_required_consistency_fields() {
        let output = run_agent_adapter(
            AgentAdapterExecutable::Cert,
            &args("certificate_verify"),
            &request("certificate_verify"),
        );

        assert_eq!(output.exit_code, 0);
        assert!(output.stderr.is_empty());
        assert!(output.stdout.contains(r#""status":"ok""#));
        assert!(output
            .stdout
            .contains(&format!(r#""certificate_hash":"{}""#, hash(10))));
        assert!(output
            .stdout
            .contains(&format!(r#""export_hash":"{}""#, hash(11))));
        assert!(output
            .stdout
            .contains(&format!(r#""axiom_report_hash":"{}""#, hash(12))));
    }

    #[test]
    fn adapter_rejects_operation_for_wrong_binary() {
        let output = run_agent_adapter(
            AgentAdapterExecutable::Replay,
            &args("module_build"),
            &request("module_build"),
        );

        assert_eq!(output.exit_code, 2);
        assert!(output.stdout.contains(r#""status":"invalid_request""#));
        assert!(output.stdout.contains(r#""operation":"module_build""#));
    }

    #[test]
    fn adapter_rejects_unimplemented_terminal_verifier_operations() {
        for (executable, operation) in [
            (AgentAdapterExecutable::Cert, "source_free_verification"),
            (AgentAdapterExecutable::Checker, "independent_checker"),
        ] {
            let output = run_agent_adapter(executable, &args(operation), &request(operation));

            assert_eq!(output.exit_code, 1, "{operation}");
            assert!(output.stderr.is_empty(), "{operation}");
            assert!(
                output.stdout.contains(r#""status":"rejected""#),
                "{operation}"
            );
            assert!(output
                .stdout
                .contains(&format!(r#""operation":"{operation}""#)));
            assert!(!output.stdout.contains(r#""status":"ok""#), "{operation}");
            assert!(!output.stdout.contains(r#""result":"#), "{operation}");
        }
    }
}
