//! Structured command diagnostics and deterministic renderers.

use std::fmt::Write as _;

use crate::args::CliUsageError;

/// Stable schema string for package command results.
pub const PACKAGE_COMMAND_RESULT_SCHEMA: &str = "npa.package.command_result.v0.3";
/// Stable schema string for optional package timing telemetry.
pub const PACKAGE_TIMINGS_SCHEMA: &str = "npa.package.timings.v0.1";

/// Process exit class for a command result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CommandExitCode {
    /// Command succeeded.
    Success,
    /// Package validation, hash, build, or checker failure.
    PackageFailure,
    /// CLI usage error or unexpected internal failure.
    UsageOrInternal,
}

impl CommandExitCode {
    /// Numeric process exit code.
    pub const fn as_u8(self) -> u8 {
        match self {
            Self::Success => 0,
            Self::PackageFailure => 1,
            Self::UsageOrInternal => 2,
        }
    }
}

/// Aggregate command status.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CommandStatus {
    /// Command completed successfully.
    Passed,
    /// Command failed.
    Failed,
}

impl CommandStatus {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Passed => "passed",
            Self::Failed => "failed",
        }
    }
}

/// Diagnostic category.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticKind {
    /// CLI usage and argument parsing.
    Usage,
    /// Package manifest parsing or validation.
    PackageManifest,
    /// Package graph validation.
    PackageGraph,
    /// Package lock parsing or validation.
    PackageLock,
    /// Filesystem access for package artifacts.
    ArtifactIo,
    /// Hash mismatch.
    HashMismatch,
    /// Certificate build failure.
    Build,
    /// Source-free boundary violation.
    SourceFreeBoundary,
    /// Fast verifier rejection.
    FastVerifier,
    /// Reference verifier rejection.
    ReferenceVerifier,
    /// External checker runner rejection.
    ExternalVerifier,
    /// Package axiom report generation or checking.
    AxiomReport,
    /// Package theorem index generation or checking.
    TheoremIndex,
    /// Generated package artifact freshness or filesystem operation.
    GeneratedArtifact,
    /// Package artifact policy evaluation.
    PackagePolicy,
    /// Unexpected internal command failure.
    Internal,
}

impl DiagnosticKind {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Usage => "Usage",
            Self::PackageManifest => "PackageManifest",
            Self::PackageGraph => "PackageGraph",
            Self::PackageLock => "PackageLock",
            Self::ArtifactIo => "ArtifactIo",
            Self::HashMismatch => "HashMismatch",
            Self::Build => "Build",
            Self::SourceFreeBoundary => "SourceFreeBoundary",
            Self::FastVerifier => "FastVerifier",
            Self::ReferenceVerifier => "ReferenceVerifier",
            Self::ExternalVerifier => "ExternalVerifier",
            Self::AxiomReport => "AxiomReport",
            Self::TheoremIndex => "TheoremIndex",
            Self::GeneratedArtifact => "GeneratedArtifact",
            Self::PackagePolicy => "PackagePolicy",
            Self::Internal => "Internal",
        }
    }

    fn exit_code(self) -> CommandExitCode {
        match self {
            Self::Usage | Self::Internal => CommandExitCode::UsageOrInternal,
            Self::PackageManifest
            | Self::PackageGraph
            | Self::PackageLock
            | Self::ArtifactIo
            | Self::HashMismatch
            | Self::Build
            | Self::SourceFreeBoundary
            | Self::FastVerifier
            | Self::ReferenceVerifier
            | Self::ExternalVerifier
            | Self::AxiomReport
            | Self::TheoremIndex
            | Self::GeneratedArtifact
            | Self::PackagePolicy => CommandExitCode::PackageFailure,
        }
    }
}

/// Diagnostic severity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticSeverity {
    /// Informational diagnostic.
    Info,
    /// Error diagnostic.
    Error,
}

impl DiagnosticSeverity {
    /// Stable JSON spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Info => "info",
            Self::Error => "error",
        }
    }
}

/// Source-local context for a command diagnostic.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandDiagnosticSourceContext {
    /// Package-relative Human source path.
    path: String,
    /// Inclusive UTF-8 byte offset of the primary span start.
    start_byte: u32,
    /// Exclusive UTF-8 byte offset of the primary span end.
    end_byte: u32,
    /// Containing source declaration, relative to the current module.
    declaration: Option<String>,
    /// One-based source line for `start_byte`, when safely derived.
    line: Option<u32>,
    /// One-based Unicode-scalar column for `start_byte`, when safely derived.
    column: Option<u32>,
    /// Exact bounded primary-span token, when safe to expose.
    token: Option<String>,
}

/// Bounded kernel conversion context in command diagnostics.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandDiagnosticConversionContext {
    phase: String,
    outcome: String,
    lhs_head: String,
    rhs_head: String,
    depth: u32,
}

impl CommandDiagnosticConversionContext {
    /// Build a context when phase, outcome, and heads use bounded stable forms.
    pub fn new(
        phase: impl Into<String>,
        outcome: impl Into<String>,
        lhs_head: impl Into<String>,
        rhs_head: impl Into<String>,
        depth: u32,
    ) -> Option<Self> {
        let phase = phase.into();
        let outcome = outcome.into();
        let lhs_head = lhs_head.into();
        let rhs_head = rhs_head.into();
        const PHASES: &[&str] = &[
            "term_check",
            "declaration_type",
            "declaration_value",
            "inductive_constructor",
            "inductive_recursor",
            "definitional_equality",
        ];
        if !PHASES.contains(&phase.as_str())
            || !matches!(outcome.as_str(), "not_defeq" | "fuel_exhausted")
            || !valid_kernel_head(&lhs_head)
            || !valid_kernel_head(&rhs_head)
        {
            return None;
        }
        Some(Self {
            phase,
            outcome,
            lhs_head,
            rhs_head,
            depth,
        })
    }

    /// Return the stable kernel phase.
    pub fn phase(&self) -> &str {
        &self.phase
    }

    /// Return the stable comparison outcome.
    pub fn outcome(&self) -> &str {
        &self.outcome
    }

    /// Return the bounded left expression head.
    pub fn lhs_head(&self) -> &str {
        &self.lhs_head
    }

    /// Return the bounded right expression head.
    pub fn rhs_head(&self) -> &str {
        &self.rhs_head
    }

    /// Return conversion recursion depth.
    pub const fn depth(&self) -> u32 {
        self.depth
    }
}

fn valid_kernel_head(head: &str) -> bool {
    matches!(
        head,
        "sort" | "bound_variable" | "application" | "lambda" | "pi" | "let" | "unknown"
    ) || head.strip_prefix("constant:").is_some_and(|name| {
        !name.is_empty() && name.len() <= 256 && !name.chars().any(char::is_control)
    })
}

impl CommandDiagnosticSourceContext {
    /// Build source context for a nonempty path and non-reversed byte range.
    pub fn new(path: impl Into<String>, start_byte: u32, end_byte: u32) -> Option<Self> {
        let path = path.into();
        if path.is_empty() || start_byte > end_byte {
            return None;
        }
        Some(Self {
            path,
            start_byte,
            end_byte,
            declaration: None,
            line: None,
            column: None,
            token: None,
        })
    }

    /// Attach a containing source declaration when the name is nonempty.
    #[must_use]
    pub fn with_declaration(mut self, declaration: impl Into<String>) -> Self {
        let declaration = declaration.into();
        if !declaration.is_empty() {
            self.declaration = Some(declaration);
        }
        self
    }

    /// Attach one-based line and Unicode-scalar column when both are positive.
    #[must_use]
    pub fn with_display_location(mut self, line: u32, column: u32) -> Self {
        if line > 0 && column > 0 {
            self.line = Some(line);
            self.column = Some(column);
        }
        self
    }

    /// Attach an exact bounded token when it satisfies the public output bound.
    #[must_use]
    pub fn with_token(mut self, token: impl Into<String>) -> Self {
        let token = token.into();
        if !token.is_empty()
            && token.len() <= 64
            && !token.chars().any(char::is_control)
            && !token.chars().all(char::is_whitespace)
        {
            self.token = Some(token);
        }
        self
    }

    /// Return the package-relative source path.
    pub fn path(&self) -> &str {
        &self.path
    }

    /// Return the inclusive UTF-8 byte offset of the primary span start.
    pub const fn start_byte(&self) -> u32 {
        self.start_byte
    }

    /// Return the exclusive UTF-8 byte offset of the primary span end.
    pub const fn end_byte(&self) -> u32 {
        self.end_byte
    }

    /// Return the containing source declaration when available.
    pub fn declaration(&self) -> Option<&str> {
        self.declaration.as_deref()
    }

    /// Return the one-based source line when available.
    pub const fn line(&self) -> Option<u32> {
        self.line
    }

    /// Return the one-based Unicode-scalar column when available.
    pub const fn column(&self) -> Option<u32> {
        self.column
    }

    /// Return the bounded primary-span token when available.
    pub fn token(&self) -> Option<&str> {
        self.token.as_deref()
    }
}

/// A single deterministic command diagnostic.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandDiagnostic {
    /// Diagnostic category.
    pub kind: DiagnosticKind,
    /// Stable machine-readable reason code.
    pub reason_code: String,
    /// Diagnostic severity.
    pub severity: DiagnosticSeverity,
    /// Module name, when applicable.
    pub module: Option<String>,
    /// Package-relative path or manifest path, when applicable.
    pub path: Option<String>,
    /// Field name, when applicable.
    pub field: Option<String>,
    /// Expected hash, when applicable.
    pub expected_hash: Option<String>,
    /// Actual hash, when applicable.
    pub actual_hash: Option<String>,
    /// Expected value, when applicable.
    pub expected_value: Option<String>,
    /// Actual value, when applicable.
    pub actual_value: Option<String>,
    /// Checker name, when applicable.
    pub checker: Option<String>,
    /// Source-local context, when the diagnostic originates in authoring text.
    pub source: Option<CommandDiagnosticSourceContext>,
    /// Bounded kernel conversion context, when available.
    pub conversion: Option<CommandDiagnosticConversionContext>,
}

impl CommandDiagnostic {
    /// Build an error diagnostic with the given category and reason code.
    pub fn error(kind: DiagnosticKind, reason_code: impl Into<String>) -> Self {
        Self {
            kind,
            reason_code: reason_code.into(),
            severity: DiagnosticSeverity::Error,
            module: None,
            path: None,
            field: None,
            expected_hash: None,
            actual_hash: None,
            expected_value: None,
            actual_value: None,
            checker: None,
            source: None,
            conversion: None,
        }
    }

    /// Build an informational diagnostic with the given category and reason code.
    pub fn info(kind: DiagnosticKind, reason_code: impl Into<String>) -> Self {
        Self {
            kind,
            reason_code: reason_code.into(),
            severity: DiagnosticSeverity::Info,
            module: None,
            path: None,
            field: None,
            expected_hash: None,
            actual_hash: None,
            expected_value: None,
            actual_value: None,
            checker: None,
            source: None,
            conversion: None,
        }
    }

    /// Attach a package-relative path or manifest path.
    pub fn with_path(mut self, path: impl Into<String>) -> Self {
        self.path = Some(path.into());
        self
    }

    /// Attach a module name.
    pub fn with_module(mut self, module: impl Into<String>) -> Self {
        self.module = Some(module.into());
        self
    }

    /// Attach a field name.
    pub fn with_field(mut self, field: impl Into<String>) -> Self {
        self.field = Some(field.into());
        self
    }

    /// Attach an expected value.
    pub fn with_expected_value(mut self, expected_value: impl Into<String>) -> Self {
        self.expected_value = Some(expected_value.into());
        self
    }

    /// Attach an actual value.
    pub fn with_actual_value(mut self, actual_value: impl Into<String>) -> Self {
        self.actual_value = Some(actual_value.into());
        self
    }

    /// Attach the checker implementation that produced or owns the result.
    pub fn with_checker(mut self, checker: impl Into<String>) -> Self {
        self.checker = Some(checker.into());
        self
    }

    /// Attach source-local context.
    #[must_use]
    pub fn with_source(mut self, source: CommandDiagnosticSourceContext) -> Self {
        self.source = Some(source);
        self
    }

    /// Attach bounded kernel conversion context.
    #[must_use]
    pub fn with_conversion(mut self, conversion: CommandDiagnosticConversionContext) -> Self {
        self.conversion = Some(conversion);
        self
    }

    /// Attach expected and actual hash values.
    pub fn with_hashes(
        mut self,
        expected_hash: impl Into<String>,
        actual_hash: impl Into<String>,
    ) -> Self {
        self.expected_hash = Some(expected_hash.into());
        self.actual_hash = Some(actual_hash.into());
        self
    }

    /// Convert a CLI usage parser error into a command diagnostic.
    pub fn from_usage_error(error: &CliUsageError) -> Self {
        let mut diagnostic = Self::error(DiagnosticKind::Usage, error.reason.reason_code());
        diagnostic.field = error.flag.clone();
        diagnostic.actual_value = error.value.clone();
        diagnostic
    }

    /// Convert an `npa-package` manifest error into a command diagnostic.
    pub fn from_package_manifest_error(error: &npa_package::PackageManifestError) -> Self {
        let kind = match error.kind {
            npa_package::PackageManifestErrorKind::Graph => DiagnosticKind::PackageGraph,
            _ => DiagnosticKind::PackageManifest,
        };
        Self {
            kind,
            reason_code: error.reason_code.as_str().to_owned(),
            severity: DiagnosticSeverity::Error,
            module: None,
            path: Some(error.path.clone()),
            field: error.field.clone(),
            expected_hash: None,
            actual_hash: None,
            expected_value: error.expected_value.clone(),
            actual_value: error.actual_value.clone(),
            checker: None,
            source: None,
            conversion: None,
        }
    }

    /// Convert an `npa-package` lock error into a command diagnostic.
    pub fn from_package_lock_error(error: &npa_package::PackageLockError) -> Self {
        let kind = match error.kind {
            _ if is_lock_hash_mismatch(error.reason_code) => DiagnosticKind::HashMismatch,
            npa_package::PackageLockErrorKind::ArtifactIo => DiagnosticKind::ArtifactIo,
            npa_package::PackageLockErrorKind::Graph => DiagnosticKind::PackageGraph,
            _ => DiagnosticKind::PackageLock,
        };
        let mut diagnostic = Self {
            kind,
            reason_code: error.reason_code.as_str().to_owned(),
            severity: DiagnosticSeverity::Error,
            module: error.module.as_ref().map(|module| module.to_string()),
            path: Some(error.path.clone()),
            field: error.field.clone(),
            expected_hash: None,
            actual_hash: None,
            expected_value: error.expected_value.clone(),
            actual_value: error.actual_value.clone(),
            checker: None,
            source: None,
            conversion: None,
        };
        if kind == DiagnosticKind::HashMismatch {
            diagnostic.expected_hash = error.expected_value.clone();
            diagnostic.actual_hash = error.actual_value.clone();
            diagnostic.expected_value = None;
            diagnostic.actual_value = None;
        }
        diagnostic
    }

    fn render_human(&self) -> String {
        let mut message = format!(
            "{} {} {}",
            self.severity.as_str(),
            self.kind.as_str(),
            self.reason_code
        );
        if let Some(path) = &self.path {
            message.push_str(&format!(" path={path}"));
        }
        if let Some(module) = &self.module {
            message.push_str(&format!(" module={module}"));
        }
        if let Some(field) = &self.field {
            message.push_str(&format!(" field={field}"));
        }
        if let Some(source) = &self.source {
            message.push_str(&format!(
                " source={}:byte[{}..{}]",
                source.path, source.start_byte, source.end_byte
            ));
            if let Some(line) = source.line {
                message.push_str(&format!(" line={line}"));
            }
            if let Some(column) = source.column {
                message.push_str(&format!(" column={column}"));
            }
            if let Some(declaration) = &source.declaration {
                message.push_str(&format!(" declaration={declaration}"));
            }
            if let Some(token) = &source.token {
                let mut quoted = String::new();
                push_json_string(&mut quoted, token);
                message.push_str(&format!(" token={quoted}"));
            }
        }
        if let Some(conversion) = &self.conversion {
            message.push_str(&format!(
                " conversion=phase:{},outcome:{},lhs:{},rhs:{},depth:{}",
                conversion.phase,
                conversion.outcome,
                conversion.lhs_head,
                conversion.rhs_head,
                conversion.depth
            ));
        }
        if let Some(expected) = &self.expected_value {
            message.push_str(&format!(" expected={expected}"));
        }
        if let Some(actual) = &self.actual_value {
            message.push_str(&format!(" actual={actual}"));
        }
        if let Some(expected) = &self.expected_hash {
            message.push_str(&format!(" expected_hash={expected}"));
        }
        if let Some(actual) = &self.actual_hash {
            message.push_str(&format!(" actual_hash={actual}"));
        }
        message
    }
}

fn is_lock_hash_mismatch(reason: npa_package::PackageLockErrorReason) -> bool {
    matches!(
        reason,
        npa_package::PackageLockErrorReason::CertificateFileHashMismatch
            | npa_package::PackageLockErrorReason::ExportHashMismatch
            | npa_package::PackageLockErrorReason::AxiomReportHashMismatch
            | npa_package::PackageLockErrorReason::CertificateHashMismatch
            | npa_package::PackageLockErrorReason::LockImportExportHashMismatch
            | npa_package::PackageLockErrorReason::LockImportCertificateHashMismatch
    )
}

/// A command-owned artifact entry for command results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandArtifact {
    /// Artifact category.
    pub kind: String,
    /// Package-relative artifact path.
    pub path: String,
}

/// A single command timing metric in milliseconds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandTimingMetric {
    /// Stable JSON field name, including the `_ms` unit suffix.
    pub field: String,
    /// Elapsed milliseconds for this phase.
    pub milliseconds: u128,
}

/// Optional package command timing telemetry.
///
/// Timing telemetry is informational only: it is neither proof evidence nor
/// build evidence, and it must not influence command pass/fail behavior.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandTimings {
    /// Requested timing mode label.
    pub mode: String,
    /// Stable timing metrics in render order.
    pub metrics: Vec<CommandTimingMetric>,
}

/// Deterministic command result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandResult {
    /// Command name.
    pub command: String,
    /// Sanitized root display string.
    pub root: String,
    /// Aggregate status.
    pub status: CommandStatus,
    /// Structured diagnostics.
    pub diagnostics: Vec<CommandDiagnostic>,
    /// Command-owned artifacts.
    pub artifacts: Vec<CommandArtifact>,
    /// Optional informational timing telemetry.
    pub timings: Option<Box<CommandTimings>>,
}

impl CommandResult {
    /// Build a successful command result.
    pub fn passed(command: impl Into<String>, root: impl Into<String>) -> Self {
        Self {
            command: command.into(),
            root: root.into(),
            status: CommandStatus::Passed,
            diagnostics: Vec::new(),
            artifacts: Vec::new(),
            timings: None,
        }
    }

    /// Build a failed command result.
    pub fn failed(
        command: impl Into<String>,
        root: impl Into<String>,
        diagnostics: Vec<CommandDiagnostic>,
    ) -> Self {
        Self {
            command: command.into(),
            root: root.into(),
            status: CommandStatus::Failed,
            diagnostics,
            artifacts: Vec::new(),
            timings: None,
        }
    }

    /// Build a failed command result from a usage error.
    pub fn usage_error(
        command: impl Into<String>,
        root: impl Into<String>,
        error: &CliUsageError,
    ) -> Self {
        Self::failed(
            command,
            root,
            vec![CommandDiagnostic::from_usage_error(error)],
        )
    }

    /// Return the process exit class for this result.
    pub fn exit_code(&self) -> CommandExitCode {
        if self.status == CommandStatus::Passed {
            return CommandExitCode::Success;
        }
        self.diagnostics
            .iter()
            .map(|diagnostic| diagnostic.kind.exit_code())
            .max_by_key(|code| code.as_u8())
            .unwrap_or(CommandExitCode::UsageOrInternal)
    }

    /// Attach informational timing telemetry to the command result.
    pub fn with_timings(mut self, timings: CommandTimings) -> Self {
        self.timings = Some(Box::new(timings));
        self
    }

    /// Render deterministic JSON.
    pub fn render_json(&self) -> String {
        let mut output = String::new();
        output.push('{');
        push_json_pair(
            &mut output,
            "schema",
            &JsonValue::String(PACKAGE_COMMAND_RESULT_SCHEMA),
            true,
        );
        push_json_pair(
            &mut output,
            "command",
            &JsonValue::String(&self.command),
            false,
        );
        push_json_pair(&mut output, "root", &JsonValue::String(&self.root), false);
        push_json_pair(
            &mut output,
            "status",
            &JsonValue::String(self.status.as_str()),
            false,
        );
        output.push_str(",\"diagnostics\":");
        push_diagnostics_json(&mut output, &self.diagnostics);
        output.push_str(",\"artifacts\":");
        push_artifacts_json(&mut output, &self.artifacts);
        if let Some(timings) = &self.timings {
            output.push_str(",\"timings\":");
            push_timings_json(&mut output, timings);
        }
        output.push('}');
        output
    }

    /// Render deterministic human text from the structured result.
    pub fn render_human(&self) -> String {
        let mut lines = vec![format!("{}: {}", self.command, self.status.as_str())];
        lines.extend(self.diagnostics.iter().map(CommandDiagnostic::render_human));
        lines.join("\n")
    }
}

enum JsonValue<'a> {
    String(&'a str),
    Bool(bool),
    U128(u128),
}

fn push_json_pair(output: &mut String, key: &str, value: &JsonValue<'_>, first: bool) {
    if !first {
        output.push(',');
    }
    push_json_string(output, key);
    output.push(':');
    push_json_value(output, value);
}

fn push_json_value(output: &mut String, value: &JsonValue<'_>) {
    match value {
        JsonValue::String(value) => push_json_string(output, value),
        JsonValue::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        JsonValue::U128(value) => write!(output, "{value}").expect("write to String cannot fail"),
    }
}

fn push_diagnostics_json(output: &mut String, diagnostics: &[CommandDiagnostic]) {
    output.push('[');
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            output,
            "kind",
            &JsonValue::String(diagnostic.kind.as_str()),
            true,
        );
        push_json_pair(
            output,
            "reason_code",
            &JsonValue::String(&diagnostic.reason_code),
            false,
        );
        push_json_pair(
            output,
            "severity",
            &JsonValue::String(diagnostic.severity.as_str()),
            false,
        );
        push_optional_json_pair(output, "module", diagnostic.module.as_deref());
        push_optional_json_pair(output, "path", diagnostic.path.as_deref());
        push_optional_json_pair(output, "field", diagnostic.field.as_deref());
        push_optional_json_pair(output, "expected_hash", diagnostic.expected_hash.as_deref());
        push_optional_json_pair(output, "actual_hash", diagnostic.actual_hash.as_deref());
        push_optional_json_pair(
            output,
            "expected_value",
            diagnostic.expected_value.as_deref(),
        );
        push_optional_json_pair(output, "actual_value", diagnostic.actual_value.as_deref());
        push_optional_json_pair(output, "checker", diagnostic.checker.as_deref());
        if let Some(source) = &diagnostic.source {
            output.push_str(",\"source\":");
            push_command_diagnostic_source_json(output, source);
        }
        if let Some(conversion) = &diagnostic.conversion {
            output.push_str(",\"conversion\":");
            push_command_diagnostic_conversion_json(output, conversion);
        }
        output.push('}');
    }
    output.push(']');
}

fn push_command_diagnostic_conversion_json(
    output: &mut String,
    conversion: &CommandDiagnosticConversionContext,
) {
    output.push('{');
    push_json_pair(output, "phase", &JsonValue::String(&conversion.phase), true);
    push_json_pair(
        output,
        "outcome",
        &JsonValue::String(&conversion.outcome),
        false,
    );
    push_json_pair(
        output,
        "lhs_head",
        &JsonValue::String(&conversion.lhs_head),
        false,
    );
    push_json_pair(
        output,
        "rhs_head",
        &JsonValue::String(&conversion.rhs_head),
        false,
    );
    push_json_pair(
        output,
        "depth",
        &JsonValue::U128(u128::from(conversion.depth)),
        false,
    );
    output.push('}');
}

fn push_command_diagnostic_source_json(
    output: &mut String,
    source: &CommandDiagnosticSourceContext,
) {
    output.push('{');
    push_json_pair(output, "path", &JsonValue::String(&source.path), true);
    push_json_pair(
        output,
        "start_byte",
        &JsonValue::U128(u128::from(source.start_byte)),
        false,
    );
    push_json_pair(
        output,
        "end_byte",
        &JsonValue::U128(u128::from(source.end_byte)),
        false,
    );
    push_optional_json_pair(output, "declaration", source.declaration.as_deref());
    if let Some(line) = source.line {
        push_json_pair(output, "line", &JsonValue::U128(u128::from(line)), false);
    }
    if let Some(column) = source.column {
        push_json_pair(
            output,
            "column",
            &JsonValue::U128(u128::from(column)),
            false,
        );
    }
    push_optional_json_pair(output, "token", source.token.as_deref());
    output.push('}');
}

fn push_artifacts_json(output: &mut String, artifacts: &[CommandArtifact]) {
    output.push('[');
    for (index, artifact) in artifacts.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(output, "kind", &JsonValue::String(&artifact.kind), true);
        push_json_pair(output, "path", &JsonValue::String(&artifact.path), false);
        output.push('}');
    }
    output.push(']');
}

fn push_timings_json(output: &mut String, timings: &CommandTimings) {
    output.push('{');
    push_json_pair(
        output,
        "schema",
        &JsonValue::String(PACKAGE_TIMINGS_SCHEMA),
        true,
    );
    push_json_pair(output, "mode", &JsonValue::String(&timings.mode), false);
    push_json_pair(output, "unit", &JsonValue::String("ms"), false);
    push_json_pair(output, "proof_evidence", &JsonValue::Bool(false), false);
    push_json_pair(output, "build_evidence", &JsonValue::Bool(false), false);
    for metric in &timings.metrics {
        push_json_pair(
            output,
            &metric.field,
            &JsonValue::U128(metric.milliseconds),
            false,
        );
    }
    output.push('}');
}

fn push_optional_json_pair(output: &mut String, key: &str, value: Option<&str>) {
    if let Some(value) = value {
        output.push(',');
        push_json_string(output, key);
        output.push(':');
        push_json_string(output, value);
    }
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
    use super::{
        CommandDiagnostic, CommandDiagnosticConversionContext, CommandDiagnosticSourceContext,
        CommandResult, DiagnosticKind,
    };

    #[test]
    fn command_diagnostic_source_context_builder_preserves_supported_values() {
        assert!(CommandDiagnosticSourceContext::new("", 0, 0).is_none());
        assert!(CommandDiagnosticSourceContext::new("source.npa", 2, 1).is_none());
        let source = CommandDiagnosticSourceContext::new("source.npa", 3, 3)
            .unwrap()
            .with_declaration("")
            .with_declaration(" namespace.term ")
            .with_display_location(4, 7)
            .with_token("term");
        assert_eq!(source.path(), "source.npa");
        assert_eq!(source.start_byte(), 3);
        assert_eq!(source.end_byte(), 3);
        assert_eq!(source.declaration(), Some(" namespace.term "));
        assert_eq!(source.line(), Some(4));
        assert_eq!(source.column(), Some(7));
        assert_eq!(source.token(), Some("term"));
    }

    #[test]
    fn command_diagnostic_source_context_unit_renderers_keep_exact_order() {
        let source = CommandDiagnosticSourceContext::new("Proofs/A/source.npa", 10, 11)
            .unwrap()
            .with_declaration("A.term")
            .with_display_location(3, 5)
            .with_token("x");
        let conversion = CommandDiagnosticConversionContext::new(
            "definitional_equality",
            "not_defeq",
            "application",
            "constant:A.expected",
            7,
        )
        .unwrap();
        let diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
            .with_field("elaborator")
            .with_actual_value("failure")
            .with_source(source)
            .with_conversion(conversion);
        let result = CommandResult::failed("package build-certs", ".", vec![diagnostic]);
        assert_eq!(
            result.render_json(),
            "{\"schema\":\"npa.package.command_result.v0.3\",\"command\":\"package build-certs\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"field\":\"elaborator\",\"actual_value\":\"failure\",\"source\":{\"path\":\"Proofs/A/source.npa\",\"start_byte\":10,\"end_byte\":11,\"declaration\":\"A.term\",\"line\":3,\"column\":5,\"token\":\"x\"},\"conversion\":{\"phase\":\"definitional_equality\",\"outcome\":\"not_defeq\",\"lhs_head\":\"application\",\"rhs_head\":\"constant:A.expected\",\"depth\":7}}],\"artifacts\":[]}"
        );
        assert_eq!(
            result.render_human(),
            "package build-certs: failed\nerror Build build_failed field=elaborator source=Proofs/A/source.npa:byte[10..11] line=3 column=5 declaration=A.term token=\"x\" conversion=phase:definitional_equality,outcome:not_defeq,lhs:application,rhs:constant:A.expected,depth:7 actual=failure"
        );
    }
}
