//! Structured command diagnostics and deterministic renderers.

use std::fmt::Write as _;

use npa_api::{performance_measurement_report_json, PerformanceMeasurementReport};

use crate::args::CliUsageError;

/// Stable schema string for package command results.
pub const PACKAGE_COMMAND_RESULT_SCHEMA: &str = "npa.package.command_result.v0.5";
/// Stable schema string for bounded, untrusted kernel fuel diagnostics.
pub const KERNEL_FUEL_DIAGNOSTIC_SCHEMA: &str = "npa.kernel-fuel-diagnostic.v0.2";

const KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES: usize = 64 * 1024;
/// Stable schema string for optional package timing telemetry.
pub const PACKAGE_TIMINGS_SCHEMA_V0_1: &str = "npa.package.timings.v0.1";
/// Timing schema for commands embedding the common measurement block.
pub const PACKAGE_TIMINGS_SCHEMA_V0_2: &str = "npa.package.timings.v0.2";
/// Current integrated timing schema.
pub const PACKAGE_TIMINGS_SCHEMA: &str = PACKAGE_TIMINGS_SCHEMA_V0_2;
/// Stable schema string for interface-proposal curation checks.
pub const INTERFACE_PROPOSAL_CHECK_SCHEMA: &str = "npa.mathlib.interface_proposal_check.v1";
/// Stable schema string for the Lean interface-inventory adapter.
pub const INTERFACE_INVENTORY_SCHEMA: &str = "npa.mathlib.interface_inventory.v1";
/// Stable schema string for adopted interface-proposal surface drift.
pub const INTERFACE_PROPOSAL_SURFACE_DRIFT_SCHEMA: &str =
    "npa.mathlib.interface_proposal_surface_drift.v1";
/// Stable schema for untrusted certificate-verification selection metadata.
pub const PACKAGE_VERIFY_SELECTION_SCHEMA: &str = "npa.package.verify-selection.v0.1";

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
    /// Interface-proposal curation metadata validation.
    InterfaceProposal,
    /// Lean interface-inventory metadata validation.
    InterfaceInventory,
    /// Human source lexical-structure validation.
    SourceStructure,
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
            Self::InterfaceProposal => "InterfaceProposal",
            Self::InterfaceInventory => "InterfaceInventory",
            Self::SourceStructure => "SourceStructure",
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
            | Self::PackagePolicy
            | Self::InterfaceProposal
            | Self::InterfaceInventory
            | Self::SourceStructure => CommandExitCode::PackageFailure,
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
        "sort" | "bound_variable" | "application" | "lambda" | "pi" | "unknown"
    ) || head.strip_prefix("constant:").is_some_and(|name| {
        !name.is_empty() && name.len() <= 256 && !name.chars().any(char::is_control)
    })
}

/// Command-owned counters for the fuel-owning failed kernel operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelFuelOperationCounters {
    /// Operation fuel budget.
    pub budget: u64,
    /// Fuel consumed by the operation.
    pub spent: u64,
    /// Fuel remaining when the operation completed.
    pub remaining: u64,
    /// Whether the operation exhausted its budget.
    pub exhausted: bool,
    /// Whether any counter arithmetic overflowed.
    pub overflowed: bool,
}

/// Command-owned declaration aggregate for one kernel fuel domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelFuelDomainTotals {
    /// Number of fuel-owning operations in the domain.
    pub calls: u64,
    /// Total logical fuel consumed in the domain.
    pub logical_spent: u64,
    /// Fuel consumed by successful operations.
    pub successful_operation_fuel: u64,
    /// Fuel consumed by the exhausted operation.
    pub exhausted_operation_fuel: u64,
    /// Whether any domain counter arithmetic overflowed.
    pub overflowed: bool,
}

/// Command-owned declaration fuel totals separated by resource domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelFuelTotals {
    /// Weak-head-normal-form fuel totals.
    pub whnf: CommandKernelFuelDomainTotals,
    /// Definitional-equality conversion fuel totals.
    pub conversion: CommandKernelFuelDomainTotals,
}

/// Command-owned bounded kernel work snapshot.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelWorkSnapshot {
    /// Type-check calls.
    pub check_calls: u64,
    /// Type-inference calls.
    pub infer_calls: u64,
    /// Weak-head-normal-form calls.
    pub whnf_calls: u64,
    /// Definitional-equality calls.
    pub defeq_calls: u64,
    /// Fast syntactic-equality hits.
    pub quick_equality_hits: u64,
    /// Beta reductions.
    pub beta_steps: u64,
    /// Delta reductions.
    pub delta_steps: u64,
    /// Iota reductions.
    pub iota_steps: u64,
    /// Total physical reductions.
    pub physical_reductions: u64,
    /// Whether any work counter arithmetic overflowed.
    pub overflowed: bool,
}

/// Command-owned failed-operation fuel and work projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelOperationWork {
    /// Failed-operation fuel counters.
    pub fuel: CommandKernelFuelOperationCounters,
    /// Failed-operation work counters.
    pub work: CommandKernelWorkSnapshot,
}

/// Command-owned declaration-scope fuel and work projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelDeclarationWork {
    /// Declaration fuel totals.
    pub fuel: CommandKernelFuelTotals,
    /// Declaration work counters.
    pub work: CommandKernelWorkSnapshot,
    /// Whether any declaration counter arithmetic overflowed.
    pub overflowed: bool,
}

/// Command-owned bounded structural comparison path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelComparisonPath {
    /// Stable snake-case comparison branches.
    pub steps: Vec<String>,
    /// Whether earlier collection or output pruning omitted path steps.
    pub truncated: bool,
}

/// Command-owned retained delta-constant entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelDeltaHotsetEntry {
    /// Canonical constant name or the stable overlong-name bucket.
    pub constant: String,
    /// Observed delta-reduction count.
    pub count: u64,
}

/// Command-owned bounded retained delta-constant summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelDeltaHotsetSummary {
    /// Number of retained ordinary constant names.
    pub retained_names: u64,
    /// Maximum retained ordinary constant names.
    pub capacity: u64,
    /// Canonically ordered emitted entries.
    pub entries: Vec<CommandKernelDeltaHotsetEntry>,
    /// Number of entries emitted after output pruning.
    pub emitted: u64,
    /// Maximum entries selected before byte-size pruning.
    pub entry_limit: u64,
    /// Observations for names outside the retained set.
    pub unretained_name_observations: u64,
    /// Observations for overlong names.
    pub overlong_name_observations: u64,
    /// Whether entry selection or byte-size pruning omitted output.
    pub output_truncated: bool,
    /// Whether any hotset counter arithmetic overflowed.
    pub overflowed: bool,
}

/// Command-owned, bounded, untrusted kernel fuel diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandKernelFuelDiagnostic {
    /// Stable producer subsystem.
    pub subsystem: String,
    /// Exhausted fuel resource.
    pub resource: String,
    /// Failed-operation counters.
    pub failed_operation: CommandKernelOperationWork,
    /// Declaration-scope counters.
    pub declaration: CommandKernelDeclarationWork,
    /// Bounded structural comparison path.
    pub comparison_path: CommandKernelComparisonPath,
    /// Optional detailed retained delta-constant summary.
    pub retained_delta_constants: Option<CommandKernelDeltaHotsetSummary>,
    /// Whether any component counter arithmetic overflowed.
    pub overflowed: bool,
}

impl CommandKernelFuelDiagnostic {
    pub(crate) fn from_frontend(value: &npa_frontend::HumanKernelFuelDiagnostic) -> Self {
        Self {
            subsystem: value.subsystem.clone(),
            resource: value.resource.clone(),
            failed_operation: CommandKernelOperationWork {
                fuel: command_kernel_fuel_operation_counters(&value.failed_operation.fuel),
                work: command_kernel_work_snapshot(&value.failed_operation.work),
            },
            declaration: CommandKernelDeclarationWork {
                fuel: CommandKernelFuelTotals {
                    whnf: command_kernel_fuel_domain_totals(&value.declaration.fuel.whnf),
                    conversion: command_kernel_fuel_domain_totals(
                        &value.declaration.fuel.conversion,
                    ),
                },
                work: command_kernel_work_snapshot(&value.declaration.work),
                overflowed: value.declaration.overflowed,
            },
            comparison_path: CommandKernelComparisonPath {
                steps: value.comparison_path.steps.clone(),
                truncated: value.comparison_path.truncated,
            },
            retained_delta_constants: value.retained_delta_constants.as_ref().map(|summary| {
                CommandKernelDeltaHotsetSummary {
                    retained_names: summary.retained_names,
                    capacity: summary.capacity,
                    entries: summary
                        .entries
                        .iter()
                        .map(|entry| CommandKernelDeltaHotsetEntry {
                            constant: entry.constant.clone(),
                            count: entry.count,
                        })
                        .collect(),
                    emitted: summary.emitted,
                    entry_limit: summary.entry_limit,
                    unretained_name_observations: summary.unretained_name_observations,
                    overlong_name_observations: summary.overlong_name_observations,
                    output_truncated: summary.output_truncated,
                    overflowed: summary.overflowed,
                }
            }),
            overflowed: value.overflowed,
        }
    }

    fn render_human(&self) -> String {
        let failed = &self.failed_operation;
        let declaration = &self.declaration;
        let path = if self.comparison_path.steps.is_empty() {
            "<root>".to_owned()
        } else {
            self.comparison_path
                .steps
                .iter()
                .map(|step| step.replace('_', "."))
                .collect::<Vec<_>>()
                .join(" > ")
        };
        let mut output = format!(
            "kernel fuel:\n  subsystem: {}\n  resource: {}\n  failed operation: budget={} spent={} remaining={}\n  work: defeq_calls={} whnf_calls={} beta={} delta={} iota={}\n  declaration: conversion_spent={} whnf_spent={} physical_reductions={}\n  path: {}\n  path truncated: {}\n  overflowed: {}",
            self.subsystem,
            self.resource,
            failed.fuel.budget,
            failed.fuel.spent,
            failed.fuel.remaining,
            failed.work.defeq_calls,
            failed.work.whnf_calls,
            failed.work.beta_steps,
            failed.work.delta_steps,
            failed.work.iota_steps,
            declaration.fuel.conversion.logical_spent,
            declaration.fuel.whnf.logical_spent,
            declaration.work.physical_reductions,
            path,
            self.comparison_path.truncated,
            self.overflowed,
        );
        if let Some(summary) = &self.retained_delta_constants {
            output.push_str("\n  retained delta constants:");
            for entry in &summary.entries {
                write!(output, "\n    {}: {}", entry.constant, entry.count)
                    .expect("write to String cannot fail");
            }
            write!(
                output,
                "\n  retained names: {}/{}; emitted: {}/{}; unretained observations: {};\n    overlong observations: {}; output truncated: {}",
                summary.retained_names,
                summary.capacity,
                summary.emitted,
                summary.entry_limit,
                summary.unretained_name_observations,
                summary.overlong_name_observations,
                summary.output_truncated,
            )
            .expect("write to String cannot fail");
        }
        output
    }
}

fn command_kernel_fuel_operation_counters(
    value: &npa_frontend::HumanKernelFuelOperationCounters,
) -> CommandKernelFuelOperationCounters {
    CommandKernelFuelOperationCounters {
        budget: value.budget,
        spent: value.spent,
        remaining: value.remaining,
        exhausted: value.exhausted,
        overflowed: value.overflowed,
    }
}

fn command_kernel_fuel_domain_totals(
    value: &npa_frontend::HumanKernelFuelDomainTotals,
) -> CommandKernelFuelDomainTotals {
    CommandKernelFuelDomainTotals {
        calls: value.calls,
        logical_spent: value.logical_spent,
        successful_operation_fuel: value.successful_operation_fuel,
        exhausted_operation_fuel: value.exhausted_operation_fuel,
        overflowed: value.overflowed,
    }
}

fn command_kernel_work_snapshot(
    value: &npa_frontend::HumanKernelWorkSnapshot,
) -> CommandKernelWorkSnapshot {
    CommandKernelWorkSnapshot {
        check_calls: value.check_calls,
        infer_calls: value.infer_calls,
        whnf_calls: value.whnf_calls,
        defeq_calls: value.defeq_calls,
        quick_equality_hits: value.quick_equality_hits,
        beta_steps: value.beta_steps,
        delta_steps: value.delta_steps,
        iota_steps: value.iota_steps,
        physical_reductions: value.physical_reductions,
        overflowed: value.overflowed,
    }
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

/// Machine-readable delimiter context for a source-structure diagnostic.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandDiagnosticDelimiterContext {
    /// Stable delimiter failure classification.
    kind: String,
    /// Expected closing delimiter when one is known.
    expected_closing: Option<String>,
    /// Encountered closing delimiter, absent for an end-of-input failure.
    actual_closing: Option<String>,
    /// Exact source location of the related opening delimiter, when one exists.
    opening_source: Option<CommandDiagnosticSourceContext>,
    /// Whether a builder received an unsupported delimiter token.
    malformed: bool,
}

impl CommandDiagnosticDelimiterContext {
    /// Build delimiter context from a supported stable classification.
    pub fn new(kind: impl Into<String>) -> Option<Self> {
        let kind = kind.into();
        if !matches!(
            kind.as_str(),
            "unexpected_closing_delimiter" | "mismatched_closing_delimiter" | "unclosed_delimiter"
        ) {
            return None;
        }
        Some(Self {
            kind,
            expected_closing: None,
            actual_closing: None,
            opening_source: None,
            malformed: false,
        })
    }

    /// Attach a supported expected closing delimiter.
    #[must_use]
    pub fn with_expected_closing(mut self, expected: impl Into<String>) -> Self {
        let expected = expected.into();
        if is_human_closing_delimiter(&expected) {
            self.expected_closing = Some(expected);
        } else {
            self.malformed = true;
        }
        self
    }

    /// Attach a supported encountered closing delimiter.
    #[must_use]
    pub fn with_actual_closing(mut self, actual: impl Into<String>) -> Self {
        let actual = actual.into();
        if is_human_closing_delimiter(&actual) {
            self.actual_closing = Some(actual);
        } else {
            self.malformed = true;
        }
        self
    }

    /// Attach the related opening-delimiter source location.
    #[must_use]
    pub fn with_opening_source(mut self, opening: CommandDiagnosticSourceContext) -> Self {
        self.opening_source = Some(opening);
        self
    }

    /// Return the stable delimiter failure classification.
    pub fn kind(&self) -> &str {
        &self.kind
    }

    /// Return the expected closing delimiter.
    pub fn expected_closing(&self) -> Option<&str> {
        self.expected_closing.as_deref()
    }

    /// Return the encountered closing delimiter.
    pub fn actual_closing(&self) -> Option<&str> {
        self.actual_closing.as_deref()
    }

    /// Return the opening-delimiter source location.
    pub fn opening_source(&self) -> Option<&CommandDiagnosticSourceContext> {
        self.opening_source.as_ref()
    }

    fn is_well_formed(&self) -> bool {
        if self.malformed {
            return false;
        }
        match self.kind.as_str() {
            "unexpected_closing_delimiter" => {
                self.expected_closing.is_none()
                    && self.actual_closing.is_some()
                    && self.opening_source.is_none()
            }
            "mismatched_closing_delimiter" => self
                .expected_closing
                .as_deref()
                .zip(self.actual_closing.as_deref())
                .zip(self.opening_source.as_ref())
                .is_some_and(|((expected, actual), opening)| {
                    expected != actual && opening_matches_closing_delimiter(opening, expected)
                }),
            "unclosed_delimiter" => {
                self.actual_closing.is_none()
                    && self
                        .expected_closing
                        .as_deref()
                        .zip(self.opening_source.as_ref())
                        .is_some_and(|(expected, opening)| {
                            opening_matches_closing_delimiter(opening, expected)
                        })
            }
            _ => false,
        }
    }
}

fn is_human_closing_delimiter(value: &str) -> bool {
    matches!(value, ")" | "]" | "}")
}

fn opening_matches_closing_delimiter(
    opening: &CommandDiagnosticSourceContext,
    expected_closing: &str,
) -> bool {
    let expected_opening = match expected_closing {
        ")" => "(",
        "]" => "[",
        "}" => "{",
        _ => return false,
    };
    opening.end_byte.checked_sub(opening.start_byte) == Some(1)
        && opening.token() == Some(expected_opening)
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
    /// Structured delimiter context for source-structure failures.
    delimiter: Option<CommandDiagnosticDelimiterContext>,
    /// Bounded kernel conversion context, when available.
    pub conversion: Option<CommandDiagnosticConversionContext>,
    /// Bounded, untrusted kernel fuel diagnostic, when available.
    pub kernel_fuel: Option<CommandKernelFuelDiagnostic>,
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
            delimiter: None,
            conversion: None,
            kernel_fuel: None,
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
            delimiter: None,
            conversion: None,
            kernel_fuel: None,
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

    /// Attach coherent machine-readable delimiter context.
    ///
    /// Unsupported classifications, delimiter tokens, or field combinations
    /// are omitted from the command diagnostic.
    #[must_use]
    pub fn with_delimiter(mut self, delimiter: CommandDiagnosticDelimiterContext) -> Self {
        self.delimiter = delimiter.is_well_formed().then_some(delimiter);
        self
    }

    /// Return validated machine-readable delimiter context when available.
    pub fn delimiter(&self) -> Option<&CommandDiagnosticDelimiterContext> {
        self.delimiter.as_ref()
    }

    /// Attach bounded kernel conversion context.
    #[must_use]
    pub fn with_conversion(mut self, conversion: CommandDiagnosticConversionContext) -> Self {
        self.conversion = Some(conversion);
        self
    }

    /// Attach a bounded, untrusted kernel fuel diagnostic.
    #[must_use]
    pub fn with_kernel_fuel(mut self, kernel_fuel: CommandKernelFuelDiagnostic) -> Self {
        self.kernel_fuel = Some(kernel_fuel);
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
            delimiter: None,
            conversion: None,
            kernel_fuel: None,
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
            delimiter: None,
            conversion: None,
            kernel_fuel: None,
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
        if let Some(delimiter) = &self.delimiter {
            message.push_str(&format!(" delimiter={}", delimiter.kind));
            if let Some(expected) = &delimiter.expected_closing {
                message.push_str(&format!(" expected_closing={expected}"));
            }
            if let Some(actual) = &delimiter.actual_closing {
                message.push_str(&format!(" actual_closing={actual}"));
            }
            if let Some(opening) = &delimiter.opening_source {
                message.push_str(&format!(
                    " opening={}:byte[{}..{}]",
                    opening.path, opening.start_byte, opening.end_byte
                ));
                if let Some(line) = opening.line {
                    message.push_str(&format!(" opening_line={line}"));
                }
                if let Some(column) = opening.column {
                    message.push_str(&format!(" opening_column={column}"));
                }
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
        if let Some(kernel_fuel) = &self.kernel_fuel {
            message.push('\n');
            message.push_str(&kernel_fuel.render_human());
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
    /// Explicit schema selected by the producing command.
    pub schema: &'static str,
    /// Requested timing mode label.
    pub mode: String,
    /// Stable timing metrics in render order.
    pub metrics: Vec<CommandTimingMetric>,
    /// Common diagnostic measurement block in v0.2.
    pub measurements: Option<PerformanceMeasurementReport>,
}

/// Deterministic lifecycle-status counts for one interface-proposal snapshot.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalStatusCounts {
    /// Number of observed records.
    pub observed: usize,
    /// Number of proposed records.
    pub proposed: usize,
    /// Number of adopted records.
    pub adopted: usize,
    /// Number of withdrawn records.
    pub withdrawn: usize,
    /// Number of superseded records.
    pub superseded: usize,
}

/// One deterministic interface-proposal row in a command result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalCheckRow {
    /// Proposal-root-relative canonical path.
    pub path: String,
    /// Exact file hash rendered as `sha256:<hex>`.
    pub file_hash: String,
    /// Parsed proposal ID, or `None` when parsing failed.
    pub proposal_id: Option<String>,
    /// Parsed target module, or `None` when parsing failed.
    pub module: Option<String>,
    /// Parsed positive revision, or `None` when parsing failed.
    pub proposal_revision: Option<u64>,
    /// Parsed lifecycle status, or `None` when parsing failed.
    pub interface_status: Option<String>,
}

/// One bounded, sanitized interface-proposal diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalCheckDiagnostic {
    /// Stable lower-case diagnostic category.
    pub category: String,
    /// Stable lower-case diagnostic reason.
    pub reason: String,
    /// Sanitized proposal-relative path.
    pub path: String,
    /// Optional field name.
    pub field: Option<String>,
    /// Optional expected value.
    pub expected: Option<String>,
    /// Optional observed value.
    pub actual: Option<String>,
}

/// Deterministic snapshot summary emitted by the interface-proposal command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalCheckSnapshot {
    /// Number of discovered canonical TOML files.
    pub proposal_count: usize,
    /// Counts of successfully parsed records by lifecycle status.
    pub status_counts: InterfaceProposalStatusCounts,
    /// Ordered proposal rows.
    pub proposal_rows: Vec<InterfaceProposalCheckRow>,
    /// Complete proposal-set hash, or `None` for an incomplete scan.
    pub proposal_set_hash: Option<String>,
}

/// Exact v1 payload for `package check-interface-proposals --json`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalCheckOutput {
    /// Whether the curation result is valid.
    pub status: String,
    /// Current proposal snapshot.
    pub current: InterfaceProposalCheckSnapshot,
    /// Optional caller-supplied previous proposal snapshot.
    pub previous: Option<InterfaceProposalCheckSnapshot>,
    /// Ordered structured diagnostics.
    pub diagnostics: Vec<InterfaceProposalCheckDiagnostic>,
}

/// Caller-supplied immutable input pin for the interface-inventory adapter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceInventoryPin {
    /// Frozen ecosystem identifier.
    pub ecosystem: String,
    /// Caller-supplied repository identity.
    pub repository: String,
    /// Immutable locator kind.
    pub revision_kind: String,
    /// Caller-supplied full revision.
    pub revision: String,
    /// Caller-supplied license identifier.
    pub license: String,
    /// Optional license follow-up note.
    pub license_note: Option<String>,
    /// Explicitly non-authoritative revision binding mode.
    pub revision_binding: String,
}

/// Exact bytes/hash summary for one selected inventory input file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceInventoryInputFile {
    /// Checkout-relative source path.
    pub path: String,
    /// SHA-256 hash of exact file bytes.
    pub file_hash: String,
    /// Exact source byte count.
    pub byte_count: usize,
}

/// One normalized interface-inventory row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceInventoryRow {
    /// Normalized row family.
    pub row_kind: String,
    /// Stable deterministic row ID.
    pub id: String,
    /// Checkout-relative source path.
    pub path: String,
    /// One-based source line.
    pub line: u32,
    /// Caller-supplied repository identity.
    pub repository: String,
    /// Immutable locator kind.
    pub revision_kind: String,
    /// Caller-supplied full revision.
    pub revision: String,
    /// Caller-supplied license identifier.
    pub license: String,
    /// Normalized source module or imported module.
    pub source_module: Option<String>,
    /// Enclosing or selected source declaration.
    pub source_declaration: Option<String>,
    /// Referenced selected declaration for use rows.
    pub referenced_declaration: Option<String>,
    /// Canonical proposal usage kind.
    pub usage_kind: String,
    /// Lean declaration kind for declaration rows.
    pub declaration_kind: Option<String>,
    /// Import visibility for import rows.
    pub import_visibility: Option<String>,
    /// Bounded normalized notes.
    pub notes: String,
}

/// One bounded interface-inventory diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceInventoryDiagnostic {
    /// Stable diagnostic category.
    pub category: String,
    /// Stable lower-case reason code.
    pub reason: String,
    /// Sanitized checkout-relative path, when applicable.
    pub path: Option<String>,
    /// One-based source line, when applicable.
    pub line: Option<u32>,
    /// Input field, when applicable.
    pub field: Option<String>,
    /// Bounded expected value.
    pub expected: Option<String>,
    /// Bounded actual value.
    pub actual: Option<String>,
}

/// Exact v1 payload for `package inventory-interface --json`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceInventoryOutput {
    /// Aggregate adapter status: `ok` or `invalid`.
    pub status: String,
    /// Validated caller pin, or `None` before pin validation succeeds.
    pub pin: Option<InterfaceInventoryPin>,
    /// Selected input files and exact hashes.
    pub input_files: Vec<InterfaceInventoryInputFile>,
    /// Deterministic selected-file set hash, when files were read.
    pub source_set_hash: Option<String>,
    /// Normalized rows; empty on any invalid result.
    pub rows: Vec<InterfaceInventoryRow>,
    /// Ordered bounded diagnostics.
    pub diagnostics: Vec<InterfaceInventoryDiagnostic>,
}

/// Target artifact identity in the surface-drift result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalSurfaceTarget {
    /// Target module name.
    pub module: Option<String>,
    /// Package-relative source path.
    pub source: Option<String>,
    /// Exact source file hash.
    pub source_file_sha256: Option<String>,
    /// Package-relative certificate path.
    pub certificate: Option<String>,
    /// Exact certificate file hash.
    pub certificate_file_sha256: Option<String>,
    /// Certificate identity hash.
    pub certificate_sha256: Option<String>,
    /// Export identity hash.
    pub export_sha256: Option<String>,
}

/// Ten comparison-axis values in the frozen surface-drift contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalSurfaceComparison {
    /// Module-name comparison.
    pub module_name: String,
    /// Direct-import comparison.
    pub direct_imports: String,
    /// Declaration-order comparison.
    pub declaration_order: String,
    /// Declaration-name comparison.
    pub declaration_names: String,
    /// Declaration-kind comparison.
    pub declaration_kinds: String,
    /// Public/support surface comparison.
    pub declaration_surfaces: String,
    /// Signature comparison.
    pub signatures: String,
    /// Definition-body comparison.
    pub definition_bodies: String,
    /// Inductive-family comparison.
    pub inductive_family_members: String,
    /// Exported support-closure comparison.
    pub exported_support_closure: String,
}

/// One bounded surface-drift diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalSurfaceDiagnostic {
    /// Stable lower-case diagnostic category.
    pub category: String,
    /// Stable lower-case reason code.
    pub reason: String,
    /// Sanitized relative path, when applicable.
    pub path: Option<String>,
    /// Structured field, when applicable.
    pub field: Option<String>,
    /// Bounded expected value.
    pub expected: Option<String>,
    /// Bounded actual value.
    pub actual: Option<String>,
}

/// Exact v1 payload for the adopted interface-proposal surface-drift command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceProposalSurfaceOutput {
    /// `parity`, `drift`, or `invalid`.
    pub status: String,
    /// Proposal-root-relative selected path.
    pub proposal_path: String,
    /// Caller-attested proposal hash string.
    pub proposal_sha256: String,
    /// Target identity, with unavailable scalars represented as `None`.
    pub target: InterfaceProposalSurfaceTarget,
    /// Frozen comparison-axis result.
    pub comparison: InterfaceProposalSurfaceComparison,
    /// Ordered bounded diagnostics.
    pub diagnostics: Vec<InterfaceProposalSurfaceDiagnostic>,
}

/// Strict counts for one bounded certificate-verification selection detail list.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PackageVerifySelectionDetailCounts {
    /// Complete number of logical details before retention.
    pub attempted: u64,
    /// Number of retained details.
    pub retained: u64,
    /// Number of omitted details.
    pub omitted: u64,
}

/// Bounded, deterministic, and explicitly untrusted verification-selection metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageVerifySelectionSummary {
    /// Schema identifier; always [`PACKAGE_VERIFY_SELECTION_SCHEMA`].
    pub schema: String,
    /// Selection metadata is never trusted proof input.
    pub trusted: bool,
    /// Selection metadata is never proof evidence.
    pub proof_evidence: bool,
    /// `modules` or `base`.
    pub mode: String,
    /// `targeted` or `full_escalated`.
    pub outcome: String,
    /// Bounded user-supplied base text for committed selection.
    pub requested_base: Option<String>,
    /// Resolved base commit object ID.
    pub base_commit: Option<String>,
    /// Resolved unique merge-base object ID.
    pub merge_base: Option<String>,
    /// Resolved `HEAD` commit object ID.
    pub head_commit: Option<String>,
    /// Number of changed protected candidate paths for committed selection.
    pub changed_path_count: Option<u64>,
    /// Strict seed-module detail counts.
    pub seed_modules: PackageVerifySelectionDetailCounts,
    /// Retained canonical seed module names.
    pub seed_details: Vec<String>,
    /// SHA-256 identity of the complete canonical seed list.
    pub seed_identity: String,
    /// Number of modules in the verifier's selected import closure, when available.
    pub closure_module_count: Option<u64>,
    /// Strict full-escalation detail counts.
    pub escalation_reasons: PackageVerifySelectionDetailCounts,
    /// Retained canonical escalation details.
    pub escalation_details: Vec<String>,
    /// SHA-256 identity of the complete canonical escalation detail list.
    pub escalation_identity: String,
    /// Whether either bounded detail list omitted entries.
    pub detail_truncated: bool,
    /// Whether any count overflowed its representation.
    pub overflowed: bool,
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
    /// Optional untrusted certificate-verification selection summary.
    pub verify_selection: Option<Box<PackageVerifySelectionSummary>>,
    /// Optional command-specific interface-proposal result payload.
    pub interface_proposals: Option<Box<InterfaceProposalCheckOutput>>,
    /// Optional command-specific interface-inventory result payload.
    pub interface_inventory: Option<Box<InterfaceInventoryOutput>>,
    /// Optional command-specific surface-drift result payload.
    pub interface_proposal_surface: Option<Box<InterfaceProposalSurfaceOutput>>,
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
            verify_selection: None,
            interface_proposals: None,
            interface_inventory: None,
            interface_proposal_surface: None,
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
            verify_selection: None,
            interface_proposals: None,
            interface_inventory: None,
            interface_proposal_surface: None,
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

    /// Attach a typed, untrusted certificate-verification selection summary.
    pub fn with_verify_selection(mut self, summary: PackageVerifySelectionSummary) -> Self {
        self.verify_selection = Some(Box::new(summary));
        self
    }

    /// Attach the exact interface-proposal command result payload.
    pub fn with_interface_proposals(mut self, output: InterfaceProposalCheckOutput) -> Self {
        self.interface_proposals = Some(Box::new(output));
        self
    }

    /// Attach the exact interface-inventory command result payload.
    pub fn with_interface_inventory(mut self, output: InterfaceInventoryOutput) -> Self {
        self.interface_inventory = Some(Box::new(output));
        self
    }

    /// Attach the exact interface-proposal surface-drift result payload.
    pub fn with_interface_proposal_surface(
        mut self,
        output: InterfaceProposalSurfaceOutput,
    ) -> Self {
        self.interface_proposal_surface = Some(Box::new(output));
        self
    }

    /// Render deterministic JSON.
    pub fn render_json(&self) -> String {
        if let Some(output) = &self.interface_proposal_surface {
            return render_interface_proposal_surface_json(output);
        }
        if let Some(output) = &self.interface_inventory {
            return render_interface_inventory_json(output);
        }
        if let Some(output) = &self.interface_proposals {
            return render_interface_proposal_json(output);
        }
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
        if let Some(summary) = &self.verify_selection {
            output.push_str(",\"verify_selection\":");
            push_package_verify_selection_json(&mut output, summary);
        }
        output.push('}');
        output
    }

    /// Render deterministic human text from the structured result.
    pub fn render_human(&self) -> String {
        let mut lines = vec![format!("{}: {}", self.command, self.status.as_str())];
        lines.extend(self.diagnostics.iter().map(CommandDiagnostic::render_human));
        if let Some(summary) = &self.verify_selection {
            lines.push(format!(
                "verify selection: mode={} outcome={} seeds={} closure_modules={} changed_paths={} trusted=false proof_evidence=false",
                summary.mode,
                summary.outcome,
                summary.seed_modules.attempted,
                summary
                    .closure_module_count
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "null".to_owned()),
                summary
                    .changed_path_count
                    .map(|value| value.to_string())
                    .unwrap_or_else(|| "null".to_owned()),
            ));
        }
        if let Some(timings) = &self.timings {
            let summary = timings
                .metrics
                .iter()
                .filter(|metric| matches!(metric.field.as_str(), "total_ms" | "checker_ms"))
                .map(|metric| format!("{}={}", metric.field, metric.milliseconds))
                .collect::<Vec<_>>()
                .join(" ");
            lines.push(if summary.is_empty() {
                format!("timings: mode={}", timings.mode)
            } else {
                format!("timings: mode={} {summary}", timings.mode)
            });
            if let Some(measurements) = timings
                .measurements
                .as_ref()
                .filter(|measurements| measurements.mode.is_detailed())
            {
                let mut modules = measurements.modules.iter().collect::<Vec<_>>();
                modules.sort_by(|left, right| {
                    right
                        .checker_elapsed_ns
                        .cmp(&left.checker_elapsed_ns)
                        .then_with(|| left.module.cmp(&right.module))
                });
                lines.extend(modules.into_iter().take(5).map(|module| {
                    format!(
                        "timing module: {} checker_elapsed_ns={} scope=retained",
                        module.module, module.checker_elapsed_ns
                    )
                }));
            }
        }
        if let Some(interface_proposals) = &self.interface_proposals {
            lines.push(
                "interface-proposal boundary: network-free curation validation; not proof verification or catalog admission; no Git or network; no writes"
                    .to_owned(),
            );
            lines.push(
                "interface-proposal continuity: the caller must supply the immediately preceding validated snapshot; only locally detectable per-record continuity is checked"
                    .to_owned(),
            );
            lines.push(format!(
                "interface-proposal current: {} records set_hash={}",
                interface_proposals.current.proposal_count,
                interface_proposals
                    .current
                    .proposal_set_hash
                    .as_deref()
                    .unwrap_or("null")
            ));
        }
        if let Some(interface_inventory) = &self.interface_inventory {
            lines.push(
                "interface-inventory boundary: read-only caller-pinned curation metadata; not proof evidence or catalog admission; no Git, network, or writes"
                    .to_owned(),
            );
            lines.push(format!(
                "interface-inventory result: status={} rows={} source_set_hash={}",
                interface_inventory.status,
                interface_inventory.rows.len(),
                interface_inventory
                    .source_set_hash
                    .as_deref()
                    .unwrap_or("null")
            ));
        }
        if let Some(surface) = &self.interface_proposal_surface {
            lines.push(
                "interface-proposal-surface boundary: read-only local surface comparison; not proof evidence or catalog admission; no Git, network, or writes"
                    .to_owned(),
            );
            lines.push(format!(
                "interface-proposal-surface result: status={} proposal={} target={}",
                surface.status,
                surface.proposal_path,
                surface.target.module.as_deref().unwrap_or("null")
            ));
        }
        lines.join("\n")
    }
}

fn render_interface_proposal_json(result: &InterfaceProposalCheckOutput) -> String {
    let mut output = String::new();
    output.push('{');
    push_json_pair(
        &mut output,
        "schema",
        &JsonValue::String(INTERFACE_PROPOSAL_CHECK_SCHEMA),
        true,
    );
    push_json_pair(
        &mut output,
        "proof_evidence",
        &JsonValue::Bool(false),
        false,
    );
    push_json_pair(
        &mut output,
        "status",
        &JsonValue::String(&result.status),
        false,
    );
    output.push_str(",\"current\":");
    push_interface_proposal_snapshot_json(&mut output, &result.current);
    output.push_str(",\"previous\":");
    if let Some(previous) = &result.previous {
        push_interface_proposal_snapshot_json(&mut output, previous);
    } else {
        output.push_str("null");
    }
    output.push_str(",\"diagnostics\":");
    push_interface_proposal_diagnostics_json(&mut output, &result.diagnostics);
    output.push('}');
    output
}

fn render_interface_inventory_json(result: &InterfaceInventoryOutput) -> String {
    let mut output = String::new();
    output.push('{');
    push_json_pair(
        &mut output,
        "schema",
        &JsonValue::String(INTERFACE_INVENTORY_SCHEMA),
        true,
    );
    push_json_pair(
        &mut output,
        "proof_evidence",
        &JsonValue::Bool(false),
        false,
    );
    push_json_pair(
        &mut output,
        "status",
        &JsonValue::String(&result.status),
        false,
    );
    output.push_str(",\"pin\":");
    if let Some(pin) = &result.pin {
        output.push('{');
        push_json_pair(
            &mut output,
            "ecosystem",
            &JsonValue::String(&pin.ecosystem),
            true,
        );
        push_json_pair(
            &mut output,
            "repository",
            &JsonValue::String(&pin.repository),
            false,
        );
        push_json_pair(
            &mut output,
            "revision_kind",
            &JsonValue::String(&pin.revision_kind),
            false,
        );
        push_json_pair(
            &mut output,
            "revision",
            &JsonValue::String(&pin.revision),
            false,
        );
        push_json_pair(
            &mut output,
            "license",
            &JsonValue::String(&pin.license),
            false,
        );
        push_nullable_json_pair(&mut output, "license_note", pin.license_note.as_deref());
        push_json_pair(
            &mut output,
            "revision_binding",
            &JsonValue::String(&pin.revision_binding),
            false,
        );
        output.push('}');
    } else {
        output.push_str("null");
    }
    output.push_str(",\"input_files\":[");
    for (index, file) in result.input_files.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(&mut output, "path", &JsonValue::String(&file.path), true);
        push_json_pair(
            &mut output,
            "file_hash",
            &JsonValue::String(&file.file_hash),
            false,
        );
        output.push_str(",\"byte_count\":");
        write!(output, "{}", file.byte_count).expect("write to String cannot fail");
        output.push('}');
    }
    output.push(']');
    output.push_str(",\"source_set_hash\":");
    if let Some(hash) = &result.source_set_hash {
        push_json_string(&mut output, hash);
    } else {
        output.push_str("null");
    }
    output.push_str(",\"rows\":[");
    for (index, row) in result.rows.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            &mut output,
            "row_kind",
            &JsonValue::String(&row.row_kind),
            true,
        );
        push_json_pair(&mut output, "id", &JsonValue::String(&row.id), false);
        push_json_pair(&mut output, "path", &JsonValue::String(&row.path), false);
        output.push_str(",\"line\":");
        write!(output, "{}", row.line).expect("write to String cannot fail");
        push_json_pair(
            &mut output,
            "repository",
            &JsonValue::String(&row.repository),
            false,
        );
        push_json_pair(
            &mut output,
            "revision_kind",
            &JsonValue::String(&row.revision_kind),
            false,
        );
        push_json_pair(
            &mut output,
            "revision",
            &JsonValue::String(&row.revision),
            false,
        );
        push_json_pair(
            &mut output,
            "license",
            &JsonValue::String(&row.license),
            false,
        );
        push_nullable_json_pair(&mut output, "source_module", row.source_module.as_deref());
        push_nullable_json_pair(
            &mut output,
            "source_declaration",
            row.source_declaration.as_deref(),
        );
        push_nullable_json_pair(
            &mut output,
            "referenced_declaration",
            row.referenced_declaration.as_deref(),
        );
        push_json_pair(
            &mut output,
            "usage_kind",
            &JsonValue::String(&row.usage_kind),
            false,
        );
        push_nullable_json_pair(
            &mut output,
            "declaration_kind",
            row.declaration_kind.as_deref(),
        );
        push_nullable_json_pair(
            &mut output,
            "import_visibility",
            row.import_visibility.as_deref(),
        );
        push_json_pair(&mut output, "notes", &JsonValue::String(&row.notes), false);
        output.push('}');
    }
    output.push(']');
    output.push_str(",\"diagnostics\":");
    push_interface_inventory_diagnostics_json(&mut output, &result.diagnostics);
    output.push('}');
    output
}

fn render_interface_proposal_surface_json(result: &InterfaceProposalSurfaceOutput) -> String {
    let mut output = String::new();
    output.push('{');
    push_json_pair(
        &mut output,
        "schema",
        &JsonValue::String(INTERFACE_PROPOSAL_SURFACE_DRIFT_SCHEMA),
        true,
    );
    push_json_pair(
        &mut output,
        "proof_evidence",
        &JsonValue::Bool(false),
        false,
    );
    push_json_pair(
        &mut output,
        "status",
        &JsonValue::String(&result.status),
        false,
    );
    push_json_pair(
        &mut output,
        "proposal_path",
        &JsonValue::String(&result.proposal_path),
        false,
    );
    push_json_pair(
        &mut output,
        "proposal_sha256",
        &JsonValue::String(&result.proposal_sha256),
        false,
    );
    output.push_str(",\"target\":{");
    push_nullable_json_pair_first(&mut output, "module", result.target.module.as_deref());
    push_nullable_json_pair(&mut output, "source", result.target.source.as_deref());
    push_nullable_json_pair(
        &mut output,
        "source_file_sha256",
        result.target.source_file_sha256.as_deref(),
    );
    push_nullable_json_pair(
        &mut output,
        "certificate",
        result.target.certificate.as_deref(),
    );
    push_nullable_json_pair(
        &mut output,
        "certificate_file_sha256",
        result.target.certificate_file_sha256.as_deref(),
    );
    push_nullable_json_pair(
        &mut output,
        "certificate_sha256",
        result.target.certificate_sha256.as_deref(),
    );
    push_nullable_json_pair(
        &mut output,
        "export_sha256",
        result.target.export_sha256.as_deref(),
    );
    output.push('}');
    output.push_str(",\"comparison\":{");
    push_json_pair(
        &mut output,
        "module_name",
        &JsonValue::String(&result.comparison.module_name),
        true,
    );
    push_json_pair(
        &mut output,
        "direct_imports",
        &JsonValue::String(&result.comparison.direct_imports),
        false,
    );
    push_json_pair(
        &mut output,
        "declaration_order",
        &JsonValue::String(&result.comparison.declaration_order),
        false,
    );
    push_json_pair(
        &mut output,
        "declaration_names",
        &JsonValue::String(&result.comparison.declaration_names),
        false,
    );
    push_json_pair(
        &mut output,
        "declaration_kinds",
        &JsonValue::String(&result.comparison.declaration_kinds),
        false,
    );
    push_json_pair(
        &mut output,
        "declaration_surfaces",
        &JsonValue::String(&result.comparison.declaration_surfaces),
        false,
    );
    push_json_pair(
        &mut output,
        "signatures",
        &JsonValue::String(&result.comparison.signatures),
        false,
    );
    push_json_pair(
        &mut output,
        "definition_bodies",
        &JsonValue::String(&result.comparison.definition_bodies),
        false,
    );
    push_json_pair(
        &mut output,
        "inductive_family_members",
        &JsonValue::String(&result.comparison.inductive_family_members),
        false,
    );
    push_json_pair(
        &mut output,
        "exported_support_closure",
        &JsonValue::String(&result.comparison.exported_support_closure),
        false,
    );
    output.push('}');
    output.push_str(",\"diagnostics\":");
    output.push('[');
    for (index, diagnostic) in result.diagnostics.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            &mut output,
            "category",
            &JsonValue::String(&diagnostic.category),
            true,
        );
        push_json_pair(
            &mut output,
            "reason",
            &JsonValue::String(&diagnostic.reason),
            false,
        );
        push_nullable_json_pair(&mut output, "path", diagnostic.path.as_deref());
        push_nullable_json_pair(&mut output, "field", diagnostic.field.as_deref());
        push_nullable_json_pair(&mut output, "expected", diagnostic.expected.as_deref());
        push_nullable_json_pair(&mut output, "actual", diagnostic.actual.as_deref());
        output.push('}');
    }
    output.push(']');
    output.push('}');
    output
}

fn push_interface_inventory_diagnostics_json(
    output: &mut String,
    diagnostics: &[InterfaceInventoryDiagnostic],
) {
    output.push('[');
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            output,
            "category",
            &JsonValue::String(&diagnostic.category),
            true,
        );
        push_json_pair(
            output,
            "reason",
            &JsonValue::String(&diagnostic.reason),
            false,
        );
        push_nullable_json_pair(output, "path", diagnostic.path.as_deref());
        push_nullable_json_number(output, "line", diagnostic.line);
        push_nullable_json_pair(output, "field", diagnostic.field.as_deref());
        push_nullable_json_pair(output, "expected", diagnostic.expected.as_deref());
        push_nullable_json_pair(output, "actual", diagnostic.actual.as_deref());
        output.push('}');
    }
    output.push(']');
}

fn push_nullable_json_number(output: &mut String, key: &str, value: Option<u32>) {
    output.push(',');
    push_json_string(output, key);
    output.push(':');
    if let Some(value) = value {
        write!(output, "{value}").expect("write to String cannot fail");
    } else {
        output.push_str("null");
    }
}

fn push_interface_proposal_snapshot_json(
    output: &mut String,
    snapshot: &InterfaceProposalCheckSnapshot,
) {
    output.push('{');
    push_json_pair(
        output,
        "proposal_count",
        &JsonValue::U128(snapshot.proposal_count as u128),
        true,
    );
    output.push_str(",\"status_counts\":{");
    push_json_pair(
        output,
        "observed",
        &JsonValue::U128(snapshot.status_counts.observed as u128),
        true,
    );
    push_json_pair(
        output,
        "proposed",
        &JsonValue::U128(snapshot.status_counts.proposed as u128),
        false,
    );
    push_json_pair(
        output,
        "adopted",
        &JsonValue::U128(snapshot.status_counts.adopted as u128),
        false,
    );
    push_json_pair(
        output,
        "withdrawn",
        &JsonValue::U128(snapshot.status_counts.withdrawn as u128),
        false,
    );
    push_json_pair(
        output,
        "superseded",
        &JsonValue::U128(snapshot.status_counts.superseded as u128),
        false,
    );
    output.push('}');
    output.push_str(",\"proposal_rows\":[");
    for (index, row) in snapshot.proposal_rows.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(output, "path", &JsonValue::String(&row.path), true);
        push_json_pair(
            output,
            "file_hash",
            &JsonValue::String(&row.file_hash),
            false,
        );
        push_nullable_json_pair(output, "proposal_id", row.proposal_id.as_deref());
        push_nullable_json_pair(output, "module", row.module.as_deref());
        output.push_str(",\"proposal_revision\":");
        if let Some(revision) = row.proposal_revision {
            write!(output, "{revision}").expect("write to String cannot fail");
        } else {
            output.push_str("null");
        }
        push_nullable_json_pair(output, "interface_status", row.interface_status.as_deref());
        output.push('}');
    }
    output.push(']');
    output.push_str(",\"proposal_set_hash\":");
    if let Some(hash) = &snapshot.proposal_set_hash {
        push_json_string(output, hash);
    } else {
        output.push_str("null");
    }
    output.push('}');
}

fn push_interface_proposal_diagnostics_json(
    output: &mut String,
    diagnostics: &[InterfaceProposalCheckDiagnostic],
) {
    output.push('[');
    for (index, diagnostic) in diagnostics.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            output,
            "category",
            &JsonValue::String(&diagnostic.category),
            true,
        );
        push_json_pair(
            output,
            "reason",
            &JsonValue::String(&diagnostic.reason),
            false,
        );
        push_json_pair(output, "path", &JsonValue::String(&diagnostic.path), false);
        push_nullable_json_pair(output, "field", diagnostic.field.as_deref());
        push_nullable_json_pair(output, "expected", diagnostic.expected.as_deref());
        push_nullable_json_pair(output, "actual", diagnostic.actual.as_deref());
        output.push('}');
    }
    output.push(']');
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

fn push_package_verify_selection_json(
    output: &mut String,
    summary: &PackageVerifySelectionSummary,
) {
    output.push('{');
    push_json_pair(output, "schema", &JsonValue::String(&summary.schema), true);
    push_json_pair(output, "trusted", &JsonValue::Bool(summary.trusted), false);
    push_json_pair(
        output,
        "proof_evidence",
        &JsonValue::Bool(summary.proof_evidence),
        false,
    );
    push_json_pair(output, "mode", &JsonValue::String(&summary.mode), false);
    push_json_pair(
        output,
        "outcome",
        &JsonValue::String(&summary.outcome),
        false,
    );
    push_nullable_json_pair(output, "requested_base", summary.requested_base.as_deref());
    push_nullable_json_pair(output, "base_commit", summary.base_commit.as_deref());
    push_nullable_json_pair(output, "merge_base", summary.merge_base.as_deref());
    push_nullable_json_pair(output, "head_commit", summary.head_commit.as_deref());
    output.push_str(",\"changed_path_count\":");
    push_optional_u64_json(output, summary.changed_path_count);
    output.push_str(",\"seed_modules\":");
    push_package_verify_detail_counts_json(output, summary.seed_modules);
    output.push_str(",\"seed_details\":");
    push_string_list_json(output, &summary.seed_details);
    push_json_pair(
        output,
        "seed_identity",
        &JsonValue::String(&summary.seed_identity),
        false,
    );
    output.push_str(",\"closure_module_count\":");
    push_optional_u64_json(output, summary.closure_module_count);
    output.push_str(",\"escalation_reasons\":");
    push_package_verify_detail_counts_json(output, summary.escalation_reasons);
    output.push_str(",\"escalation_details\":");
    push_string_list_json(output, &summary.escalation_details);
    push_json_pair(
        output,
        "escalation_identity",
        &JsonValue::String(&summary.escalation_identity),
        false,
    );
    push_json_pair(
        output,
        "detail_truncated",
        &JsonValue::Bool(summary.detail_truncated),
        false,
    );
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(summary.overflowed),
        false,
    );
    output.push('}');
}

fn push_package_verify_detail_counts_json(
    output: &mut String,
    counts: PackageVerifySelectionDetailCounts,
) {
    output.push('{');
    push_json_pair(
        output,
        "attempted",
        &JsonValue::U128(u128::from(counts.attempted)),
        true,
    );
    push_json_pair(
        output,
        "retained",
        &JsonValue::U128(u128::from(counts.retained)),
        false,
    );
    push_json_pair(
        output,
        "omitted",
        &JsonValue::U128(u128::from(counts.omitted)),
        false,
    );
    output.push('}');
}

fn push_string_list_json(output: &mut String, values: &[String]) {
    output.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        push_json_string(output, value);
    }
    output.push(']');
}

fn push_optional_u64_json(output: &mut String, value: Option<u64>) {
    if let Some(value) = value {
        write!(output, "{value}").expect("write to String cannot fail");
    } else {
        output.push_str("null");
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
        if let Some(delimiter) = &diagnostic.delimiter {
            output.push_str(",\"delimiter\":");
            push_command_diagnostic_delimiter_json(output, delimiter);
        }
        if let Some(conversion) = &diagnostic.conversion {
            output.push_str(",\"conversion\":");
            push_command_diagnostic_conversion_json(output, conversion);
        }
        if let Some(kernel_fuel) = &diagnostic.kernel_fuel {
            output.push_str(",\"kernel_fuel\":");
            output.push_str(&command_kernel_fuel_json(kernel_fuel));
        }
        output.push('}');
    }
    output.push(']');
}

fn push_command_diagnostic_delimiter_json(
    output: &mut String,
    delimiter: &CommandDiagnosticDelimiterContext,
) {
    output.push('{');
    push_json_pair(output, "kind", &JsonValue::String(&delimiter.kind), true);
    push_nullable_json_pair(
        output,
        "expected_closing",
        delimiter.expected_closing.as_deref(),
    );
    push_nullable_json_pair(
        output,
        "actual_closing",
        delimiter.actual_closing.as_deref(),
    );
    if let Some(opening) = &delimiter.opening_source {
        output.push_str(",\"opening_source\":");
        push_command_diagnostic_source_json(output, opening);
    } else {
        output.push_str(",\"opening_source\":null");
    }
    output.push('}');
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

fn command_kernel_fuel_json(diagnostic: &CommandKernelFuelDiagnostic) -> String {
    command_kernel_fuel_json_with_limit(diagnostic, KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES)
}

fn command_kernel_fuel_json_with_limit(
    diagnostic: &CommandKernelFuelDiagnostic,
    limit: usize,
) -> String {
    let mut bounded = diagnostic.clone();
    loop {
        let mut output = String::new();
        push_command_kernel_fuel_json(&mut output, &bounded);
        if output.len() <= limit {
            return output;
        }
        if let Some(summary) = bounded.retained_delta_constants.as_mut() {
            if summary.entries.pop().is_some() {
                summary.emitted = u64::try_from(summary.entries.len()).unwrap_or(u64::MAX);
                summary.output_truncated = true;
                continue;
            }
        }
        if bounded.comparison_path.steps.len() > 2 {
            let middle = bounded.comparison_path.steps.len() / 2;
            bounded.comparison_path.steps.remove(middle);
            bounded.comparison_path.truncated = true;
            continue;
        }
        if !bounded.comparison_path.steps.is_empty() {
            bounded.comparison_path.steps.clear();
            bounded.comparison_path.truncated = true;
            continue;
        }
        if !bounded.subsystem.is_empty() {
            bounded.subsystem.clear();
            continue;
        }
        if !bounded.resource.is_empty() {
            bounded.resource.clear();
            continue;
        }

        // Production uses a 64-KiB limit, which always admits the fixed
        // scalar-only payload. Keep this helper total for smaller test-only
        // limits as well: returning the irreducible JSON is safer than
        // panicking in a serializer.
        return output;
    }
}

fn push_command_kernel_fuel_json(output: &mut String, diagnostic: &CommandKernelFuelDiagnostic) {
    output.push('{');
    push_json_pair(
        output,
        "schema",
        &JsonValue::String(KERNEL_FUEL_DIAGNOSTIC_SCHEMA),
        true,
    );
    push_json_pair(output, "trusted", &JsonValue::Bool(false), false);
    push_json_pair(output, "proof_evidence", &JsonValue::Bool(false), false);
    push_json_pair(
        output,
        "subsystem",
        &JsonValue::String(&diagnostic.subsystem),
        false,
    );
    push_json_pair(
        output,
        "resource",
        &JsonValue::String(&diagnostic.resource),
        false,
    );
    output.push_str(",\"failed_operation\":{");
    output.push_str("\"fuel\":");
    push_command_kernel_operation_fuel_json(output, &diagnostic.failed_operation.fuel);
    output.push_str(",\"work\":");
    push_command_kernel_work_json(output, &diagnostic.failed_operation.work);
    output.push('}');
    output.push_str(",\"declaration\":{");
    output.push_str("\"fuel\":{");
    output.push_str("\"whnf\":");
    push_command_kernel_domain_fuel_json(output, &diagnostic.declaration.fuel.whnf);
    output.push_str(",\"conversion\":");
    push_command_kernel_domain_fuel_json(output, &diagnostic.declaration.fuel.conversion);
    output.push('}');
    output.push_str(",\"work\":");
    push_command_kernel_work_json(output, &diagnostic.declaration.work);
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(diagnostic.declaration.overflowed),
        false,
    );
    output.push('}');
    output.push_str(",\"comparison_path\":{");
    output.push_str("\"steps\":[");
    for (index, step) in diagnostic.comparison_path.steps.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        push_json_string(output, step);
    }
    output.push(']');
    push_json_pair(
        output,
        "truncated",
        &JsonValue::Bool(diagnostic.comparison_path.truncated),
        false,
    );
    output.push('}');
    output.push_str(",\"retained_delta_constants\":");
    if let Some(summary) = &diagnostic.retained_delta_constants {
        push_command_kernel_hotset_json(output, summary);
    } else {
        output.push_str("null");
    }
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(diagnostic.overflowed),
        false,
    );
    output.push('}');
}

fn push_command_kernel_operation_fuel_json(
    output: &mut String,
    fuel: &CommandKernelFuelOperationCounters,
) {
    output.push('{');
    push_json_pair(
        output,
        "budget",
        &JsonValue::U128(u128::from(fuel.budget)),
        true,
    );
    push_json_pair(
        output,
        "spent",
        &JsonValue::U128(u128::from(fuel.spent)),
        false,
    );
    push_json_pair(
        output,
        "remaining",
        &JsonValue::U128(u128::from(fuel.remaining)),
        false,
    );
    push_json_pair(output, "exhausted", &JsonValue::Bool(fuel.exhausted), false);
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(fuel.overflowed),
        false,
    );
    output.push('}');
}

fn push_command_kernel_domain_fuel_json(output: &mut String, fuel: &CommandKernelFuelDomainTotals) {
    output.push('{');
    push_json_pair(
        output,
        "calls",
        &JsonValue::U128(u128::from(fuel.calls)),
        true,
    );
    push_json_pair(
        output,
        "logical_spent",
        &JsonValue::U128(u128::from(fuel.logical_spent)),
        false,
    );
    push_json_pair(
        output,
        "successful_operation_fuel",
        &JsonValue::U128(u128::from(fuel.successful_operation_fuel)),
        false,
    );
    push_json_pair(
        output,
        "exhausted_operation_fuel",
        &JsonValue::U128(u128::from(fuel.exhausted_operation_fuel)),
        false,
    );
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(fuel.overflowed),
        false,
    );
    output.push('}');
}

fn push_command_kernel_work_json(output: &mut String, work: &CommandKernelWorkSnapshot) {
    output.push('{');
    push_json_pair(
        output,
        "check_calls",
        &JsonValue::U128(u128::from(work.check_calls)),
        true,
    );
    push_json_pair(
        output,
        "infer_calls",
        &JsonValue::U128(u128::from(work.infer_calls)),
        false,
    );
    push_json_pair(
        output,
        "whnf_calls",
        &JsonValue::U128(u128::from(work.whnf_calls)),
        false,
    );
    push_json_pair(
        output,
        "defeq_calls",
        &JsonValue::U128(u128::from(work.defeq_calls)),
        false,
    );
    push_json_pair(
        output,
        "quick_equality_hits",
        &JsonValue::U128(u128::from(work.quick_equality_hits)),
        false,
    );
    push_json_pair(
        output,
        "beta_steps",
        &JsonValue::U128(u128::from(work.beta_steps)),
        false,
    );
    push_json_pair(
        output,
        "delta_steps",
        &JsonValue::U128(u128::from(work.delta_steps)),
        false,
    );
    push_json_pair(
        output,
        "iota_steps",
        &JsonValue::U128(u128::from(work.iota_steps)),
        false,
    );
    push_json_pair(
        output,
        "physical_reductions",
        &JsonValue::U128(u128::from(work.physical_reductions)),
        false,
    );
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(work.overflowed),
        false,
    );
    output.push('}');
}

fn push_command_kernel_hotset_json(output: &mut String, summary: &CommandKernelDeltaHotsetSummary) {
    output.push('{');
    push_json_pair(
        output,
        "retained_names",
        &JsonValue::U128(u128::from(summary.retained_names)),
        true,
    );
    push_json_pair(
        output,
        "capacity",
        &JsonValue::U128(u128::from(summary.capacity)),
        false,
    );
    output.push_str(",\"entries\":[");
    for (index, entry) in summary.entries.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        output.push('{');
        push_json_pair(
            output,
            "constant",
            &JsonValue::String(&entry.constant),
            true,
        );
        push_json_pair(
            output,
            "count",
            &JsonValue::U128(u128::from(entry.count)),
            false,
        );
        output.push('}');
    }
    output.push(']');
    push_json_pair(
        output,
        "emitted",
        &JsonValue::U128(u128::from(summary.emitted)),
        false,
    );
    push_json_pair(
        output,
        "entry_limit",
        &JsonValue::U128(u128::from(summary.entry_limit)),
        false,
    );
    push_json_pair(
        output,
        "unretained_name_observations",
        &JsonValue::U128(u128::from(summary.unretained_name_observations)),
        false,
    );
    push_json_pair(
        output,
        "overlong_name_observations",
        &JsonValue::U128(u128::from(summary.overlong_name_observations)),
        false,
    );
    push_json_pair(
        output,
        "output_truncated",
        &JsonValue::Bool(summary.output_truncated),
        false,
    );
    push_json_pair(
        output,
        "overflowed",
        &JsonValue::Bool(summary.overflowed),
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
    push_json_pair(output, "schema", &JsonValue::String(timings.schema), true);
    push_json_pair(output, "mode", &JsonValue::String(&timings.mode), false);
    push_json_pair(output, "unit", &JsonValue::String("ms"), false);
    push_json_pair(output, "proof_evidence", &JsonValue::Bool(false), false);
    push_json_pair(output, "build_evidence", &JsonValue::Bool(false), false);
    if timings.schema == PACKAGE_TIMINGS_SCHEMA_V0_2 {
        push_json_pair(output, "trusted", &JsonValue::Bool(false), false);
    }
    for metric in &timings.metrics {
        push_json_pair(
            output,
            &metric.field,
            &JsonValue::U128(metric.milliseconds),
            false,
        );
    }
    if let Some(measurements) = &timings.measurements {
        output.push_str(",\"measurements\":");
        output.push_str(&performance_measurement_report_json(measurements));
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

fn push_nullable_json_pair(output: &mut String, key: &str, value: Option<&str>) {
    output.push(',');
    push_json_string(output, key);
    output.push(':');
    if let Some(value) = value {
        push_json_string(output, value);
    } else {
        output.push_str("null");
    }
}

fn push_nullable_json_pair_first(output: &mut String, key: &str, value: Option<&str>) {
    push_json_string(output, key);
    output.push(':');
    if let Some(value) = value {
        push_json_string(output, value);
    } else {
        output.push_str("null");
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
        command_kernel_fuel_json, command_kernel_fuel_json_with_limit,
        push_command_kernel_fuel_json, CommandDiagnostic, CommandDiagnosticConversionContext,
        CommandDiagnosticDelimiterContext, CommandDiagnosticSourceContext,
        CommandKernelComparisonPath, CommandKernelDeclarationWork, CommandKernelDeltaHotsetEntry,
        CommandKernelDeltaHotsetSummary, CommandKernelFuelDiagnostic,
        CommandKernelFuelDomainTotals, CommandKernelFuelOperationCounters, CommandKernelFuelTotals,
        CommandKernelOperationWork, CommandKernelWorkSnapshot, CommandResult, CommandTimingMetric,
        CommandTimings, DiagnosticKind, PackageVerifySelectionDetailCounts,
        PackageVerifySelectionSummary, KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES,
        PACKAGE_TIMINGS_SCHEMA_V0_2, PACKAGE_VERIFY_SELECTION_SCHEMA,
    };
    use npa_api::{
        PerformanceMeasurementMode, PerformanceMeasurementRecorder, PerformanceModuleMeasurement,
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
    fn command_diagnostic_delimiter_context_rejects_unbounded_or_incoherent_values() {
        assert!(CommandDiagnosticDelimiterContext::new("other\nkind").is_none());

        let opening = CommandDiagnosticSourceContext::new("source.npa", 2, 3)
            .unwrap()
            .with_token("[");
        let valid = CommandDiagnosticDelimiterContext::new("mismatched_closing_delimiter")
            .unwrap()
            .with_expected_closing("]")
            .with_actual_closing(")")
            .with_opening_source(opening.clone());
        let diagnostic = CommandDiagnostic::error(
            DiagnosticKind::SourceStructure,
            "mismatched_closing_delimiter",
        )
        .with_delimiter(valid);
        assert!(diagnostic.delimiter().is_some());
        let result = CommandResult::failed("package check-source-structure", ".", vec![diagnostic]);
        assert_eq!(
            result.render_json(),
            "{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package check-source-structure\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{\"kind\":\"SourceStructure\",\"reason_code\":\"mismatched_closing_delimiter\",\"severity\":\"error\",\"delimiter\":{\"kind\":\"mismatched_closing_delimiter\",\"expected_closing\":\"]\",\"actual_closing\":\")\",\"opening_source\":{\"path\":\"source.npa\",\"start_byte\":2,\"end_byte\":3,\"token\":\"[\"}}}],\"artifacts\":[]}"
        );
        assert_eq!(
            result.render_human(),
            "package check-source-structure: failed\nerror SourceStructure mismatched_closing_delimiter delimiter=mismatched_closing_delimiter expected_closing=] actual_closing=) opening=source.npa:byte[2..3]"
        );

        let wrong_opening = CommandDiagnosticDelimiterContext::new("unclosed_delimiter")
            .unwrap()
            .with_expected_closing(")")
            .with_opening_source(opening);
        let diagnostic = CommandDiagnostic::error(DiagnosticKind::SourceStructure, "unclosed")
            .with_delimiter(wrong_opening);
        assert!(diagnostic.delimiter().is_none());

        let exact_paren = CommandDiagnosticSourceContext::new("source.npa", 4, 5)
            .unwrap()
            .with_token("(");
        for malformed in [
            CommandDiagnosticDelimiterContext::new("unclosed_delimiter")
                .unwrap()
                .with_expected_closing(")")
                .with_actual_closing("invalid\ncloser")
                .with_opening_source(exact_paren),
            CommandDiagnosticDelimiterContext::new("unexpected_closing_delimiter")
                .unwrap()
                .with_expected_closing("not-a-delimiter")
                .with_actual_closing(")"),
        ] {
            let diagnostic = CommandDiagnostic::error(
                DiagnosticKind::SourceStructure,
                "malformed_delimiter_context",
            )
            .with_delimiter(malformed);
            assert!(
                diagnostic.delimiter().is_none(),
                "unsupported delimiter tokens must fail closed"
            );
        }

        let valid = CommandDiagnosticDelimiterContext::new("unexpected_closing_delimiter")
            .unwrap()
            .with_actual_closing(")");
        let malformed = CommandDiagnosticDelimiterContext::new("unexpected_closing_delimiter")
            .unwrap()
            .with_actual_closing("invalid");
        let diagnostic = CommandDiagnostic::error(
            DiagnosticKind::SourceStructure,
            "unexpected_closing_delimiter",
        )
        .with_delimiter(valid)
        .with_delimiter(malformed);
        assert!(
            diagnostic.delimiter().is_none(),
            "an invalid replacement must clear previously attached delimiter context"
        );

        for incomplete_opening in [
            CommandDiagnosticSourceContext::new("source.npa", 2, 3).unwrap(),
            CommandDiagnosticSourceContext::new("source.npa", 2, 4)
                .unwrap()
                .with_token("["),
        ] {
            let context = CommandDiagnosticDelimiterContext::new("unclosed_delimiter")
                .unwrap()
                .with_expected_closing("]")
                .with_opening_source(incomplete_opening);
            let diagnostic =
                CommandDiagnostic::error(DiagnosticKind::SourceStructure, "unclosed_delimiter")
                    .with_delimiter(context);
            assert!(
                diagnostic.delimiter().is_none(),
                "an opener must expose the exact one-byte delimiter token"
            );
        }
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
            "{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"field\":\"elaborator\",\"actual_value\":\"failure\",\"source\":{\"path\":\"Proofs/A/source.npa\",\"start_byte\":10,\"end_byte\":11,\"declaration\":\"A.term\",\"line\":3,\"column\":5,\"token\":\"x\"},\"conversion\":{\"phase\":\"definitional_equality\",\"outcome\":\"not_defeq\",\"lhs_head\":\"application\",\"rhs_head\":\"constant:A.expected\",\"depth\":7}}],\"artifacts\":[]}"
        );
        assert_eq!(
            result.render_human(),
            "package build-certs: failed\nerror Build build_failed field=elaborator source=Proofs/A/source.npa:byte[10..11] line=3 column=5 declaration=A.term token=\"x\" conversion=phase:definitional_equality,outcome:not_defeq,lhs:application,rhs:constant:A.expected,depth:7 actual=failure"
        );
    }

    #[test]
    fn command_diagnostic_conversion_context_rejects_retired_let_heads() {
        assert!(CommandDiagnosticConversionContext::new(
            "definitional_equality",
            "not_defeq",
            "let",
            "unknown",
            0,
        )
        .is_none());
        assert!(CommandDiagnosticConversionContext::new(
            "definitional_equality",
            "not_defeq",
            "unknown",
            "let",
            0,
        )
        .is_none());
    }

    #[test]
    fn command_diagnostic_conversion_fuel_renderers_are_byte_exact() {
        let fuel = conversion_fuel_fixture(None);
        let conversion = CommandDiagnosticConversionContext::new(
            "definitional_equality",
            "fuel_exhausted",
            "application",
            "constant:A.expected",
            7,
        )
        .unwrap();
        let diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
            .with_field("kernel_handoff")
            .with_conversion(conversion)
            .with_kernel_fuel(fuel);
        let result = CommandResult::failed("package build-certs", ".", vec![diagnostic]);
        assert_eq!(
            result.render_json(),
            format!(
                "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"field\":\"kernel_handoff\",\"conversion\":{{\"phase\":\"definitional_equality\",\"outcome\":\"fuel_exhausted\",\"lhs_head\":\"application\",\"rhs_head\":\"constant:A.expected\",\"depth\":7}},\"kernel_fuel\":{}}}],\"artifacts\":[]}}",
                expected_conversion_fuel_json("null")
            )
        );
        assert_eq!(
            result.render_human(),
            "package build-certs: failed\nerror Build build_failed field=kernel_handoff conversion=phase:definitional_equality,outcome:fuel_exhausted,lhs:application,rhs:constant:A.expected,depth:7\nkernel fuel:\n  subsystem: fast_kernel\n  resource: conversion\n  failed operation: budget=5000000 spent=5000000 remaining=0\n  work: defeq_calls=4187 whnf_calls=9120 beta=64 delta=4821031 iota=0\n  declaration: conversion_spent=5000218 whnf_spent=18342 physical_reductions=4821164\n  path: app.argument > pi.body > whnf.left > app.function\n  path truncated: false\n  overflowed: false"
        );
    }

    #[test]
    fn rollout_exhaustion_fixture_json_is_same_mode_repeatable_and_mode_neutral() {
        let detailed_hotset = CommandKernelDeltaHotsetSummary {
            retained_names: 2,
            capacity: 256,
            entries: vec![
                CommandKernelDeltaHotsetEntry {
                    constant: "Observed.AliasArg".to_owned(),
                    count: 2,
                },
                CommandKernelDeltaHotsetEntry {
                    constant: "Observed.AliasExpected2".to_owned(),
                    count: 1,
                },
            ],
            emitted: 2,
            entry_limit: 16,
            unretained_name_observations: 0,
            overlong_name_observations: 0,
            output_truncated: false,
            overflowed: false,
        };
        let modes = [
            ("off", None),
            ("failure", Some(rollout_exhaustion_fuel_fixture(None))),
            (
                "detailed",
                Some(rollout_exhaustion_fuel_fixture(Some(detailed_hotset))),
            ),
        ];
        let mut expected_primary = None;

        for (mode, fuel) in modes {
            let conversion = CommandDiagnosticConversionContext::new(
                "declaration_value",
                "fuel_exhausted",
                "pi",
                "pi",
                2,
            )
            .unwrap();
            let mut diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
                .with_field("kernel_handoff")
                .with_conversion(conversion);
            if let Some(fuel) = fuel {
                diagnostic = diagnostic.with_kernel_fuel(fuel);
            }
            let result = CommandResult::failed("package build-certs", ".", vec![diagnostic]);
            let first = result.render_json();
            let second = result.render_json();
            assert_eq!(first.as_bytes(), second.as_bytes(), "mode={mode}");

            let mut primary = result.clone();
            primary.diagnostics[0].kernel_fuel = None;
            if let Some(expected) = &expected_primary {
                assert_eq!(&primary, expected, "mode={mode}");
            } else {
                expected_primary = Some(primary);
            }
            assert_eq!(result.status, super::CommandStatus::Failed);
            assert!(!first.contains("\"timings\":"), "mode={mode}");
            assert_eq!(first.contains("\"kernel_fuel\":"), mode != "off");
            assert_eq!(
                first.contains("\"retained_delta_constants\":null"),
                mode == "failure"
            );
            assert_eq!(
                first.contains("Observed.AliasExpected2"),
                mode == "detailed"
            );
        }
    }

    #[test]
    fn command_diagnostic_whnf_fuel_has_no_conversion_and_renders_root_path() {
        let mut fuel = conversion_fuel_fixture(None);
        fuel.resource = "whnf".to_owned();
        fuel.comparison_path.steps.clear();
        let diagnostic = CommandDiagnostic::error(DiagnosticKind::Build, "build_failed")
            .with_field("kernel_handoff")
            .with_kernel_fuel(fuel);
        let result = CommandResult::failed("package build-certs", ".", vec![diagnostic]);
        let expected_fuel = expected_conversion_fuel_json("null")
            .replacen("\"resource\":\"conversion\"", "\"resource\":\"whnf\"", 1)
            .replace(
                "\"steps\":[\"app_argument\",\"pi_body\",\"whnf_left\",\"app_function\"]",
                "\"steps\":[]",
            );
        assert_eq!(
            result.render_json(),
            format!(
                "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\",\"field\":\"kernel_handoff\",\"kernel_fuel\":{expected_fuel}}}],\"artifacts\":[]}}"
            )
        );
        assert_eq!(
            result.render_human(),
            "package build-certs: failed\nerror Build build_failed field=kernel_handoff\nkernel fuel:\n  subsystem: fast_kernel\n  resource: whnf\n  failed operation: budget=5000000 spent=5000000 remaining=0\n  work: defeq_calls=4187 whnf_calls=9120 beta=64 delta=4821031 iota=0\n  declaration: conversion_spent=5000218 whnf_spent=18342 physical_reductions=4821164\n  path: <root>\n  path truncated: false\n  overflowed: false"
        );
    }

    #[test]
    fn command_kernel_fuel_frontend_projection_preserves_bounded_payload() {
        let frontend = npa_frontend::HumanKernelFuelDiagnostic {
            subsystem: "fast_kernel".to_owned(),
            resource: "whnf".to_owned(),
            failed_operation: npa_frontend::HumanKernelOperationWork {
                fuel: npa_frontend::HumanKernelFuelOperationCounters {
                    budget: 9,
                    spent: 9,
                    remaining: 0,
                    exhausted: true,
                    overflowed: false,
                },
                work: npa_frontend::HumanKernelWorkSnapshot {
                    check_calls: 1,
                    infer_calls: 2,
                    whnf_calls: 3,
                    defeq_calls: 4,
                    quick_equality_hits: 5,
                    beta_steps: 6,
                    delta_steps: 7,
                    iota_steps: 8,
                    physical_reductions: 21,
                    overflowed: false,
                },
            },
            declaration: npa_frontend::HumanKernelDeclarationWork {
                fuel: npa_frontend::HumanKernelFuelTotals {
                    whnf: npa_frontend::HumanKernelFuelDomainTotals {
                        calls: 1,
                        logical_spent: 9,
                        successful_operation_fuel: 0,
                        exhausted_operation_fuel: 9,
                        overflowed: false,
                    },
                    conversion: npa_frontend::HumanKernelFuelDomainTotals {
                        calls: 0,
                        logical_spent: 0,
                        successful_operation_fuel: 0,
                        exhausted_operation_fuel: 0,
                        overflowed: false,
                    },
                },
                work: npa_frontend::HumanKernelWorkSnapshot {
                    check_calls: 1,
                    infer_calls: 2,
                    whnf_calls: 3,
                    defeq_calls: 4,
                    quick_equality_hits: 5,
                    beta_steps: 6,
                    delta_steps: 7,
                    iota_steps: 8,
                    physical_reductions: 21,
                    overflowed: false,
                },
                overflowed: false,
            },
            comparison_path: npa_frontend::HumanKernelComparisonPath {
                steps: Vec::new(),
                truncated: false,
            },
            retained_delta_constants: Some(npa_frontend::HumanKernelDeltaHotsetSummary {
                retained_names: 0,
                capacity: 256,
                entries: Vec::new(),
                emitted: 0,
                entry_limit: 16,
                unretained_name_observations: 0,
                overlong_name_observations: 0,
                output_truncated: false,
                overflowed: false,
            }),
            overflowed: false,
        };

        let projected = CommandKernelFuelDiagnostic::from_frontend(&frontend);
        assert_eq!(projected.subsystem, frontend.subsystem);
        assert_eq!(projected.resource, frontend.resource);
        assert_eq!(projected.failed_operation.fuel.spent, 9);
        assert_eq!(projected.failed_operation.work.physical_reductions, 21);
        assert_eq!(projected.declaration.fuel.whnf.exhausted_operation_fuel, 9);
        assert_eq!(projected.declaration.fuel.conversion.calls, 0);
        assert!(projected.comparison_path.steps.is_empty());
        assert_eq!(
            projected
                .retained_delta_constants
                .as_ref()
                .map(|summary| summary.capacity),
            Some(256)
        );
        assert!(!projected.overflowed);
    }

    #[test]
    fn command_diagnostic_detailed_hotset_and_present_empty_hotset_are_byte_exact() {
        let hotset = CommandKernelDeltaHotsetSummary {
            retained_names: 2,
            capacity: 256,
            entries: vec![
                CommandKernelDeltaHotsetEntry {
                    constant: "MyProject.Expr.eval".to_owned(),
                    count: 3_100_421,
                },
                CommandKernelDeltaHotsetEntry {
                    constant: "MyProject.Residue.normalize".to_owned(),
                    count: 1_720_679,
                },
            ],
            emitted: 2,
            entry_limit: 16,
            unretained_name_observations: 0,
            overlong_name_observations: 0,
            output_truncated: false,
            overflowed: false,
        };
        let detailed = conversion_fuel_fixture(Some(hotset));
        assert_eq!(
            command_kernel_fuel_json(&detailed),
            expected_conversion_fuel_json(
                "{\"retained_names\":2,\"capacity\":256,\"entries\":[{\"constant\":\"MyProject.Expr.eval\",\"count\":3100421},{\"constant\":\"MyProject.Residue.normalize\",\"count\":1720679}],\"emitted\":2,\"entry_limit\":16,\"unretained_name_observations\":0,\"overlong_name_observations\":0,\"output_truncated\":false,\"overflowed\":false}"
            )
        );
        assert_eq!(
            detailed.render_human(),
            "kernel fuel:\n  subsystem: fast_kernel\n  resource: conversion\n  failed operation: budget=5000000 spent=5000000 remaining=0\n  work: defeq_calls=4187 whnf_calls=9120 beta=64 delta=4821031 iota=0\n  declaration: conversion_spent=5000218 whnf_spent=18342 physical_reductions=4821164\n  path: app.argument > pi.body > whnf.left > app.function\n  path truncated: false\n  overflowed: false\n  retained delta constants:\n    MyProject.Expr.eval: 3100421\n    MyProject.Residue.normalize: 1720679\n  retained names: 2/256; emitted: 2/16; unretained observations: 0;\n    overlong observations: 0; output truncated: false"
        );

        let empty_hotset = CommandKernelDeltaHotsetSummary {
            retained_names: 0,
            capacity: 256,
            entries: Vec::new(),
            emitted: 0,
            entry_limit: 16,
            unretained_name_observations: 0,
            overlong_name_observations: 0,
            output_truncated: false,
            overflowed: false,
        };
        let empty = conversion_fuel_fixture(Some(empty_hotset));
        assert_eq!(
            command_kernel_fuel_json(&empty),
            expected_conversion_fuel_json(
                "{\"retained_names\":0,\"capacity\":256,\"entries\":[],\"emitted\":0,\"entry_limit\":16,\"unretained_name_observations\":0,\"overlong_name_observations\":0,\"output_truncated\":false,\"overflowed\":false}"
            )
        );
        assert!(empty.render_human().ends_with(
            "  retained delta constants:\n  retained names: 0/256; emitted: 0/16; unretained observations: 0;\n    overlong observations: 0; output truncated: false"
        ));
    }

    #[test]
    fn command_kernel_fuel_json_prunes_hotset_then_path_deterministically() {
        let mut diagnostic = conversion_fuel_fixture(Some(CommandKernelDeltaHotsetSummary {
            retained_names: 4,
            capacity: 256,
            entries: (0_u64..4)
                .map(|index| CommandKernelDeltaHotsetEntry {
                    constant: format!("Fixture.{}.Entry{index}", "A".repeat(220)),
                    count: 4 - index,
                })
                .collect(),
            emitted: 4,
            entry_limit: 16,
            unretained_name_observations: 0,
            overlong_name_observations: 0,
            output_truncated: false,
            overflowed: false,
        }));
        diagnostic.comparison_path.steps = vec![
            "app_function".to_owned(),
            "app_argument".to_owned(),
            "pi_domain".to_owned(),
            "pi_body".to_owned(),
            "whnf_left".to_owned(),
            "whnf_right".to_owned(),
        ];

        let mut one_hotset_entry_removed = diagnostic.clone();
        let summary = one_hotset_entry_removed
            .retained_delta_constants
            .as_mut()
            .unwrap();
        summary.entries.pop().expect("fixture has a canonical tail");
        summary.emitted = 3;
        summary.output_truncated = true;
        let mut one_hotset_entry_removed_json = String::new();
        push_command_kernel_fuel_json(
            &mut one_hotset_entry_removed_json,
            &one_hotset_entry_removed,
        );
        assert_eq!(
            command_kernel_fuel_json_with_limit(&diagnostic, one_hotset_entry_removed_json.len()),
            one_hotset_entry_removed_json,
            "the canonical hotset tail must be the first pruned entry"
        );

        let mut no_entries = diagnostic.clone();
        let summary = no_entries.retained_delta_constants.as_mut().unwrap();
        summary.entries.clear();
        summary.emitted = 0;
        summary.output_truncated = true;
        let mut no_entries_json = String::new();
        push_command_kernel_fuel_json(&mut no_entries_json, &no_entries);
        assert_eq!(
            command_kernel_fuel_json_with_limit(&diagnostic, no_entries_json.len()),
            no_entries_json,
            "hotset entries must be removed before any path step"
        );

        let mut one_middle_step_removed = no_entries.clone();
        one_middle_step_removed.comparison_path.steps.remove(3);
        one_middle_step_removed.comparison_path.truncated = true;
        let mut one_middle_step_removed_json = String::new();
        push_command_kernel_fuel_json(&mut one_middle_step_removed_json, &one_middle_step_removed);
        assert_eq!(
            command_kernel_fuel_json_with_limit(&diagnostic, one_middle_step_removed_json.len()),
            one_middle_step_removed_json,
            "the first path prune must remove steps.len() / 2"
        );

        let mut endpoints = no_entries;
        endpoints.comparison_path.steps = vec!["app_function".to_owned(), "whnf_right".to_owned()];
        endpoints.comparison_path.truncated = true;
        let mut endpoints_json = String::new();
        push_command_kernel_fuel_json(&mut endpoints_json, &endpoints);
        let first = command_kernel_fuel_json_with_limit(&diagnostic, endpoints_json.len());
        let second = command_kernel_fuel_json_with_limit(&diagnostic, endpoints_json.len());
        assert_eq!(first, endpoints_json);
        assert_eq!(second, first);
        assert_eq!(first.matches("app_function").count(), 1);
        assert_eq!(first.matches("whnf_right").count(), 1);
        assert!(first.contains("\"truncated\":true"));
        assert!(first.contains("\"output_truncated\":true"));
        assert!(
            command_kernel_fuel_json(&diagnostic).len() <= KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES
        );
    }

    #[test]
    fn command_kernel_fuel_json_bounds_forged_public_strings_without_panicking() {
        let oversized = "X".repeat(KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES * 2);
        let mut diagnostic = conversion_fuel_fixture(None);
        diagnostic.subsystem = oversized.clone();
        diagnostic.resource = oversized.clone();
        diagnostic.comparison_path.steps = vec![oversized.clone(), oversized];

        let json = command_kernel_fuel_json(&diagnostic);

        assert!(json.len() <= KERNEL_FUEL_DIAGNOSTIC_MAX_JSON_BYTES);
        assert!(json.contains("\"subsystem\":\"\""));
        assert!(json.contains("\"resource\":\"\""));
        assert!(json.contains("\"steps\":[]"));
        assert!(json.contains("\"truncated\":true"));
    }

    #[test]
    fn command_result_v0_5_omits_fuel_for_unrelated_and_incapable_commands() {
        let result = CommandResult::failed(
            "package build-certs",
            ".",
            vec![CommandDiagnostic::error(
                DiagnosticKind::Build,
                "build_failed",
            )],
        );
        assert_eq!(
            result.render_json(),
            "{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package build-certs\",\"root\":\".\",\"status\":\"failed\",\"diagnostics\":[{\"kind\":\"Build\",\"reason_code\":\"build_failed\",\"severity\":\"error\"}],\"artifacts\":[]}"
        );
        let incapable = CommandResult::passed("package check-hashes", ".");
        assert_eq!(
            incapable.render_json(),
            "{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package check-hashes\",\"root\":\".\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[]}"
        );
    }

    #[test]
    fn command_result_verify_selection_renderers_are_byte_exact() {
        let summary = PackageVerifySelectionSummary {
            schema: PACKAGE_VERIFY_SELECTION_SCHEMA.to_owned(),
            trusted: false,
            proof_evidence: false,
            mode: "base".to_owned(),
            outcome: "full_escalated".to_owned(),
            requested_base: Some("origin/main".to_owned()),
            base_commit: Some("a".repeat(40)),
            merge_base: Some("b".repeat(40)),
            head_commit: Some("c".repeat(40)),
            changed_path_count: Some(3),
            seed_modules: PackageVerifySelectionDetailCounts {
                attempted: 2,
                retained: 2,
                omitted: 0,
            },
            seed_details: vec!["Proofs.A".to_owned(), "Proofs.B".to_owned()],
            seed_identity: format!("sha256:{}", "0".repeat(64)),
            closure_module_count: Some(4),
            escalation_reasons: PackageVerifySelectionDetailCounts {
                attempted: 1,
                retained: 1,
                omitted: 0,
            },
            escalation_details: vec!["package_identity_changed:package".to_owned()],
            escalation_identity: format!("sha256:{}", "f".repeat(64)),
            detail_truncated: false,
            overflowed: false,
        };
        let result =
            CommandResult::passed("package verify-certs", "proofs").with_verify_selection(summary);

        assert_eq!(
            result.render_json(),
            format!(
                "{{\"schema\":\"npa.package.command_result.v0.5\",\"command\":\"package verify-certs\",\"root\":\"proofs\",\"status\":\"passed\",\"diagnostics\":[],\"artifacts\":[],\"verify_selection\":{{\"schema\":\"npa.package.verify-selection.v0.1\",\"trusted\":false,\"proof_evidence\":false,\"mode\":\"base\",\"outcome\":\"full_escalated\",\"requested_base\":\"origin/main\",\"base_commit\":\"{}\",\"merge_base\":\"{}\",\"head_commit\":\"{}\",\"changed_path_count\":3,\"seed_modules\":{{\"attempted\":2,\"retained\":2,\"omitted\":0}},\"seed_details\":[\"Proofs.A\",\"Proofs.B\"],\"seed_identity\":\"sha256:{}\",\"closure_module_count\":4,\"escalation_reasons\":{{\"attempted\":1,\"retained\":1,\"omitted\":0}},\"escalation_details\":[\"package_identity_changed:package\"],\"escalation_identity\":\"sha256:{}\",\"detail_truncated\":false,\"overflowed\":false}}}}",
                "a".repeat(40),
                "b".repeat(40),
                "c".repeat(40),
                "0".repeat(64),
                "f".repeat(64),
            )
        );
        assert_eq!(
            result.render_human(),
            "package verify-certs: passed\nverify selection: mode=base outcome=full_escalated seeds=2 closure_modules=4 changed_paths=3 trusted=false proof_evidence=false"
        );
    }

    #[test]
    fn command_result_human_timings_show_summary_and_slowest_modules() {
        let mut recorder =
            PerformanceMeasurementRecorder::new(PerformanceMeasurementMode::Detailed);
        for (module, checker_elapsed_ns) in [("A", 7), ("B", 19), ("C", 19)] {
            recorder.record_module(PerformanceModuleMeasurement {
                module: module.to_owned(),
                certificate_bytes: 1,
                declaration_count: 1,
                import_count: 0,
                checker_elapsed_ns,
                package_sharding: None,
            });
        }
        let result =
            CommandResult::passed("package verify-certs", ".").with_timings(CommandTimings {
                schema: PACKAGE_TIMINGS_SCHEMA_V0_2,
                mode: "detailed".to_owned(),
                metrics: vec![
                    CommandTimingMetric {
                        field: "checker_ms".to_owned(),
                        milliseconds: 2,
                    },
                    CommandTimingMetric {
                        field: "total_ms".to_owned(),
                        milliseconds: 3,
                    },
                ],
                measurements: recorder.report(),
            });

        assert_eq!(
            result.render_human(),
            "package verify-certs: passed\ntimings: mode=detailed checker_ms=2 total_ms=3\ntiming module: B checker_elapsed_ns=19 scope=retained\ntiming module: C checker_elapsed_ns=19 scope=retained\ntiming module: A checker_elapsed_ns=7 scope=retained"
        );
    }

    fn conversion_fuel_fixture(
        retained_delta_constants: Option<CommandKernelDeltaHotsetSummary>,
    ) -> CommandKernelFuelDiagnostic {
        CommandKernelFuelDiagnostic {
            subsystem: "fast_kernel".to_owned(),
            resource: "conversion".to_owned(),
            failed_operation: CommandKernelOperationWork {
                fuel: CommandKernelFuelOperationCounters {
                    budget: 5_000_000,
                    spent: 5_000_000,
                    remaining: 0,
                    exhausted: true,
                    overflowed: false,
                },
                work: CommandKernelWorkSnapshot {
                    check_calls: 0,
                    infer_calls: 0,
                    whnf_calls: 9_120,
                    defeq_calls: 4_187,
                    quick_equality_hits: 203,
                    beta_steps: 64,
                    delta_steps: 4_821_031,
                    iota_steps: 0,
                    physical_reductions: 4_821_095,
                    overflowed: false,
                },
            },
            declaration: CommandKernelDeclarationWork {
                fuel: CommandKernelFuelTotals {
                    whnf: CommandKernelFuelDomainTotals {
                        calls: 114,
                        logical_spent: 18_342,
                        successful_operation_fuel: 18_342,
                        exhausted_operation_fuel: 0,
                        overflowed: false,
                    },
                    conversion: CommandKernelFuelDomainTotals {
                        calls: 27,
                        logical_spent: 5_000_218,
                        successful_operation_fuel: 218,
                        exhausted_operation_fuel: 5_000_000,
                        overflowed: false,
                    },
                },
                work: CommandKernelWorkSnapshot {
                    check_calls: 1,
                    infer_calls: 12,
                    whnf_calls: 9_234,
                    defeq_calls: 4_214,
                    quick_equality_hits: 210,
                    beta_steps: 64,
                    delta_steps: 4_821_100,
                    iota_steps: 0,
                    physical_reductions: 4_821_164,
                    overflowed: false,
                },
                overflowed: false,
            },
            comparison_path: CommandKernelComparisonPath {
                steps: ["app_argument", "pi_body", "whnf_left", "app_function"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                truncated: false,
            },
            retained_delta_constants,
            overflowed: false,
        }
    }

    fn rollout_exhaustion_fuel_fixture(
        retained_delta_constants: Option<CommandKernelDeltaHotsetSummary>,
    ) -> CommandKernelFuelDiagnostic {
        CommandKernelFuelDiagnostic {
            subsystem: "fast_kernel".to_owned(),
            resource: "conversion".to_owned(),
            failed_operation: CommandKernelOperationWork {
                fuel: CommandKernelFuelOperationCounters {
                    budget: 7,
                    spent: 7,
                    remaining: 0,
                    exhausted: true,
                    overflowed: false,
                },
                work: CommandKernelWorkSnapshot {
                    check_calls: 0,
                    infer_calls: 0,
                    whnf_calls: 4,
                    defeq_calls: 3,
                    quick_equality_hits: 1,
                    beta_steps: 0,
                    delta_steps: 1,
                    iota_steps: 0,
                    physical_reductions: 1,
                    overflowed: false,
                },
            },
            declaration: CommandKernelDeclarationWork {
                fuel: CommandKernelFuelTotals {
                    whnf: CommandKernelFuelDomainTotals {
                        calls: 8,
                        logical_spent: 8,
                        successful_operation_fuel: 8,
                        exhausted_operation_fuel: 0,
                        overflowed: false,
                    },
                    conversion: CommandKernelFuelDomainTotals {
                        calls: 3,
                        logical_spent: 15,
                        successful_operation_fuel: 8,
                        exhausted_operation_fuel: 7,
                        overflowed: false,
                    },
                },
                work: CommandKernelWorkSnapshot {
                    check_calls: 3,
                    infer_calls: 14,
                    whnf_calls: 16,
                    defeq_calls: 5,
                    quick_equality_hits: 1,
                    beta_steps: 0,
                    delta_steps: 3,
                    iota_steps: 0,
                    physical_reductions: 3,
                    overflowed: false,
                },
                overflowed: false,
            },
            comparison_path: CommandKernelComparisonPath {
                steps: ["pi_body", "whnf_right"].map(str::to_owned).to_vec(),
                truncated: false,
            },
            retained_delta_constants,
            overflowed: false,
        }
    }

    fn expected_conversion_fuel_json(retained_delta_constants: &str) -> String {
        concat!(
            "{\"schema\":\"npa.kernel-fuel-diagnostic.v0.2\",\"trusted\":false,\"proof_evidence\":false,",
            "\"subsystem\":\"fast_kernel\",\"resource\":\"conversion\",",
            "\"failed_operation\":{\"fuel\":{\"budget\":5000000,\"spent\":5000000,\"remaining\":0,\"exhausted\":true,\"overflowed\":false},",
            "\"work\":{\"check_calls\":0,\"infer_calls\":0,\"whnf_calls\":9120,\"defeq_calls\":4187,\"quick_equality_hits\":203,\"beta_steps\":64,\"delta_steps\":4821031,\"iota_steps\":0,\"physical_reductions\":4821095,\"overflowed\":false}},",
            "\"declaration\":{\"fuel\":{\"whnf\":{\"calls\":114,\"logical_spent\":18342,\"successful_operation_fuel\":18342,\"exhausted_operation_fuel\":0,\"overflowed\":false},",
            "\"conversion\":{\"calls\":27,\"logical_spent\":5000218,\"successful_operation_fuel\":218,\"exhausted_operation_fuel\":5000000,\"overflowed\":false}},",
            "\"work\":{\"check_calls\":1,\"infer_calls\":12,\"whnf_calls\":9234,\"defeq_calls\":4214,\"quick_equality_hits\":210,\"beta_steps\":64,\"delta_steps\":4821100,\"iota_steps\":0,\"physical_reductions\":4821164,\"overflowed\":false},\"overflowed\":false},",
            "\"comparison_path\":{\"steps\":[\"app_argument\",\"pi_body\",\"whnf_left\",\"app_function\"],\"truncated\":false},",
            "\"retained_delta_constants\":$HOTSET$,\"overflowed\":false}"
        )
        .replace("$HOTSET$", retained_delta_constants)
    }
}
