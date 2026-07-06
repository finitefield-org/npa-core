//! Argument model and parser for the `npa` binary.

use std::fmt;
use std::path::PathBuf;

/// Parsed top-level CLI action.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliAction {
    /// Execute a parsed command.
    Run(CliCommand),
    /// Render deterministic help for the selected topic.
    Help(HelpTopic),
    /// Print the `npa` CLI package version.
    Version,
}

/// Parsed top-level command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliCommand {
    /// `npa package ...`.
    Package(PackageCommand),
}

impl CliCommand {
    /// Stable command name used in diagnostics.
    pub fn command_name(&self) -> &'static str {
        match self {
            Self::Package(command) => command.command_name(),
        }
    }
}

/// Parsed `npa package` subcommand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageCommand {
    /// `npa package check`.
    Check(PackageCommonOptions),
    /// `npa package build-certs`.
    BuildCerts(PackageBuildCertsOptions),
    /// `npa package axiom-report`.
    AxiomReport(PackageAxiomReportOptions),
    /// `npa package index`.
    Index(PackageIndexOptions),
    /// `npa package export-summary`.
    ExportSummary(PackageExportSummaryOptions),
    /// `npa package verify-certs`.
    VerifyCerts(PackageVerifyCertsOptions),
    /// `npa package check-hashes`.
    CheckHashes(PackageCommonOptions),
    /// `npa package publish-plan`.
    PublishPlan(PackagePublishPlanOptions),
    /// `npa package check-generated`.
    CheckGenerated(PackageCheckGeneratedOptions),
    /// `npa package high-trust`.
    HighTrust(Box<PackageHighTrustOptions>),
    /// `npa package gate-plan`.
    GatePlan(PackageGatePlanOptions),
}

impl PackageCommand {
    /// Stable command name used in diagnostics.
    pub fn command_name(&self) -> &'static str {
        match self {
            Self::Check(_) => "package check",
            Self::BuildCerts(_) => "package build-certs",
            Self::AxiomReport(_) => "package axiom-report",
            Self::Index(_) => "package index",
            Self::ExportSummary(_) => "package export-summary",
            Self::VerifyCerts(_) => "package verify-certs",
            Self::CheckHashes(_) => "package check-hashes",
            Self::PublishPlan(_) => "package publish-plan",
            Self::CheckGenerated(_) => "package check-generated",
            Self::HighTrust(_) => "package high-trust",
            Self::GatePlan(_) => "package gate-plan",
        }
    }

    /// Common options for the package subcommand.
    pub fn common_options(&self) -> &PackageCommonOptions {
        match self {
            Self::Check(options) | Self::CheckHashes(options) => options,
            Self::BuildCerts(options) => &options.common,
            Self::AxiomReport(options) => &options.common,
            Self::Index(options) => &options.common,
            Self::ExportSummary(options) => &options.common,
            Self::VerifyCerts(options) => &options.common,
            Self::PublishPlan(options) => &options.common,
            Self::CheckGenerated(options) => &options.common,
            Self::HighTrust(options) => &options.common,
            Self::GatePlan(options) => &options.common,
        }
    }
}

/// Common options accepted by each package subcommand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageCommonOptions {
    /// Package root path. Defaults to `.` without parent search.
    pub root: PathBuf,
    /// Whether deterministic JSON output was requested.
    pub json: bool,
}

impl Default for PackageCommonOptions {
    fn default() -> Self {
        Self {
            root: PathBuf::from("."),
            json: false,
        }
    }
}

/// Options for `package gate-plan`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageGatePlanOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Git merge-base comparison base for `git diff --name-only <base>...HEAD`.
    pub base: String,
}

/// Options for `package build-certs`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageBuildCertsOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: rebuild in memory without writing files.
    pub check: bool,
    /// Local build-check cache mode for check mode.
    pub build_check_cache: PackageBuildCheckCacheMode,
}

/// Local package build-check cache mode for `package build-certs --check`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageBuildCheckCacheMode {
    /// Do not read or write package build-check cache entries.
    Off,
    /// Read cache entries for diagnostics, but still run live build comparison.
    ReadThrough,
}

impl PackageBuildCheckCacheMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
        }
    }

    /// Return whether this mode reads or writes the local build-check cache store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough => true,
        }
    }
}

/// Options for `package axiom-report`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageAxiomReportOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package index`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageIndexOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package export-summary`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageExportSummaryOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Optional package-relative output path.
    pub out: Option<PathBuf>,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package publish-plan`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackagePublishPlanOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package check-generated`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageCheckGeneratedOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Options for `package high-trust`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageHighTrustOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Workspace-relative release policy path.
    pub release_policy: PathBuf,
    /// Expected canonical release policy hash.
    pub release_policy_hash: String,
    /// Workspace-relative high-trust runner policy path.
    pub runner_policy: PathBuf,
    /// Expected canonical runner policy hash.
    pub runner_policy_hash: String,
    /// Workspace-relative high-trust challenge runner policy path.
    pub challenge_runner_policy: PathBuf,
    /// Expected canonical challenge runner policy hash.
    pub challenge_runner_policy_hash: String,
    /// Workspace-relative checker binary registry path.
    pub checker_registry: PathBuf,
    /// Optional workspace-relative output path. Defaults under package root.
    pub out: Option<PathBuf>,
    /// Check mode: regenerate in memory without writing files.
    pub check: bool,
}

/// Options for `package verify-certs`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageVerifyCertsOptions {
    /// Common package command options.
    pub common: PackageCommonOptions,
    /// Checker mode selected for source-free verification.
    pub checker: PackageChecker,
    /// Local package audit cache mode.
    pub audit_cache: PackageAuditCacheMode,
    /// Local verifier memo mode.
    pub verifier_memo: PackageVerifierMemoMode,
    /// Maximum verifier worker count.
    pub jobs: usize,
    /// Required external checker runner inputs when `checker = external`.
    pub external: Option<PackageExternalCheckerOptions>,
    /// Optional package audit timing telemetry mode.
    pub timings: PackageTimingMode,
}

/// Optional package audit timing telemetry mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageTimingMode {
    /// Do not collect or render timing telemetry.
    Off,
    /// Collect stable command phase totals.
    Summary,
    /// Collect stable command phase totals with the detailed mode label.
    Detailed,
}

impl PackageTimingMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Summary => "summary",
            Self::Detailed => "detailed",
        }
    }

    /// Return whether this mode emits timing telemetry.
    pub const fn is_enabled(self) -> bool {
        match self {
            Self::Off => false,
            Self::Summary | Self::Detailed => true,
        }
    }
}

/// Options required by `package verify-certs --checker external`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageExternalCheckerOptions {
    /// Package-relative runner policy path.
    pub runner_policy: PathBuf,
    /// Expected canonical runner policy hash.
    pub runner_policy_hash: String,
    /// Package-relative checker binary registry path.
    pub checker_registry: PathBuf,
}

/// Supported package certificate checker modes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageChecker {
    /// CLR-03 source-free reference checker path.
    Reference,
    /// CLR-03 fast kernel verifier path for local development.
    Fast,
    /// CLR-08 external checker runner path.
    External,
}

impl PackageChecker {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Reference => "reference",
            Self::Fast => "fast",
            Self::External => "external",
        }
    }
}

/// Local package audit cache mode for `package verify-certs`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageAuditCacheMode {
    /// Do not read or write package audit cache entries.
    Off,
    /// Read cache entries for diagnostics, but still run live verification.
    ReadThrough,
    /// Use exact accepted local cache hits for local-only audit acceleration.
    LocalHit,
}

impl PackageAuditCacheMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
            Self::LocalHit => "local-hit",
        }
    }

    /// Return whether this mode reads the local audit cache store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough | Self::LocalHit => true,
        }
    }
}

/// Local verifier memo mode for `package verify-certs`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageVerifierMemoMode {
    /// Do not read or write disk-backed verifier memo entries.
    Off,
    /// Read and write disk-backed verifier memo entries, but still run live verification.
    ReadThrough,
    /// Use exact accepted disk-backed verifier memo hits for local-only audit acceleration.
    Disk,
}

impl PackageVerifierMemoMode {
    /// Stable CLI spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::ReadThrough => "read-through",
            Self::Disk => "disk",
        }
    }

    /// Return whether this mode reads or writes the local disk memo store.
    pub fn uses_local_store(self) -> bool {
        match self {
            Self::Off => false,
            Self::ReadThrough | Self::Disk => true,
        }
    }
}

/// Help topic selected by `--help`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HelpTopic {
    /// Top-level `npa` help.
    Root,
    /// `npa package` help.
    Package,
    /// `npa package check --help`.
    PackageCheck,
    /// `npa package build-certs --help`.
    PackageBuildCerts,
    /// `npa package axiom-report --help`.
    PackageAxiomReport,
    /// `npa package index --help`.
    PackageIndex,
    /// `npa package export-summary --help`.
    PackageExportSummary,
    /// `npa package verify-certs --help`.
    PackageVerifyCerts,
    /// `npa package check-hashes --help`.
    PackageCheckHashes,
    /// `npa package publish-plan --help`.
    PackagePublishPlan,
    /// `npa package check-generated --help`.
    PackageCheckGenerated,
    /// `npa package high-trust --help`.
    PackageHighTrust,
    /// `npa package gate-plan --help`.
    PackageGatePlan,
}

/// Stable usage error produced by the argument parser.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CliUsageError {
    /// Machine-readable reason code.
    pub reason: UsageReason,
    /// Command context, when known.
    pub command: Option<String>,
    /// Flag involved in the error, when applicable.
    pub flag: Option<String>,
    /// Value involved in the error, when applicable.
    pub value: Option<String>,
}

impl CliUsageError {
    fn new(reason: UsageReason) -> Self {
        Self {
            reason,
            command: None,
            flag: None,
            value: None,
        }
    }

    fn with_command(mut self, command: impl Into<String>) -> Self {
        self.command = Some(command.into());
        self
    }

    fn with_flag(mut self, flag: impl Into<String>) -> Self {
        self.flag = Some(flag.into());
        self
    }

    fn with_value(mut self, value: impl Into<String>) -> Self {
        self.value = Some(value.into());
        self
    }

    /// Deterministic human-readable usage diagnostic.
    pub fn render_human(&self) -> String {
        let mut message = format!("error: {}", self.reason.reason_code());
        if let Some(command) = &self.command {
            message.push_str(&format!(" command={command}"));
        }
        if let Some(flag) = &self.flag {
            message.push_str(&format!(" flag={flag}"));
        }
        if let Some(value) = &self.value {
            message.push_str(&format!(" value={value}"));
        }
        message
    }
}

impl fmt::Display for CliUsageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render_human())
    }
}

impl std::error::Error for CliUsageError {}

/// Stable usage reason codes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UsageReason {
    /// Unknown command or subcommand.
    UnknownCommand,
    /// Unknown flag.
    UnknownFlag,
    /// Flag requires a value but none was provided.
    MissingFlagValue,
    /// Flag was provided more than once.
    DuplicateFlag,
    /// A selected mode requires a flag that was not provided.
    MissingRequiredFlag,
    /// Known flag is outside CLR-04 scope or the selected command.
    UnsupportedFlag,
    /// Flag value has the wrong deterministic shape.
    InvalidFlagValue,
    /// Checker mode is outside CLR-04 scope.
    UnsupportedChecker,
    /// Package audit cache mode is unsupported.
    UnsupportedAuditCacheMode,
    /// Package verifier memo mode is unsupported.
    UnsupportedVerifierMemoMode,
    /// Package build-check cache mode is unsupported.
    UnsupportedBuildCheckCacheMode,
    /// Package timing telemetry mode is unsupported.
    UnsupportedTimingMode,
}

impl UsageReason {
    /// Stable reason code used by later structured diagnostics.
    pub fn reason_code(self) -> &'static str {
        match self {
            Self::UnknownCommand => "unknown_command",
            Self::UnknownFlag => "unknown_flag",
            Self::MissingFlagValue => "missing_flag_value",
            Self::DuplicateFlag => "duplicate_flag",
            Self::MissingRequiredFlag => "missing_required_flag",
            Self::UnsupportedFlag => "unsupported_flag",
            Self::InvalidFlagValue => "invalid_flag_value",
            Self::UnsupportedChecker => "unsupported_checker",
            Self::UnsupportedAuditCacheMode => "unsupported_audit_cache_mode",
            Self::UnsupportedVerifierMemoMode => "unsupported_verifier_memo_mode",
            Self::UnsupportedBuildCheckCacheMode => "unsupported_build_check_cache_mode",
            Self::UnsupportedTimingMode => "unsupported_timing_mode",
        }
    }
}

/// Parse `npa` arguments, excluding the binary name.
pub fn parse_cli_args<I, S>(args: I) -> Result<CliAction, CliUsageError>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    if args.is_empty() {
        return Ok(CliAction::Help(HelpTopic::Root));
    }

    match args[0].as_str() {
        "--help" | "-h" => Ok(CliAction::Help(HelpTopic::Root)),
        "--version" | "-V" | "version" => Ok(CliAction::Version),
        "package" => parse_package_args(&args[1..]),
        command => Err(CliUsageError::new(UsageReason::UnknownCommand).with_command(command)),
    }
}

fn parse_package_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if args.is_empty() {
        return Ok(CliAction::Help(HelpTopic::Package));
    }
    match args[0].as_str() {
        "--help" | "-h" => Ok(CliAction::Help(HelpTopic::Package)),
        "check" => parse_package_check_args(&args[1..]),
        "build-certs" => parse_package_build_certs_args(&args[1..]),
        "axiom-report" => parse_package_axiom_report_args(&args[1..]),
        "index" => parse_package_index_args(&args[1..]),
        "export-summary" => parse_package_export_summary_args(&args[1..]),
        "verify-certs" => parse_package_verify_certs_args(&args[1..]),
        "check-hashes" => parse_package_check_hashes_args(&args[1..]),
        "publish-plan" => parse_package_publish_plan_args(&args[1..]),
        "check-generated" => parse_package_check_generated_args(&args[1..]),
        "high-trust" => parse_package_high_trust_args(&args[1..]),
        "gate-plan" => parse_package_gate_plan_args(&args[1..]),
        command if command.starts_with('-') => {
            Err(flag_error(command, UsageReason::UnknownFlag).with_command("package"))
        }
        command => Err(CliUsageError::new(UsageReason::UnknownCommand)
            .with_command(format!("package {command}"))),
    }
}

fn parse_package_check_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheck));
    }
    let common = parse_common_options(args, "package check", &[])?;
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Check(
        common,
    ))))
}

fn parse_package_check_hashes_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheckHashes));
    }
    let common = parse_common_options(args, "package check-hashes", &[])?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::CheckHashes(common),
    )))
}

fn parse_package_gate_plan_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageGatePlan));
    }

    let mut common_tokens = Vec::new();
    let mut base = None::<String>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--base" => {
                parse_string_flag(args, &mut index, "--base", "package gate-plan", &mut base)?;
            }
            token if token.starts_with("--base=") => {
                parse_string_equals_flag(token, "--base", "package gate-plan", &mut base)?;
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(&common_tokens, "package gate-plan", &["--base"])?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::GatePlan(PackageGatePlanOptions {
            common,
            base: base.ok_or_else(|| {
                flag_error("--base", UsageReason::MissingRequiredFlag)
                    .with_command("package gate-plan")
            })?,
        }),
    )))
}

fn parse_package_build_certs_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageBuildCerts));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut build_check_cache = None::<PackageBuildCheckCacheMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package build-certs"));
                }
                check = true;
                index += 1;
            }
            "--build-check-cache" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                let value = flag_value(args, index, "--build-check-cache", "package build-certs")?;
                build_check_cache = Some(parse_build_check_cache_mode(value)?);
                index += 2;
            }
            "--build-check-cache=off" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(PackageBuildCheckCacheMode::Off);
                index += 1;
            }
            "--build-check-cache=read-through" => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(PackageBuildCheckCacheMode::ReadThrough);
                index += 1;
            }
            token if token.starts_with("--build-check-cache=") => {
                if build_check_cache.is_some() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::DuplicateFlag)
                            .with_command("package build-certs"),
                    );
                }
                let value = token.trim_start_matches("--build-check-cache=");
                if value.is_empty() {
                    return Err(
                        flag_error("--build-check-cache", UsageReason::MissingFlagValue)
                            .with_command("package build-certs"),
                    );
                }
                build_check_cache = Some(parse_build_check_cache_mode(value)?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package build-certs",
        &["--check", "--build-check-cache"],
    )?;
    let build_check_cache = build_check_cache.unwrap_or(PackageBuildCheckCacheMode::Off);
    if build_check_cache.uses_local_store() && !check {
        return Err(CliUsageError::new(UsageReason::UnsupportedFlag)
            .with_command("package build-certs")
            .with_flag("--build-check-cache")
            .with_value(build_check_cache.as_str()));
    }
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::BuildCerts(PackageBuildCertsOptions {
            common,
            check,
            build_check_cache,
        }),
    )))
}

fn parse_package_axiom_report_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageAxiomReport));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                let value = flag_value(args, index, "--timings", "package axiom-report")?;
                timings = Some(parse_timing_mode(value, "package axiom-report")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package axiom-report"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package axiom-report"));
                }
                timings = Some(parse_timing_mode(value, "package axiom-report")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package axiom-report",
        &["--check", "--checker", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::AxiomReport(PackageAxiomReportOptions {
            common,
            check,
            timings,
        }),
    )))
}

fn parse_package_index_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageIndex));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                let value = flag_value(args, index, "--timings", "package index")?;
                timings = Some(parse_timing_mode(value, "package index")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package index"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package index"));
                }
                timings = Some(parse_timing_mode(value, "package index")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package index",
        &["--check", "--checker", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(PackageCommand::Index(
        PackageIndexOptions {
            common,
            check,
            timings,
        },
    ))))
}

fn parse_package_export_summary_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageExportSummary));
    }

    let mut common_tokens = Vec::new();
    let mut out = None::<PathBuf>;
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--out" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--out",
                    "package export-summary",
                    &mut out,
                )?;
            }
            token if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", "package export-summary", &mut out)?;
                index += 1;
            }
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                let value = flag_value(args, index, "--timings", "package export-summary")?;
                timings = Some(parse_timing_mode(value, "package export-summary")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package export-summary"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package export-summary"));
                }
                timings = Some(parse_timing_mode(value, "package export-summary")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package export-summary",
        &["--check", "--out", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::ExportSummary(PackageExportSummaryOptions {
            common,
            out,
            check,
            timings,
        }),
    )))
}

fn parse_package_publish_plan_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackagePublishPlan));
    }

    let mut common_tokens = Vec::new();
    let mut check = false;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                check = true;
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                let value = flag_value(args, index, "--timings", "package publish-plan")?;
                timings = Some(parse_timing_mode(value, "package publish-plan")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package publish-plan"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package publish-plan"));
                }
                timings = Some(parse_timing_mode(value, "package publish-plan")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package publish-plan",
        &["--check", "--timings"],
    )?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::PublishPlan(PackagePublishPlanOptions {
            common,
            check,
            timings,
        }),
    )))
}

fn parse_package_check_generated_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageCheckGenerated));
    }

    let mut common_tokens = Vec::new();
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package check-generated"));
                }
                let value = flag_value(args, index, "--timings", "package check-generated")?;
                timings = Some(parse_timing_mode(value, "package check-generated")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package check-generated"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package check-generated"));
                }
                timings = Some(parse_timing_mode(value, "package check-generated")?);
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(&common_tokens, "package check-generated", &["--timings"])?;
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::CheckGenerated(PackageCheckGeneratedOptions { common, timings }),
    )))
}

fn parse_package_high_trust_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageHighTrust));
    }

    let mut common_tokens = Vec::new();
    let mut release_policy = None::<PathBuf>;
    let mut release_policy_hash = None::<String>;
    let mut runner_policy = None::<PathBuf>;
    let mut runner_policy_hash = None::<String>;
    let mut challenge_runner_policy = None::<PathBuf>;
    let mut challenge_runner_policy_hash = None::<String>;
    let mut checker_registry = None::<PathBuf>;
    let mut out = None::<PathBuf>;
    let mut check = false;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--release-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--release-policy",
                    "package high-trust",
                    &mut release_policy,
                )?;
            }
            token if token.starts_with("--release-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--release-policy",
                    "package high-trust",
                    &mut release_policy,
                )?;
                index += 1;
            }
            "--release-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--release-policy-hash",
                    "package high-trust",
                    &mut release_policy_hash,
                )?;
            }
            token if token.starts_with("--release-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--release-policy-hash",
                    "package high-trust",
                    &mut release_policy_hash,
                )?;
                index += 1;
            }
            "--runner-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--runner-policy",
                    "package high-trust",
                    &mut runner_policy,
                )?;
            }
            token if token.starts_with("--runner-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--runner-policy",
                    "package high-trust",
                    &mut runner_policy,
                )?;
                index += 1;
            }
            "--runner-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--runner-policy-hash",
                    "package high-trust",
                    &mut runner_policy_hash,
                )?;
            }
            token if token.starts_with("--runner-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--runner-policy-hash",
                    "package high-trust",
                    &mut runner_policy_hash,
                )?;
                index += 1;
            }
            "--challenge-runner-policy" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--challenge-runner-policy",
                    "package high-trust",
                    &mut challenge_runner_policy,
                )?;
            }
            token if token.starts_with("--challenge-runner-policy=") => {
                parse_path_equals_flag(
                    token,
                    "--challenge-runner-policy",
                    "package high-trust",
                    &mut challenge_runner_policy,
                )?;
                index += 1;
            }
            "--challenge-runner-policy-hash" => {
                parse_string_flag(
                    args,
                    &mut index,
                    "--challenge-runner-policy-hash",
                    "package high-trust",
                    &mut challenge_runner_policy_hash,
                )?;
            }
            token if token.starts_with("--challenge-runner-policy-hash=") => {
                parse_string_equals_flag(
                    token,
                    "--challenge-runner-policy-hash",
                    "package high-trust",
                    &mut challenge_runner_policy_hash,
                )?;
                index += 1;
            }
            "--checker-registry" => {
                parse_path_flag(
                    args,
                    &mut index,
                    "--checker-registry",
                    "package high-trust",
                    &mut checker_registry,
                )?;
            }
            token if token.starts_with("--checker-registry=") => {
                parse_path_equals_flag(
                    token,
                    "--checker-registry",
                    "package high-trust",
                    &mut checker_registry,
                )?;
                index += 1;
            }
            "--out" => {
                parse_path_flag(args, &mut index, "--out", "package high-trust", &mut out)?;
            }
            token if token.starts_with("--out=") => {
                parse_path_equals_flag(token, "--out", "package high-trust", &mut out)?;
                index += 1;
            }
            "--check" => {
                if check {
                    return Err(flag_error("--check", UsageReason::DuplicateFlag)
                        .with_command("package high-trust"));
                }
                check = true;
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package high-trust",
        &[
            "--release-policy",
            "--release-policy-hash",
            "--runner-policy",
            "--runner-policy-hash",
            "--challenge-runner-policy",
            "--challenge-runner-policy-hash",
            "--checker-registry",
            "--out",
            "--check",
        ],
    )?;
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::HighTrust(Box::new(PackageHighTrustOptions {
            common,
            release_policy: release_policy.ok_or_else(|| {
                flag_error("--release-policy", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            release_policy_hash: release_policy_hash.ok_or_else(|| {
                flag_error("--release-policy-hash", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            runner_policy: runner_policy.ok_or_else(|| {
                flag_error("--runner-policy", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            runner_policy_hash: runner_policy_hash.ok_or_else(|| {
                flag_error("--runner-policy-hash", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            challenge_runner_policy: challenge_runner_policy.ok_or_else(|| {
                flag_error(
                    "--challenge-runner-policy",
                    UsageReason::MissingRequiredFlag,
                )
                .with_command("package high-trust")
            })?,
            challenge_runner_policy_hash: challenge_runner_policy_hash.ok_or_else(|| {
                flag_error(
                    "--challenge-runner-policy-hash",
                    UsageReason::MissingRequiredFlag,
                )
                .with_command("package high-trust")
            })?,
            checker_registry: checker_registry.ok_or_else(|| {
                flag_error("--checker-registry", UsageReason::MissingRequiredFlag)
                    .with_command("package high-trust")
            })?,
            out,
            check,
        })),
    )))
}

fn parse_package_verify_certs_args(args: &[String]) -> Result<CliAction, CliUsageError> {
    if contains_help(args) {
        return Ok(CliAction::Help(HelpTopic::PackageVerifyCerts));
    }

    let mut common_tokens = Vec::new();
    let mut checker = None::<PackageChecker>;
    let mut audit_cache = None::<PackageAuditCacheMode>;
    let mut verifier_memo = None::<PackageVerifierMemoMode>;
    let mut jobs = None::<usize>;
    let mut runner_policy = None::<PathBuf>;
    let mut runner_policy_hash = None::<String>;
    let mut checker_registry = None::<PathBuf>;
    let mut timings = None::<PackageTimingMode>;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--checker" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--checker", "package verify-certs")?;
                checker = Some(parse_checker(value)?);
                index += 2;
            }
            "--checker=reference" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::Reference);
                index += 1;
            }
            "--checker=fast" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::Fast);
                index += 1;
            }
            "--checker=external" => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                checker = Some(PackageChecker::External);
                index += 1;
            }
            token if token.starts_with("--checker=") => {
                if checker.is_some() {
                    return Err(flag_error("--checker", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--checker=");
                if value.is_empty() {
                    return Err(flag_error("--checker", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                checker = Some(parse_checker(value)?);
                index += 1;
            }
            "--audit-cache" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--audit-cache", "package verify-certs")?;
                audit_cache = Some(parse_audit_cache_mode(value)?);
                index += 2;
            }
            "--audit-cache=off" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::Off);
                index += 1;
            }
            "--audit-cache=read-through" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::ReadThrough);
                index += 1;
            }
            "--audit-cache=local-hit" => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(PackageAuditCacheMode::LocalHit);
                index += 1;
            }
            token if token.starts_with("--audit-cache=") => {
                if audit_cache.is_some() {
                    return Err(flag_error("--audit-cache", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--audit-cache=");
                if value.is_empty() {
                    return Err(flag_error("--audit-cache", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                audit_cache = Some(parse_audit_cache_mode(value)?);
                index += 1;
            }
            "--verifier-memo" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--verifier-memo", "package verify-certs")?;
                verifier_memo = Some(parse_verifier_memo_mode(value)?);
                index += 2;
            }
            "--verifier-memo=off" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::Off);
                index += 1;
            }
            "--verifier-memo=read-through" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::ReadThrough);
                index += 1;
            }
            "--verifier-memo=disk" => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(PackageVerifierMemoMode::Disk);
                index += 1;
            }
            token if token.starts_with("--verifier-memo=") => {
                if verifier_memo.is_some() {
                    return Err(flag_error("--verifier-memo", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--verifier-memo=");
                if value.is_empty() {
                    return Err(flag_error("--verifier-memo", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                verifier_memo = Some(parse_verifier_memo_mode(value)?);
                index += 1;
            }
            "--jobs" => {
                if jobs.is_some() {
                    return Err(flag_error("--jobs", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--jobs", "package verify-certs")?;
                jobs = Some(parse_jobs(value)?);
                index += 2;
            }
            token if token.starts_with("--jobs=") => {
                if jobs.is_some() {
                    return Err(flag_error("--jobs", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--jobs=");
                if value.is_empty() {
                    return Err(flag_error("--jobs", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                jobs = Some(parse_jobs(value)?);
                index += 1;
            }
            "--timings" => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--timings", "package verify-certs")?;
                timings = Some(parse_timing_mode(value, "package verify-certs")?);
                index += 2;
            }
            token if token.starts_with("--timings=") => {
                if timings.is_some() {
                    return Err(flag_error("--timings", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--timings=");
                if value.is_empty() {
                    return Err(flag_error("--timings", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                timings = Some(parse_timing_mode(value, "package verify-certs")?);
                index += 1;
            }
            "--runner-policy" => {
                if runner_policy.is_some() {
                    return Err(flag_error("--runner-policy", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--runner-policy", "package verify-certs")?;
                runner_policy = Some(PathBuf::from(value));
                index += 2;
            }
            token if token.starts_with("--runner-policy=") => {
                if runner_policy.is_some() {
                    return Err(flag_error("--runner-policy", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--runner-policy=");
                if value.is_empty() {
                    return Err(flag_error("--runner-policy", UsageReason::MissingFlagValue)
                        .with_command("package verify-certs"));
                }
                runner_policy = Some(PathBuf::from(value));
                index += 1;
            }
            "--runner-policy-hash" => {
                if runner_policy_hash.is_some() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::DuplicateFlag)
                            .with_command("package verify-certs"),
                    );
                }
                let value =
                    flag_value(args, index, "--runner-policy-hash", "package verify-certs")?;
                runner_policy_hash = Some(value.to_owned());
                index += 2;
            }
            token if token.starts_with("--runner-policy-hash=") => {
                if runner_policy_hash.is_some() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::DuplicateFlag)
                            .with_command("package verify-certs"),
                    );
                }
                let value = token.trim_start_matches("--runner-policy-hash=");
                if value.is_empty() {
                    return Err(
                        flag_error("--runner-policy-hash", UsageReason::MissingFlagValue)
                            .with_command("package verify-certs"),
                    );
                }
                runner_policy_hash = Some(value.to_owned());
                index += 1;
            }
            "--checker-registry" => {
                if checker_registry.is_some() {
                    return Err(flag_error("--checker-registry", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = flag_value(args, index, "--checker-registry", "package verify-certs")?;
                checker_registry = Some(PathBuf::from(value));
                index += 2;
            }
            token if token.starts_with("--checker-registry=") => {
                if checker_registry.is_some() {
                    return Err(flag_error("--checker-registry", UsageReason::DuplicateFlag)
                        .with_command("package verify-certs"));
                }
                let value = token.trim_start_matches("--checker-registry=");
                if value.is_empty() {
                    return Err(
                        flag_error("--checker-registry", UsageReason::MissingFlagValue)
                            .with_command("package verify-certs"),
                    );
                }
                checker_registry = Some(PathBuf::from(value));
                index += 1;
            }
            token => {
                common_tokens.push(token.to_owned());
                index += 1;
            }
        }
    }

    let common = parse_common_options(
        &common_tokens,
        "package verify-certs",
        &[
            "--checker",
            "--runner-policy",
            "--runner-policy-hash",
            "--checker-registry",
            "--audit-cache",
            "--verifier-memo",
            "--jobs",
            "--timings",
        ],
    )?;
    let checker = checker.unwrap_or(PackageChecker::Reference);
    let audit_cache = audit_cache.unwrap_or(PackageAuditCacheMode::Off);
    let verifier_memo = verifier_memo.unwrap_or(PackageVerifierMemoMode::Off);
    let jobs = jobs.unwrap_or(1);
    let timings = timings.unwrap_or(PackageTimingMode::Off);
    if checker == PackageChecker::External && audit_cache.uses_local_store() {
        return Err(CliUsageError::new(UsageReason::UnsupportedFlag)
            .with_command("package verify-certs")
            .with_flag("--audit-cache")
            .with_value(audit_cache.as_str()));
    }
    if checker == PackageChecker::External && verifier_memo.uses_local_store() {
        return Err(CliUsageError::new(UsageReason::UnsupportedFlag)
            .with_command("package verify-certs")
            .with_flag("--verifier-memo")
            .with_value(verifier_memo.as_str()));
    }
    if audit_cache.uses_local_store() && verifier_memo.uses_local_store() {
        return Err(CliUsageError::new(UsageReason::UnsupportedFlag)
            .with_command("package verify-certs")
            .with_flag("--verifier-memo")
            .with_value(verifier_memo.as_str()));
    }
    let has_external_options =
        runner_policy.is_some() || runner_policy_hash.is_some() || checker_registry.is_some();
    let external = if checker == PackageChecker::External {
        Some(PackageExternalCheckerOptions {
            runner_policy: runner_policy.ok_or_else(|| {
                flag_error("--runner-policy", UsageReason::MissingRequiredFlag)
                    .with_command("package verify-certs")
            })?,
            runner_policy_hash: runner_policy_hash.ok_or_else(|| {
                flag_error("--runner-policy-hash", UsageReason::MissingRequiredFlag)
                    .with_command("package verify-certs")
            })?,
            checker_registry: checker_registry.ok_or_else(|| {
                flag_error("--checker-registry", UsageReason::MissingRequiredFlag)
                    .with_command("package verify-certs")
            })?,
        })
    } else {
        if has_external_options {
            let flag = if runner_policy.is_some() {
                "--runner-policy"
            } else if runner_policy_hash.is_some() {
                "--runner-policy-hash"
            } else {
                "--checker-registry"
            };
            return Err(
                flag_error(flag, UsageReason::UnsupportedFlag).with_command("package verify-certs")
            );
        }
        None
    };
    Ok(CliAction::Run(CliCommand::Package(
        PackageCommand::VerifyCerts(PackageVerifyCertsOptions {
            common,
            checker,
            audit_cache,
            verifier_memo,
            jobs,
            external,
            timings,
        }),
    )))
}

fn parse_checker(value: &str) -> Result<PackageChecker, CliUsageError> {
    match value {
        "reference" => Ok(PackageChecker::Reference),
        "fast" => Ok(PackageChecker::Fast),
        "external" => Ok(PackageChecker::External),
        other => Err(CliUsageError::new(UsageReason::UnsupportedChecker)
            .with_command("package verify-certs")
            .with_flag("--checker")
            .with_value(other)),
    }
}

fn parse_audit_cache_mode(value: &str) -> Result<PackageAuditCacheMode, CliUsageError> {
    match value {
        "off" => Ok(PackageAuditCacheMode::Off),
        "read-through" => Ok(PackageAuditCacheMode::ReadThrough),
        "local-hit" => Ok(PackageAuditCacheMode::LocalHit),
        other => Err(CliUsageError::new(UsageReason::UnsupportedAuditCacheMode)
            .with_command("package verify-certs")
            .with_flag("--audit-cache")
            .with_value(other)),
    }
}

fn parse_verifier_memo_mode(value: &str) -> Result<PackageVerifierMemoMode, CliUsageError> {
    match value {
        "off" => Ok(PackageVerifierMemoMode::Off),
        "read-through" => Ok(PackageVerifierMemoMode::ReadThrough),
        "disk" => Ok(PackageVerifierMemoMode::Disk),
        other => Err(CliUsageError::new(UsageReason::UnsupportedVerifierMemoMode)
            .with_command("package verify-certs")
            .with_flag("--verifier-memo")
            .with_value(other)),
    }
}

fn parse_timing_mode(
    value: &str,
    command: &'static str,
) -> Result<PackageTimingMode, CliUsageError> {
    match value {
        "off" => Ok(PackageTimingMode::Off),
        "summary" => Ok(PackageTimingMode::Summary),
        "detailed" => Ok(PackageTimingMode::Detailed),
        other => Err(CliUsageError::new(UsageReason::UnsupportedTimingMode)
            .with_command(command)
            .with_flag("--timings")
            .with_value(other)),
    }
}

fn parse_build_check_cache_mode(value: &str) -> Result<PackageBuildCheckCacheMode, CliUsageError> {
    match value {
        "off" => Ok(PackageBuildCheckCacheMode::Off),
        "read-through" => Ok(PackageBuildCheckCacheMode::ReadThrough),
        other => Err(
            CliUsageError::new(UsageReason::UnsupportedBuildCheckCacheMode)
                .with_command("package build-certs")
                .with_flag("--build-check-cache")
                .with_value(other),
        ),
    }
}

fn parse_jobs(value: &str) -> Result<usize, CliUsageError> {
    let Ok(jobs) = value.parse::<usize>() else {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package verify-certs")
            .with_flag("--jobs")
            .with_value(value));
    };
    if jobs == 0 {
        return Err(CliUsageError::new(UsageReason::InvalidFlagValue)
            .with_command("package verify-certs")
            .with_flag("--jobs")
            .with_value(value));
    }
    Ok(jobs)
}

fn parse_path_flag(
    args: &[String],
    index: &mut usize,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<PathBuf>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let value = flag_value(args, *index, flag, command)?;
    *target = Some(PathBuf::from(value));
    *index += 2;
    Ok(())
}

fn parse_path_equals_flag(
    token: &str,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<PathBuf>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let prefix = format!("{flag}=");
    let value = token.trim_start_matches(&prefix);
    if value.is_empty() {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    *target = Some(PathBuf::from(value));
    Ok(())
}

fn parse_string_flag(
    args: &[String],
    index: &mut usize,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<String>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let value = flag_value(args, *index, flag, command)?;
    *target = Some(value.to_owned());
    *index += 2;
    Ok(())
}

fn parse_string_equals_flag(
    token: &str,
    flag: &'static str,
    command: &'static str,
    target: &mut Option<String>,
) -> Result<(), CliUsageError> {
    if target.is_some() {
        return Err(flag_error(flag, UsageReason::DuplicateFlag).with_command(command));
    }
    let prefix = format!("{flag}=");
    let value = token.trim_start_matches(&prefix);
    if value.is_empty() {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    *target = Some(value.to_owned());
    Ok(())
}

fn parse_common_options(
    args: &[String],
    command: &'static str,
    command_flags: &[&str],
) -> Result<PackageCommonOptions, CliUsageError> {
    let mut common = PackageCommonOptions::default();
    let mut root_seen = false;
    let mut json_seen = false;
    let mut index = 0usize;

    while index < args.len() {
        match args[index].as_str() {
            "--root" => {
                if root_seen {
                    return Err(
                        flag_error("--root", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = flag_value(args, index, "--root", command)?;
                common.root = PathBuf::from(value);
                root_seen = true;
                index += 2;
            }
            token if token.starts_with("--root=") => {
                if root_seen {
                    return Err(
                        flag_error("--root", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                let value = token.trim_start_matches("--root=");
                if value.is_empty() {
                    return Err(
                        flag_error("--root", UsageReason::MissingFlagValue).with_command(command)
                    );
                }
                common.root = PathBuf::from(value);
                root_seen = true;
                index += 1;
            }
            "--json" => {
                if json_seen {
                    return Err(
                        flag_error("--json", UsageReason::DuplicateFlag).with_command(command)
                    );
                }
                common.json = true;
                json_seen = true;
                index += 1;
            }
            flag if is_unsupported_clr04_flag(flag) || command_flags.contains(&flag) => {
                return Err(flag_error(flag, UsageReason::UnsupportedFlag).with_command(command));
            }
            flag if flag.starts_with('-') => {
                return Err(flag_error(flag, UsageReason::UnknownFlag).with_command(command));
            }
            value => {
                return Err(CliUsageError::new(UsageReason::UnknownCommand)
                    .with_command(format!("{command} {value}")));
            }
        }
    }

    Ok(common)
}

fn flag_value<'a>(
    args: &'a [String],
    index: usize,
    flag: &'static str,
    command: &'static str,
) -> Result<&'a str, CliUsageError> {
    let value = args
        .get(index + 1)
        .ok_or_else(|| flag_error(flag, UsageReason::MissingFlagValue).with_command(command))?;
    if value.starts_with('-') {
        return Err(flag_error(flag, UsageReason::MissingFlagValue).with_command(command));
    }
    Ok(value)
}

fn flag_error(flag: impl Into<String>, reason: UsageReason) -> CliUsageError {
    CliUsageError::new(reason).with_flag(flag)
}

fn contains_help(args: &[String]) -> bool {
    args.iter()
        .any(|argument| argument == "--help" || argument == "-h")
}

fn is_unsupported_clr04_flag(flag: &str) -> bool {
    matches!(
        flag,
        "--changed"
            | "--all"
            | "--registry"
            | "--network"
            | "--latest"
            | "--runner-policy"
            | "--runner-policy-hash"
            | "--checker-registry"
            | "--upload"
            | "--sign"
            | "--update-manifest-hashes"
            | "--include-source"
            | "--include-replay"
            | "--include-ai-traces"
            | "--checker"
            | "--audit-cache"
            | "--verifier-memo"
            | "--build-check-cache"
            | "--jobs"
            | "--timings"
            | "--base"
    ) || flag.starts_with("--changed=")
        || flag.starts_with("--all=")
        || flag.starts_with("--registry=")
        || flag.starts_with("--network=")
        || flag.starts_with("--latest=")
        || flag.starts_with("--runner-policy=")
        || flag.starts_with("--runner-policy-hash=")
        || flag.starts_with("--checker-registry=")
        || flag.starts_with("--upload=")
        || flag.starts_with("--sign=")
        || flag.starts_with("--update-manifest-hashes=")
        || flag.starts_with("--include-source=")
        || flag.starts_with("--include-replay=")
        || flag.starts_with("--include-ai-traces=")
        || flag.starts_with("--checker=")
        || flag.starts_with("--audit-cache=")
        || flag.starts_with("--verifier-memo=")
        || flag.starts_with("--build-check-cache=")
        || flag.starts_with("--jobs=")
        || flag.starts_with("--timings=")
        || flag.starts_with("--base=")
}

/// Render deterministic help text.
pub fn render_help(topic: HelpTopic) -> &'static str {
    match topic {
        HelpTopic::Root => {
            "Usage: npa <command> [options]\n\nCommands:\n  package    Package manifest and certificate commands\n  version    Print npa CLI version\n\nOptions:\n  --help\n  --version"
        }
        HelpTopic::Package => {
            "Usage: npa package <command> [options]\n\nCommands:\n  check\n  build-certs\n  axiom-report\n  index\n  export-summary\n  verify-certs\n  check-hashes\n  publish-plan\n  check-generated\n  high-trust\n  gate-plan\n\nCommon options:\n  --root PATH    Package root, default: .\n  --json         Emit deterministic JSON diagnostics\n  --help         Show help"
        }
        HelpTopic::PackageCheck => {
            "Usage: npa package check [--root PATH] [--json]\n\nValidate npa-package.toml metadata without reading source or certificate artifacts."
        }
        HelpTopic::PackageBuildCerts => {
            "Usage: npa package build-certs [--root PATH] [--json] [--check] [--build-check-cache off|read-through]\n\nRebuild package certificates. --check writes no files; write mode updates local certificates and generated/package-lock.json. read-through still runs live source-to-certificate comparison and only records untrusted local cache counters."
        }
        HelpTopic::PackageAxiomReport => {
            "Usage: npa package axiom-report [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/axiom-report.json from source-free package certificate artifacts. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageIndex => {
            "Usage: npa package index [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/theorem-index.json from source-free package certificate artifacts. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageExportSummary => {
            "Usage: npa package export-summary [--root PATH] [--json] [--check] [--out PATH] [--timings off|summary|detailed]\n\nGenerate or check generated/verified-export-summary.json from source-free package certificate artifacts. The summary and timing telemetry are not proof evidence."
        }
        HelpTopic::PackageVerifyCerts => {
            "Usage: npa package verify-certs [--root PATH] [--json] [--checker reference|fast|external] [--audit-cache off|read-through|local-hit] [--verifier-memo off|read-through|disk] [--jobs N] [--timings off|summary|detailed] [--runner-policy PATH --runner-policy-hash HASH --checker-registry PATH]\n\nVerify certificates through the source-free package verifier. The default checker is reference, the default audit cache mode is off, the default verifier memo mode is off, the default jobs value is 1, and timings default to off. read-through audit cache and verifier memo modes still run live verification; local-hit and disk verifier memo hits are local-only acceleration and are not proof evidence; timing telemetry is informational and is not proof evidence; external mode requires explicit runner policy and checker registry inputs and does not support audit-cache or verifier-memo acceleration."
        }
        HelpTopic::PackageCheckHashes => {
            "Usage: npa package check-hashes [--root PATH] [--json]\n\nCheck checked-in package artifact hashes."
        }
        HelpTopic::PackagePublishPlan => {
            "Usage: npa package publish-plan [--root PATH] [--json] [--check] [--timings off|summary|detailed]\n\nGenerate or check generated/publish-plan.json from source-free package release metadata. Timing telemetry is informational and is not proof evidence."
        }
        HelpTopic::PackageCheckGenerated => {
            "Usage: npa package check-generated [--root PATH] [--json] [--timings off|summary|detailed]\n\nCheck generated axiom report, theorem index, verified export summary, publish plan, and fast certificate verification from one source-free package snapshot. This local aggregate command is not proof evidence."
        }
        HelpTopic::PackageHighTrust => {
            "Usage: npa package high-trust [--root PATH] [--json] --release-policy PATH --release-policy-hash HASH --runner-policy PATH --runner-policy-hash HASH --challenge-runner-policy PATH --challenge-runner-policy-hash HASH --checker-registry PATH [--out PATH] [--check]\n\nGenerate or check verified_high_trust release evidence after external and high-trust-reference gates pass. The artifact is release evidence, not checker input."
        }
        HelpTopic::PackageGatePlan => {
            "Usage: npa package gate-plan [--root PATH] [--json] --base REF\n\nRecommend the cheapest sufficient package gate commands from git diff --name-only REF...HEAD. The planner runs no gates and is not proof evidence."
        }
    }
}
