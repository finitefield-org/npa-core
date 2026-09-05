//! Bounded, opt-in authoring diagnostics for kernel conversion failures.

use std::collections::BTreeMap;

use crate::{
    work::{KernelFuelOperationCounters, KernelFuelTotals, KernelWorkSnapshot},
    Error, Expr,
};

pub const KERNEL_COMPARISON_PATH_PREFIX_LIMIT: usize = 32;
pub const KERNEL_COMPARISON_PATH_SUFFIX_LIMIT: usize = 32;
pub const KERNEL_COMPARISON_PATH_LIMIT: usize =
    KERNEL_COMPARISON_PATH_PREFIX_LIMIT + KERNEL_COMPARISON_PATH_SUFFIX_LIMIT;
pub const KERNEL_DELTA_HOTSET_CAPACITY: usize = 256;
pub const KERNEL_DELTA_NAME_BYTE_LIMIT: usize = 256;
pub const KERNEL_DELTA_HOTSET_ENTRY_LIMIT: usize = 16;
pub const KERNEL_DELTA_OVERLONG_NAME: &str = "<overlong-name>";

/// Kernel-owned fuel-report selection, independent of execution options.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum KernelFuelReportMode {
    /// Do not collect fuel-report-specific state.
    #[default]
    Off,
    /// Collect failure-local scalar work and structural paths.
    Failure,
    /// Also collect bounded declaration-local delta-constant counts.
    Detailed,
}

impl KernelFuelReportMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Failure => "failure",
            Self::Detailed => "detailed",
        }
    }

    pub const fn collects_failures(self) -> bool {
        matches!(self, Self::Failure | Self::Detailed)
    }

    pub const fn collects_delta_names(self) -> bool {
        matches!(self, Self::Detailed)
    }
}

/// Declaration-local operational diagnostic options.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelDiagnosticOptions {
    pub fuel_report: KernelFuelReportMode,
}

/// Successful diagnosed admission data retained only by the requested mode.
#[non_exhaustive]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KernelDiagnosedAdmission {
    declaration_work: Option<KernelDeclarationWork>,
    retained_delta_constants: Option<KernelDeltaHotsetSummary>,
}

impl KernelDiagnosedAdmission {
    pub(crate) fn from_success(
        mode: KernelFuelReportMode,
        declaration_work: KernelDeclarationWork,
        retained_delta_constants: Option<KernelDeltaHotsetSummary>,
    ) -> Self {
        if mode.collects_delta_names() {
            Self {
                declaration_work: Some(declaration_work),
                retained_delta_constants: Some(
                    retained_delta_constants.unwrap_or_else(KernelDeltaHotsetSummary::empty),
                ),
            }
        } else {
            Self::default()
        }
    }

    pub fn declaration_work(&self) -> Option<&KernelDeclarationWork> {
        self.declaration_work.as_ref()
    }

    pub fn retained_delta_constants(&self) -> Option<&KernelDeltaHotsetSummary> {
        self.retained_delta_constants.as_ref()
    }
}

/// Stable subsystem identity for a kernel fuel report.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelDiagnosticSubsystem {
    FastKernel,
}

impl KernelDiagnosticSubsystem {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FastKernel => "fast_kernel",
        }
    }
}

/// Fuel domain whose operation exhausted.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelFuelResource {
    Conversion,
    Whnf,
}

impl KernelFuelResource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Conversion => "conversion",
            Self::Whnf => "whnf",
        }
    }
}

/// One stable branch in a bounded structural comparison path.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelComparisonPathStep {
    AppFunction,
    AppArgument,
    PiDomain,
    PiBody,
    LambdaDomain,
    LambdaBody,
    WhnfLeft,
    WhnfRight,
}

impl KernelComparisonPathStep {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AppFunction => "app_function",
            Self::AppArgument => "app_argument",
            Self::PiDomain => "pi_domain",
            Self::PiBody => "pi_body",
            Self::LambdaDomain => "lambda_domain",
            Self::LambdaBody => "lambda_body",
            Self::WhnfLeft => "whnf_left",
            Self::WhnfRight => "whnf_right",
        }
    }
}

/// Materialized bounded structural path for one retained comparison.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KernelComparisonPath {
    pub steps: Vec<KernelComparisonPathStep>,
    pub truncated: bool,
}

impl KernelComparisonPath {
    pub fn empty() -> Self {
        Self::default()
    }
}

/// Failed-operation fuel and bounded work delta.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelOperationWork {
    pub fuel: KernelFuelOperationCounters,
    pub work: KernelWorkSnapshot,
}

/// Declaration-scope fuel and bounded work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelDeclarationWork {
    pub fuel: KernelFuelTotals,
    pub work: KernelWorkSnapshot,
    pub overflowed: bool,
}

impl KernelDeclarationWork {
    pub fn from_snapshot(work: KernelWorkSnapshot) -> Self {
        let fuel = work.fuel;
        let overflowed = work.overflowed || fuel.whnf.overflowed || fuel.conversion.overflowed;
        Self {
            fuel,
            work,
            overflowed,
        }
    }
}

/// One retained delta-constant count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelDeltaHotsetEntry {
    pub constant: String,
    pub count: u64,
}

/// Canonical bounded projection of the declaration-local delta collector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelDeltaHotsetSummary {
    pub retained_names: u64,
    pub capacity: u64,
    pub entries: Vec<KernelDeltaHotsetEntry>,
    pub emitted: u64,
    pub entry_limit: u64,
    pub unretained_name_observations: u64,
    pub overlong_name_observations: u64,
    pub output_truncated: bool,
    pub overflowed: bool,
}

impl KernelDeltaHotsetSummary {
    pub fn empty() -> Self {
        Self {
            retained_names: 0,
            capacity: KERNEL_DELTA_HOTSET_CAPACITY as u64,
            entries: Vec::new(),
            emitted: 0,
            entry_limit: KERNEL_DELTA_HOTSET_ENTRY_LIMIT as u64,
            unretained_name_observations: 0,
            overlong_name_observations: 0,
            output_truncated: false,
            overflowed: false,
        }
    }
}

/// Bounded operational context for one fast-kernel fuel exhaustion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelFuelDiagnostic {
    pub subsystem: KernelDiagnosticSubsystem,
    pub resource: KernelFuelResource,
    pub failed_operation: KernelOperationWork,
    pub declaration: KernelDeclarationWork,
    pub comparison_path: KernelComparisonPath,
    pub retained_delta_constants: Option<KernelDeltaHotsetSummary>,
    pub overflowed: bool,
}

impl KernelFuelDiagnostic {
    pub fn new(
        resource: KernelFuelResource,
        failed_operation: KernelOperationWork,
        declaration: KernelDeclarationWork,
        comparison_path: KernelComparisonPath,
        retained_delta_constants: Option<KernelDeltaHotsetSummary>,
    ) -> Self {
        let overflowed = failed_operation.fuel.overflowed
            || failed_operation.work.overflowed
            || declaration.overflowed
            || retained_delta_constants
                .as_ref()
                .is_some_and(|summary| summary.overflowed);
        Self {
            subsystem: KernelDiagnosticSubsystem::FastKernel,
            resource,
            failed_operation,
            declaration,
            comparison_path,
            retained_delta_constants,
            overflowed,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct KernelDeltaHotset {
    counts: BTreeMap<String, u64>,
    unretained_name_observations: u64,
    overlong_name_observations: u64,
    overflowed: bool,
}

impl KernelDeltaHotset {
    pub(crate) fn for_mode(mode: KernelFuelReportMode) -> Option<Self> {
        mode.collects_delta_names().then(Self::default)
    }

    pub(crate) fn record(&mut self, constant: &str) {
        if constant.len() > KERNEL_DELTA_NAME_BYTE_LIMIT {
            saturating_increment(&mut self.overlong_name_observations, &mut self.overflowed);
            return;
        }
        if let Some(count) = self.counts.get_mut(constant) {
            saturating_increment(count, &mut self.overflowed);
            return;
        }
        if self.counts.len() < KERNEL_DELTA_HOTSET_CAPACITY {
            self.counts.insert(constant.to_owned(), 1);
        } else {
            saturating_increment(&mut self.unretained_name_observations, &mut self.overflowed);
        }
    }

    pub(crate) fn summary(&self) -> KernelDeltaHotsetSummary {
        let mut entries = self
            .counts
            .iter()
            .map(|(constant, count)| KernelDeltaHotsetEntry {
                constant: constant.clone(),
                count: *count,
            })
            .collect::<Vec<_>>();
        if self.overlong_name_observations > 0 {
            entries.push(KernelDeltaHotsetEntry {
                constant: KERNEL_DELTA_OVERLONG_NAME.to_owned(),
                count: self.overlong_name_observations,
            });
        }
        entries.sort_by(|left, right| {
            right
                .count
                .cmp(&left.count)
                .then_with(|| left.constant.cmp(&right.constant))
        });
        entries.truncate(KERNEL_DELTA_HOTSET_ENTRY_LIMIT);

        let retained_names = self.counts.len() as u64;
        let emitted = entries.len() as u64;
        let candidate_count = retained_names + u64::from(self.overlong_name_observations > 0);
        KernelDeltaHotsetSummary {
            retained_names,
            capacity: KERNEL_DELTA_HOTSET_CAPACITY as u64,
            entries,
            emitted,
            entry_limit: KERNEL_DELTA_HOTSET_ENTRY_LIMIT as u64,
            unretained_name_observations: self.unretained_name_observations,
            overlong_name_observations: self.overlong_name_observations,
            output_truncated: emitted < candidate_count,
            overflowed: self.overflowed,
        }
    }
}

fn saturating_increment(value: &mut u64, overflowed: &mut bool) {
    if *value == u64::MAX {
        *overflowed = true;
    } else {
        *value += 1;
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct KernelComparisonPathRestoreToken {
    depth: usize,
    overwritten_suffix: Option<(usize, KernelComparisonPathStep)>,
}

#[derive(Clone, Debug)]
pub(crate) struct KernelComparisonPathRecorder {
    prefix: [KernelComparisonPathStep; KERNEL_COMPARISON_PATH_PREFIX_LIMIT],
    suffix: [KernelComparisonPathStep; KERNEL_COMPARISON_PATH_SUFFIX_LIMIT],
    depth: usize,
}

impl Default for KernelComparisonPathRecorder {
    fn default() -> Self {
        Self {
            prefix: [KernelComparisonPathStep::AppFunction; KERNEL_COMPARISON_PATH_PREFIX_LIMIT],
            suffix: [KernelComparisonPathStep::AppFunction; KERNEL_COMPARISON_PATH_SUFFIX_LIMIT],
            depth: 0,
        }
    }
}

impl KernelComparisonPathRecorder {
    pub(crate) fn push(
        &mut self,
        step: KernelComparisonPathStep,
    ) -> KernelComparisonPathRestoreToken {
        let depth = self.depth;
        let overwritten_suffix = if depth < KERNEL_COMPARISON_PATH_PREFIX_LIMIT {
            self.prefix[depth] = step;
            None
        } else {
            let slot = depth % KERNEL_COMPARISON_PATH_SUFFIX_LIMIT;
            let overwritten = self.suffix[slot];
            self.suffix[slot] = step;
            Some((slot, overwritten))
        };
        self.depth = self.depth.saturating_add(1);
        KernelComparisonPathRestoreToken {
            depth,
            overwritten_suffix,
        }
    }

    pub(crate) fn pop(&mut self, token: KernelComparisonPathRestoreToken) {
        debug_assert_eq!(self.depth, token.depth.saturating_add(1));
        if let Some((slot, overwritten)) = token.overwritten_suffix {
            self.suffix[slot] = overwritten;
        }
        self.depth = token.depth;
    }

    pub(crate) fn materialize(&self) -> KernelComparisonPath {
        let mut steps = Vec::with_capacity(self.depth.min(KERNEL_COMPARISON_PATH_LIMIT));
        let prefix_len = self.depth.min(KERNEL_COMPARISON_PATH_PREFIX_LIMIT);
        steps.extend_from_slice(&self.prefix[..prefix_len]);
        if self.depth > KERNEL_COMPARISON_PATH_PREFIX_LIMIT {
            let suffix_start = if self.depth <= KERNEL_COMPARISON_PATH_LIMIT {
                KERNEL_COMPARISON_PATH_PREFIX_LIMIT
            } else {
                self.depth - KERNEL_COMPARISON_PATH_SUFFIX_LIMIT
            };
            for index in suffix_start..self.depth {
                steps.push(self.suffix[index % KERNEL_COMPARISON_PATH_SUFFIX_LIMIT]);
            }
        }
        KernelComparisonPath {
            steps,
            truncated: self.depth > KERNEL_COMPARISON_PATH_LIMIT,
        }
    }
}

#[derive(Default)]
pub(crate) struct KernelConversionRecorder {
    comparison: Option<KernelConversionContext>,
    comparison_path: Option<KernelComparisonPath>,
    path: Option<KernelComparisonPathRecorder>,
}

impl KernelConversionRecorder {
    pub(crate) fn with_path() -> Self {
        Self {
            path: Some(KernelComparisonPathRecorder::default()),
            ..Self::default()
        }
    }

    pub(crate) fn push_path(
        &mut self,
        step: KernelComparisonPathStep,
    ) -> Option<KernelComparisonPathRestoreToken> {
        self.path.as_mut().map(|path| path.push(step))
    }

    pub(crate) fn pop_path(&mut self, token: Option<KernelComparisonPathRestoreToken>) {
        if let (Some(path), Some(token)) = (&mut self.path, token) {
            path.pop(token);
        }
    }

    pub(crate) fn record(
        &mut self,
        outcome: KernelComparisonOutcome,
        lhs: &Expr,
        rhs: &Expr,
        depth: u32,
    ) {
        let replace = self.comparison.as_ref().is_none_or(|current| {
            depth > current.depth()
                || (depth == current.depth()
                    && outcome == KernelComparisonOutcome::FuelExhausted
                    && current.outcome() == KernelComparisonOutcome::NotDefEq)
        });
        if replace {
            self.comparison = Some(KernelConversionContext::new(
                outcome,
                KernelExprHead::from_expr(lhs),
                KernelExprHead::from_expr(rhs),
                depth,
            ));
            self.comparison_path = self
                .path
                .as_ref()
                .map(KernelComparisonPathRecorder::materialize);
        }
    }

    pub(crate) fn into_observation(
        self,
    ) -> Option<(KernelConversionContext, KernelComparisonPath)> {
        self.comparison.map(|comparison| {
            (
                comparison,
                self.comparison_path
                    .unwrap_or_else(KernelComparisonPath::empty),
            )
        })
    }
}

/// Kernel failure plus optional bounded authoring context.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosedKernelError {
    error: Box<Error>,
    context: Option<KernelDiagnosticContext>,
}

impl DiagnosedKernelError {
    /// Build a diagnosed error without additional context.
    pub fn new(error: Error) -> Self {
        Self {
            error: Box::new(error),
            context: None,
        }
    }

    /// Attach bounded diagnostic context.
    #[must_use]
    pub fn with_context(mut self, context: KernelDiagnosticContext) -> Self {
        self.context = Some(context);
        self
    }

    /// Return the unchanged kernel error.
    pub fn error(&self) -> &Error {
        &self.error
    }

    /// Consume the wrapper and return the unchanged kernel error.
    pub fn into_error(self) -> Error {
        *self.error
    }

    /// Return bounded authoring context when recorded.
    pub fn context(&self) -> Option<&KernelDiagnosticContext> {
        self.context.as_ref()
    }
}

/// Bounded context for one kernel checking phase.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelDiagnosticContext {
    phase: KernelDiagnosticPhase,
    conversion: Option<KernelConversionContext>,
    kernel_fuel: Option<KernelFuelDiagnostic>,
}

impl KernelDiagnosticContext {
    /// Build context for a phase with no conversion record.
    pub fn new(phase: KernelDiagnosticPhase) -> Self {
        Self {
            phase,
            conversion: None,
            kernel_fuel: None,
        }
    }

    /// Attach one bounded conversion record.
    #[must_use]
    pub fn with_conversion(mut self, conversion: KernelConversionContext) -> Self {
        self.conversion = Some(conversion);
        self
    }

    /// Attach one bounded operational fuel report.
    #[must_use]
    pub fn with_kernel_fuel(mut self, kernel_fuel: KernelFuelDiagnostic) -> Self {
        self.kernel_fuel = Some(kernel_fuel);
        self
    }

    /// Return the checking phase.
    pub const fn phase(&self) -> KernelDiagnosticPhase {
        self.phase
    }

    /// Return the conversion record when available.
    pub fn conversion(&self) -> Option<&KernelConversionContext> {
        self.conversion.as_ref()
    }

    /// Return the fuel report when a fast-kernel resource operation exhausted.
    pub fn kernel_fuel(&self) -> Option<&KernelFuelDiagnostic> {
        self.kernel_fuel.as_ref()
    }
}

/// Stable phase for a bounded authoring diagnostic.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelDiagnosticPhase {
    /// Term checking against an expected type.
    TermCheck,
    /// Declaration type checking.
    DeclarationType,
    /// Declaration value or proof checking.
    DeclarationValue,
    /// Inductive constructor checking.
    InductiveConstructor,
    /// Inductive recursor checking.
    InductiveRecursor,
    /// A conversion with no narrower phase.
    DefinitionalEquality,
}

impl KernelDiagnosticPhase {
    /// Stable output spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TermCheck => "term_check",
            Self::DeclarationType => "declaration_type",
            Self::DeclarationValue => "declaration_value",
            Self::InductiveConstructor => "inductive_constructor",
            Self::InductiveRecursor => "inductive_recursor",
            Self::DefinitionalEquality => "definitional_equality",
        }
    }
}

/// Stable conversion outcome.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelComparisonOutcome {
    /// Compared expressions were not definitionally equal.
    NotDefEq,
    /// Conversion fuel was exhausted at the recorded comparison.
    FuelExhausted,
}

impl KernelComparisonOutcome {
    /// Stable output spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotDefEq => "not_defeq",
            Self::FuelExhausted => "fuel_exhausted",
        }
    }
}

/// Bounded expression head label.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelExprHead {
    /// Universe sort.
    Sort,
    /// Bound variable.
    BoundVariable,
    /// Named constant, capped by `from_expr`.
    Constant(String),
    /// Function application.
    Application,
    /// Lambda abstraction.
    Lambda,
    /// Dependent function type.
    Pi,
    /// Unavailable or deliberately omitted head.
    Unknown,
}

impl KernelExprHead {
    /// Derive a bounded head without rendering the complete expression.
    pub fn from_expr(expression: &Expr) -> Self {
        match expression {
            Expr::Sort(_) => Self::Sort,
            Expr::BVar(_) => Self::BoundVariable,
            Expr::Const { name, .. } if name.len() <= 256 => Self::Constant(name.clone()),
            Expr::Const { .. } => Self::Constant("<truncated>".to_owned()),
            Expr::App(..) => Self::Application,
            Expr::Lam { .. } => Self::Lambda,
            Expr::Pi { .. } => Self::Pi,
        }
    }

    /// Stable bounded output spelling.
    pub fn as_str(&self) -> String {
        match self {
            Self::Sort => "sort".to_owned(),
            Self::BoundVariable => "bound_variable".to_owned(),
            Self::Constant(name) => format!("constant:{name}"),
            Self::Application => "application".to_owned(),
            Self::Lambda => "lambda".to_owned(),
            Self::Pi => "pi".to_owned(),
            Self::Unknown => "unknown".to_owned(),
        }
    }
}

/// One deepest bounded conversion comparison.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelConversionContext {
    outcome: KernelComparisonOutcome,
    lhs_head: KernelExprHead,
    rhs_head: KernelExprHead,
    depth: u32,
}

impl KernelConversionContext {
    /// Build a bounded comparison record.
    pub fn new(
        outcome: KernelComparisonOutcome,
        lhs_head: KernelExprHead,
        rhs_head: KernelExprHead,
        depth: u32,
    ) -> Self {
        Self {
            outcome,
            lhs_head,
            rhs_head,
            depth,
        }
    }

    /// Return the comparison outcome.
    pub const fn outcome(&self) -> KernelComparisonOutcome {
        self.outcome
    }

    /// Return the left expression head.
    pub fn lhs_head(&self) -> &KernelExprHead {
        &self.lhs_head
    }

    /// Return the right expression head.
    pub fn rhs_head(&self) -> &KernelExprHead {
        &self.rhs_head
    }

    /// Return conversion recursion depth.
    pub const fn depth(&self) -> u32 {
        self.depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Level;

    fn path_step(index: usize) -> KernelComparisonPathStep {
        const STEPS: [KernelComparisonPathStep; 8] = [
            KernelComparisonPathStep::AppFunction,
            KernelComparisonPathStep::AppArgument,
            KernelComparisonPathStep::PiDomain,
            KernelComparisonPathStep::PiBody,
            KernelComparisonPathStep::LambdaDomain,
            KernelComparisonPathStep::LambdaBody,
            KernelComparisonPathStep::WhnfLeft,
            KernelComparisonPathStep::WhnfRight,
        ];
        STEPS[index % STEPS.len()]
    }

    fn empty_declaration_work() -> KernelDeclarationWork {
        KernelDeclarationWork::from_snapshot(KernelWorkSnapshot::zero())
    }

    fn empty_diagnostic(resource: KernelFuelResource) -> KernelFuelDiagnostic {
        KernelFuelDiagnostic::new(
            resource,
            KernelOperationWork {
                fuel: KernelFuelOperationCounters::default(),
                work: KernelWorkSnapshot::zero(),
            },
            empty_declaration_work(),
            KernelComparisonPath::empty(),
            None,
        )
    }

    #[test]
    fn diagnostic_modes_have_stable_spellings_and_off_default() {
        assert_eq!(
            KernelDiagnosticOptions::default().fuel_report,
            KernelFuelReportMode::Off
        );
        assert_eq!(KernelFuelReportMode::Off.as_str(), "off");
        assert_eq!(KernelFuelReportMode::Failure.as_str(), "failure");
        assert_eq!(KernelFuelReportMode::Detailed.as_str(), "detailed");
        assert!(!KernelFuelReportMode::Off.collects_failures());
        assert!(KernelFuelReportMode::Failure.collects_failures());
        assert!(!KernelFuelReportMode::Failure.collects_delta_names());
        assert!(KernelFuelReportMode::Detailed.collects_delta_names());
    }

    #[test]
    fn detailed_success_has_present_empty_hotset_while_other_modes_have_no_summary() {
        let off = KernelDiagnosedAdmission::from_success(
            KernelFuelReportMode::Off,
            empty_declaration_work(),
            None,
        );
        let failure = KernelDiagnosedAdmission::from_success(
            KernelFuelReportMode::Failure,
            empty_declaration_work(),
            None,
        );
        let detailed = KernelDiagnosedAdmission::from_success(
            KernelFuelReportMode::Detailed,
            empty_declaration_work(),
            None,
        );

        assert!(off.declaration_work().is_none());
        assert!(off.retained_delta_constants().is_none());
        assert!(failure.declaration_work().is_none());
        assert!(failure.retained_delta_constants().is_none());
        assert!(detailed.declaration_work().is_some());
        assert_eq!(
            detailed.retained_delta_constants(),
            Some(&KernelDeltaHotsetSummary::empty())
        );
    }

    #[test]
    fn diagnostic_context_carries_fuel_without_changing_the_kernel_error() {
        let diagnostic = empty_diagnostic(KernelFuelResource::Whnf);
        let context = KernelDiagnosticContext::new(KernelDiagnosticPhase::TermCheck)
            .with_kernel_fuel(diagnostic.clone());
        let error = DiagnosedKernelError::new(Error::ResourceLimit {
            kind: crate::ResourceLimitKind::Whnf,
        })
        .with_context(context);

        assert!(matches!(
            error.error(),
            Error::ResourceLimit {
                kind: crate::ResourceLimitKind::Whnf
            }
        ));
        assert_eq!(error.context().unwrap().kernel_fuel(), Some(&diagnostic));
        assert!(error.context().unwrap().conversion().is_none());
    }

    #[test]
    fn path_step_spellings_are_fixed() {
        assert_eq!(
            KernelDiagnosticSubsystem::FastKernel.as_str(),
            "fast_kernel"
        );
        assert_eq!(KernelFuelResource::Conversion.as_str(), "conversion");
        assert_eq!(KernelFuelResource::Whnf.as_str(), "whnf");
        assert_eq!(
            KernelComparisonPathStep::AppFunction.as_str(),
            "app_function"
        );
        assert_eq!(
            KernelComparisonPathStep::AppArgument.as_str(),
            "app_argument"
        );
        assert_eq!(KernelComparisonPathStep::PiDomain.as_str(), "pi_domain");
        assert_eq!(KernelComparisonPathStep::PiBody.as_str(), "pi_body");
        assert_eq!(
            KernelComparisonPathStep::LambdaDomain.as_str(),
            "lambda_domain"
        );
        assert_eq!(KernelComparisonPathStep::LambdaBody.as_str(), "lambda_body");
        assert_eq!(KernelComparisonPathStep::WhnfLeft.as_str(), "whnf_left");
        assert_eq!(KernelComparisonPathStep::WhnfRight.as_str(), "whnf_right");
    }

    #[test]
    fn fixed_path_recorder_keeps_exact_64_then_restores_after_a_deep_branch() {
        let mut recorder = KernelComparisonPathRecorder::default();
        let mut tokens = Vec::new();
        for index in 0..70 {
            tokens.push(recorder.push(path_step(index)));
            if index + 1 == KERNEL_COMPARISON_PATH_LIMIT {
                let exact = recorder.materialize();
                assert!(!exact.truncated);
                assert_eq!(exact.steps, (0..64).map(path_step).collect::<Vec<_>>());
            }
        }

        let deep = recorder.materialize();
        assert!(deep.truncated);
        assert_eq!(deep.steps.len(), KERNEL_COMPARISON_PATH_LIMIT);
        assert_eq!(deep.steps[..32], (0..32).map(path_step).collect::<Vec<_>>());
        assert_eq!(
            deep.steps[32..],
            (38..70).map(path_step).collect::<Vec<_>>()
        );

        for token in tokens.into_iter().rev() {
            recorder.pop(token);
        }
        let first = recorder.push(KernelComparisonPathStep::LambdaBody);
        let second = recorder.push(KernelComparisonPathStep::WhnfRight);
        assert_eq!(
            recorder.materialize(),
            KernelComparisonPath {
                steps: vec![
                    KernelComparisonPathStep::LambdaBody,
                    KernelComparisonPathStep::WhnfRight,
                ],
                truncated: false,
            }
        );
        recorder.pop(second);
        recorder.pop(first);
        assert_eq!(recorder.materialize(), KernelComparisonPath::empty());
    }

    #[test]
    fn conversion_recorder_preserves_deepest_and_equal_depth_exhaustion_precedence() {
        let lhs = Expr::sort(Level::zero());
        let rhs = Expr::bvar(0);
        let mut recorder = KernelConversionRecorder::with_path();
        let outer = recorder.push_path(KernelComparisonPathStep::AppFunction);
        recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, 1);
        let inner = recorder.push_path(KernelComparisonPathStep::AppArgument);
        recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, 2);
        recorder.pop_path(inner);
        let sibling = recorder.push_path(KernelComparisonPathStep::WhnfLeft);
        recorder.record(KernelComparisonOutcome::FuelExhausted, &lhs, &rhs, 1);
        recorder.pop_path(sibling);
        recorder.pop_path(outer);
        let (comparison, path) = recorder.into_observation().unwrap();
        assert_eq!(comparison.outcome(), KernelComparisonOutcome::NotDefEq);
        assert_eq!(comparison.depth(), 2);
        assert_eq!(
            path.steps,
            vec![
                KernelComparisonPathStep::AppFunction,
                KernelComparisonPathStep::AppArgument,
            ]
        );

        let mut recorder = KernelConversionRecorder::with_path();
        let first = recorder.push_path(KernelComparisonPathStep::PiDomain);
        recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, 1);
        recorder.pop_path(first);
        let winning = recorder.push_path(KernelComparisonPathStep::PiBody);
        recorder.record(KernelComparisonOutcome::FuelExhausted, &lhs, &rhs, 1);
        recorder.pop_path(winning);
        let later = recorder.push_path(KernelComparisonPathStep::WhnfRight);
        recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, 1);
        recorder.pop_path(later);
        let (comparison, path) = recorder.into_observation().unwrap();
        assert_eq!(comparison.outcome(), KernelComparisonOutcome::FuelExhausted);
        assert_eq!(path.steps, vec![KernelComparisonPathStep::PiBody]);
    }

    #[test]
    fn default_conversion_recorder_keeps_path_collection_disabled() {
        let lhs = Expr::sort(Level::zero());
        let rhs = Expr::bvar(0);
        let mut recorder = KernelConversionRecorder::default();

        assert!(!std::mem::needs_drop::<KernelComparisonPathRecorder>());
        assert!(recorder.path.is_none());
        let token = recorder.push_path(KernelComparisonPathStep::AppFunction);
        assert!(token.is_none());
        recorder.record(KernelComparisonOutcome::NotDefEq, &lhs, &rhs, 1);
        recorder.pop_path(token);

        let (_, path) = recorder.into_observation().unwrap();
        assert_eq!(path, KernelComparisonPath::empty());
    }

    #[test]
    fn hotset_bounds_names_and_orders_retained_and_synthetic_entries() {
        let mut hotset = KernelDeltaHotset::default();
        for index in 0..KERNEL_DELTA_HOTSET_CAPACITY {
            hotset.record(&format!("N{index:03}"));
        }
        hotset.record("N000");
        hotset.record("N000");
        hotset.record("N999");
        hotset.record("N999");
        let overlong = "é".repeat(129);
        assert!(overlong.len() > KERNEL_DELTA_NAME_BYTE_LIMIT);
        hotset.record(&overlong);
        hotset.record(&overlong);

        let summary = hotset.summary();

        assert_eq!(summary.retained_names, 256);
        assert_eq!(summary.capacity, 256);
        assert_eq!(summary.emitted, 16);
        assert_eq!(summary.entry_limit, 16);
        assert_eq!(summary.unretained_name_observations, 2);
        assert_eq!(summary.overlong_name_observations, 2);
        assert!(summary.output_truncated);
        assert!(!summary.overflowed);
        assert_eq!(
            summary.entries[0],
            KernelDeltaHotsetEntry {
                constant: "N000".to_owned(),
                count: 3,
            }
        );
        assert_eq!(
            summary.entries[1],
            KernelDeltaHotsetEntry {
                constant: KERNEL_DELTA_OVERLONG_NAME.to_owned(),
                count: 2,
            }
        );
        assert_eq!(summary.entries[2].constant, "N001");
    }

    #[test]
    fn hotset_ties_sort_by_name_and_saturation_marks_nearest_overflow() {
        let mut hotset = KernelDeltaHotset::default();
        hotset.record("Zeta.value");
        hotset.record("Alpha.value");
        hotset.record("Zeta.value");
        hotset.record("Alpha.value");
        hotset.counts.insert("Max.value".to_owned(), u64::MAX);
        hotset.record("Max.value");

        let summary = hotset.summary();

        assert_eq!(summary.entries[0].constant, "Max.value");
        assert_eq!(summary.entries[0].count, u64::MAX);
        assert_eq!(summary.entries[1].constant, "Alpha.value");
        assert_eq!(summary.entries[2].constant, "Zeta.value");
        assert!(summary.overflowed);
    }

    #[test]
    fn hotset_omission_counters_saturate_and_propagate_overflow() {
        let mut hotset = KernelDeltaHotset::default();
        for index in 0..KERNEL_DELTA_HOTSET_CAPACITY {
            hotset.record(&format!("N{index:03}"));
        }

        hotset.unretained_name_observations = u64::MAX;
        hotset.record("N999");
        hotset.overlong_name_observations = u64::MAX;
        hotset.record(&"x".repeat(KERNEL_DELTA_NAME_BYTE_LIMIT + 1));

        let summary = hotset.summary();
        assert_eq!(summary.unretained_name_observations, u64::MAX);
        assert_eq!(summary.overlong_name_observations, u64::MAX);
        assert_eq!(summary.entries[0].constant, KERNEL_DELTA_OVERLONG_NAME);
        assert_eq!(summary.entries[0].count, u64::MAX);
        assert!(summary.overflowed);
    }

    #[test]
    fn hotset_mode_selection_allocates_only_for_detailed() {
        assert!(KernelDeltaHotset::for_mode(KernelFuelReportMode::Off).is_none());
        assert!(KernelDeltaHotset::for_mode(KernelFuelReportMode::Failure).is_none());
        let detailed = KernelDeltaHotset::for_mode(KernelFuelReportMode::Detailed).unwrap();
        assert_eq!(detailed.summary(), KernelDeltaHotsetSummary::empty());
    }

    #[test]
    fn kernel_fuel_failure_report_shape_is_scalar_and_producer_bounded() {
        fn assert_operation_fuel_shape(counters: KernelFuelOperationCounters) {
            let KernelFuelOperationCounters {
                budget: _,
                spent: _,
                remaining: _,
                exhausted: _,
                overflowed: _,
            } = counters;
        }

        fn assert_domain_fuel_shape(counters: crate::work::KernelFuelDomainTotals) {
            let crate::work::KernelFuelDomainTotals {
                calls: _,
                logical_spent: _,
                successful_operation_fuel: _,
                exhausted_operation_fuel: _,
                overflowed: _,
            } = counters;
        }

        fn assert_work_shape(work: KernelWorkSnapshot) {
            let KernelWorkSnapshot {
                check_calls: _,
                infer_calls: _,
                whnf_calls: _,
                defeq_calls: _,
                quick_equality_hits: _,
                beta_steps: _,
                delta_steps: _,
                iota_steps: _,
                physical_reductions: _,
                fuel,
                overflowed: _,
            } = work;
            let KernelFuelTotals { whnf, conversion } = fuel;
            assert_domain_fuel_shape(whnf);
            assert_domain_fuel_shape(conversion);
        }

        let mut hotset = KernelDeltaHotset::default();
        hotset.record("Bounded.Constant");
        hotset.record(&"x".repeat(KERNEL_DELTA_NAME_BYTE_LIMIT + 1));
        let report = KernelFuelDiagnostic::new(
            KernelFuelResource::Conversion,
            KernelOperationWork {
                fuel: KernelFuelOperationCounters::default(),
                work: KernelWorkSnapshot::zero(),
            },
            KernelDeclarationWork::from_snapshot(KernelWorkSnapshot::zero()),
            KernelComparisonPath {
                steps: vec![KernelComparisonPathStep::PiDomain],
                truncated: false,
            },
            Some(hotset.summary()),
        );

        // These exhaustive patterns are intentional: adding an expression,
        // context, source/proof identity, or another rendered field makes this
        // regression require an explicit review instead of being hidden by `..`.
        let KernelFuelDiagnostic {
            subsystem,
            resource,
            failed_operation,
            declaration,
            comparison_path,
            retained_delta_constants,
            overflowed: _,
        } = report;
        let _: KernelDiagnosticSubsystem = subsystem;
        let _: KernelFuelResource = resource;
        let KernelOperationWork { fuel, work } = failed_operation;
        assert_operation_fuel_shape(fuel);
        assert_work_shape(work);
        let KernelDeclarationWork {
            fuel,
            work,
            overflowed: _,
        } = declaration;
        let KernelFuelTotals { whnf, conversion } = fuel;
        assert_domain_fuel_shape(whnf);
        assert_domain_fuel_shape(conversion);
        assert_work_shape(work);
        let KernelComparisonPath { steps, truncated } = comparison_path;
        assert!(steps.len() <= KERNEL_COMPARISON_PATH_LIMIT);
        assert!(!truncated);

        let KernelDeltaHotsetSummary {
            retained_names,
            capacity,
            entries,
            emitted,
            entry_limit,
            unretained_name_observations: _,
            overlong_name_observations,
            output_truncated: _,
            overflowed: _,
        } = retained_delta_constants.unwrap();
        assert!(retained_names <= capacity);
        assert_eq!(emitted as usize, entries.len());
        assert!(emitted <= entry_limit);
        assert!(entries.len() <= KERNEL_DELTA_HOTSET_ENTRY_LIMIT);
        for entry in entries {
            let KernelDeltaHotsetEntry { constant, count } = entry;
            assert!(
                constant == KERNEL_DELTA_OVERLONG_NAME
                    || constant.len() <= KERNEL_DELTA_NAME_BYTE_LIMIT
            );
            assert!(count > 0);
            if constant == KERNEL_DELTA_OVERLONG_NAME {
                assert_eq!(count, overlong_name_observations);
            }
        }
    }
}
