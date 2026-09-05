//! Stable, versioned constructors for the programmatic package-command API.

use crate::args::{
    KernelFuelReportMode, PackageArtifactLedgerAuditOptions, PackageAuditCacheMode,
    PackageBuildCertsOptions, PackageBuildCheckCacheMode, PackageBuildSelection,
    PackageCheckSourceStructureOptions, PackageChecker, PackageCommonOptions,
    PackageExternalCheckerOptions, PackageLockInputMode, PackageSourceStructureSelection,
    PackageTheoremPremiseReportOptions, PackageTimingMode, PackageVerifierMemoMode,
    PackageVerifyCertsOptions,
};

/// Version 1 of the semantic package-option construction contract.
pub mod v1 {
    use std::path::PathBuf;

    use super::{
        KernelFuelReportMode, PackageArtifactLedgerAuditOptions, PackageAuditCacheMode,
        PackageBuildCertsOptions, PackageBuildCheckCacheMode, PackageBuildSelection,
        PackageCheckSourceStructureOptions, PackageChecker, PackageCommonOptions,
        PackageExternalCheckerOptions, PackageLockInputMode, PackageSourceStructureSelection,
        PackageTheoremPremiseReportOptions, PackageTimingMode, PackageVerifierMemoMode,
        PackageVerifyCertsOptions,
    };

    /// Construct common package-command options with the requested root and output mode.
    pub fn common_options(root: impl Into<PathBuf>, json: bool) -> PackageCommonOptions {
        PackageCommonOptions {
            root: root.into(),
            json,
        }
    }

    /// Construct an audit request selecting every local module with declared metadata.
    pub fn audit_artifact_ledger_all(
        common: PackageCommonOptions,
    ) -> PackageArtifactLedgerAuditOptions {
        PackageArtifactLedgerAuditOptions {
            common,
            modules: Vec::new(),
        }
    }

    /// Construct an artifact-ledger audit request for explicit modules.
    pub fn audit_artifact_ledger_modules(
        common: PackageCommonOptions,
        modules: Vec<npa_cert::Name>,
    ) -> PackageArtifactLedgerAuditOptions {
        PackageArtifactLedgerAuditOptions { common, modules }
    }

    /// Construct a source-structure check for every manifest module.
    pub fn check_source_structure_all(
        common: PackageCommonOptions,
    ) -> PackageCheckSourceStructureOptions {
        PackageCheckSourceStructureOptions {
            common,
            selection: PackageSourceStructureSelection::All,
        }
    }

    /// Construct a source-structure check for explicit registered modules.
    pub fn check_source_structure_modules(
        common: PackageCommonOptions,
        modules: Vec<npa_cert::Name>,
    ) -> PackageCheckSourceStructureOptions {
        PackageCheckSourceStructureOptions {
            common,
            selection: PackageSourceStructureSelection::Modules(modules),
        }
    }

    /// Construct a manifest-free source-structure check for package-relative paths.
    pub fn check_source_structure_paths(
        common: PackageCommonOptions,
        paths: Vec<npa_package::PackagePath>,
    ) -> PackageCheckSourceStructureOptions {
        PackageCheckSourceStructureOptions {
            common,
            selection: PackageSourceStructureSelection::Paths(paths),
        }
    }

    /// Construct the policy and registry inputs required by the external checker.
    pub fn external_checker_options(
        runner_policy: impl Into<PathBuf>,
        runner_policy_hash: impl Into<String>,
        checker_registry: impl Into<PathBuf>,
    ) -> PackageExternalCheckerOptions {
        PackageExternalCheckerOptions {
            runner_policy: runner_policy.into(),
            runner_policy_hash: runner_policy_hash.into(),
            checker_registry: checker_registry.into(),
        }
    }

    /// Construct a full-package certificate-verification request.
    pub fn verify_certs_full(
        common: PackageCommonOptions,
        checker: PackageChecker,
    ) -> PackageVerifyCertsOptions {
        verify_certs(common, checker, false)
    }

    /// Construct a request that verifies only certificates changed in Git.
    pub fn verify_changed_certificates(
        common: PackageCommonOptions,
        checker: PackageChecker,
    ) -> PackageVerifyCertsOptions {
        verify_certs(common, checker, true)
    }

    /// Construct a request that verifies explicit local seed modules and their imports.
    pub fn verify_certs_modules(
        common: PackageCommonOptions,
        checker: PackageChecker,
        modules: Vec<npa_cert::Name>,
    ) -> PackageVerifyCertsOptions {
        verify_certs(common, checker, false).with_modules(modules)
    }

    /// Construct a request that selects committed changes relative to a Git base ref.
    pub fn verify_certs_base(
        common: PackageCommonOptions,
        checker: PackageChecker,
        base: impl Into<String>,
    ) -> PackageVerifyCertsOptions {
        verify_certs(common, checker, false).with_base(base)
    }

    /// Alias for [`verify_certs_modules`] using selection-oriented naming.
    pub fn verify_modules(
        common: PackageCommonOptions,
        checker: PackageChecker,
        modules: Vec<npa_cert::Name>,
    ) -> PackageVerifyCertsOptions {
        verify_certs_modules(common, checker, modules)
    }

    /// Alias for [`verify_certs_base`] using committed-range naming.
    pub fn verify_committed_base(
        common: PackageCommonOptions,
        checker: PackageChecker,
        base: impl Into<String>,
    ) -> PackageVerifyCertsOptions {
        verify_certs_base(common, checker, base)
    }

    /// Construct a read-only ordinary certificate-build check request.
    pub fn build_certs_check(common: PackageCommonOptions) -> PackageBuildCertsOptions {
        build_certs(common, true, false)
    }

    /// Construct an ordinary certificate-build write request.
    pub fn build_certs_write(common: PackageCommonOptions) -> PackageBuildCertsOptions {
        build_certs(common, false, false)
    }

    /// Construct a read-only artifact-refresh check request.
    pub fn refresh_artifacts_check(common: PackageCommonOptions) -> PackageBuildCertsOptions {
        build_certs(common, true, true)
    }

    /// Construct an atomic artifact-refresh write request.
    pub fn refresh_artifacts_write(common: PackageCommonOptions) -> PackageBuildCertsOptions {
        build_certs(common, false, true)
    }

    /// Construct a theorem-premise report generation or check request.
    pub fn theorem_premise_report(
        common: PackageCommonOptions,
        check: bool,
    ) -> PackageTheoremPremiseReportOptions {
        PackageTheoremPremiseReportOptions {
            common,
            check,
            timings: PackageTimingMode::Off,
        }
    }

    fn verify_certs(
        common: PackageCommonOptions,
        checker: PackageChecker,
        changed: bool,
    ) -> PackageVerifyCertsOptions {
        PackageVerifyCertsOptions {
            common,
            checker,
            changed,
            modules: Vec::new(),
            base: None,
            modules_requested: false,
            audit_cache: PackageAuditCacheMode::Off,
            verifier_memo: PackageVerifierMemoMode::Off,
            jobs: 1,
            external: None,
            timings: PackageTimingMode::Off,
            package_lock_mode: PackageLockInputMode::CheckedFile,
        }
    }

    fn build_certs(
        common: PackageCommonOptions,
        check: bool,
        update_manifest_hashes: bool,
    ) -> PackageBuildCertsOptions {
        PackageBuildCertsOptions {
            common,
            check,
            build_check_cache: PackageBuildCheckCacheMode::Off,
            build_check_cache_root: None,
            update_manifest_hashes,
            selection: PackageBuildSelection::Full,
            kernel_fuel_report: KernelFuelReportMode::Failure,
            timings: PackageTimingMode::Off,
        }
    }
}

impl PackageVerifyCertsOptions {
    /// Replace the current selector with explicit local seed modules.
    #[must_use]
    pub fn with_modules(mut self, modules: Vec<npa_cert::Name>) -> Self {
        self.changed = false;
        self.modules = modules;
        self.base = None;
        self.modules_requested = true;
        self
    }

    /// Replace the current selector with a committed Git base ref.
    #[must_use]
    pub fn with_base(mut self, base: impl Into<String>) -> Self {
        self.changed = false;
        self.modules.clear();
        self.modules_requested = false;
        self.base = Some(base.into());
        self
    }

    /// Set the local package audit-cache mode without changing any other option.
    #[must_use]
    pub fn with_audit_cache(mut self, mode: PackageAuditCacheMode) -> Self {
        self.audit_cache = mode;
        self
    }

    /// Set the local verifier-memo mode without changing any other option.
    #[must_use]
    pub fn with_verifier_memo(mut self, mode: PackageVerifierMemoMode) -> Self {
        self.verifier_memo = mode;
        self
    }

    /// Set the maximum verifier worker count without changing any other option.
    #[must_use]
    pub fn with_jobs(mut self, jobs: usize) -> Self {
        self.jobs = jobs;
        self
    }

    /// Set the external-checker inputs without changing the selected checker or other options.
    #[must_use]
    pub fn with_external(mut self, options: PackageExternalCheckerOptions) -> Self {
        self.external = Some(options);
        self
    }

    /// Set package audit timing telemetry without changing any other option.
    #[must_use]
    pub fn with_timings(mut self, mode: PackageTimingMode) -> Self {
        self.timings = mode;
        self
    }

    /// Set the package-lock input mode without changing checker or cache selection.
    #[must_use]
    pub fn with_package_lock_mode(mut self, mode: PackageLockInputMode) -> Self {
        self.package_lock_mode = mode;
        self
    }
}

impl PackageBuildCertsOptions {
    /// Set the build-check cache mode without changing any other option.
    ///
    /// `Off` performs no cache-only work. `ReadThrough` is accepted by full or targeted checks,
    /// performs every build and support check live, and may warm untrusted diagnostic and support
    /// stores. `LocalHit` is accepted only by targeted checks, may reuse eligible support
    /// contexts, builds every reached target fresh, and always produces local-only authoring
    /// feedback. Both non-off modes write only safety-resolved external local stores;
    /// local-hit warms only eligible cache-free live miss subtrees. Neither mode is proof
    /// evidence.
    #[must_use]
    pub fn with_build_check_cache(mut self, mode: PackageBuildCheckCacheMode) -> Self {
        self.build_check_cache = mode;
        self
    }

    /// Set the complete build-check cache root used by programmatic tools and tests.
    ///
    /// This does not expose an ordinary CLI flag. The cache-anchor resolver validates the
    /// supplied root before use.
    #[must_use]
    pub fn with_build_check_cache_root(mut self, root: std::path::PathBuf) -> Self {
        self.build_check_cache_root = Some(root);
        self
    }

    /// Replace full selection with explicit local modules.
    #[must_use]
    pub fn with_modules(mut self, modules: Vec<npa_cert::Name>) -> Self {
        self.selection = PackageBuildSelection::Modules(modules);
        self
    }

    /// Replace the current selection with Git-derived changed paths.
    #[must_use]
    pub fn with_changed(mut self) -> Self {
        self.selection = PackageBuildSelection::Changed;
        self
    }

    /// Set kernel fuel diagnostics without changing timing telemetry or any other option.
    #[must_use]
    pub fn with_kernel_fuel_report(mut self, mode: KernelFuelReportMode) -> Self {
        self.kernel_fuel_report = mode;
        self
    }

    /// Set package build timing telemetry without changing fuel diagnostics or any other option.
    #[must_use]
    pub fn with_timings(mut self, mode: PackageTimingMode) -> Self {
        self.timings = mode;
        self
    }
}

impl PackageTheoremPremiseReportOptions {
    /// Set package audit timing telemetry without changing any other option.
    #[must_use]
    pub fn with_timings(mut self, mode: PackageTimingMode) -> Self {
        self.timings = mode;
        self
    }
}
