//! Package artifact schema constants.

/// Public package manifest schema for `npa-package.toml`.
///
/// This manifest is package metadata, not checker evidence.
pub const PACKAGE_MANIFEST_SCHEMA: &str = "npa.package.v0.1";

/// Generated package lock schema.
///
/// Package locks are generated metadata used to derive checker-run import
/// locks; they are not checker evidence by themselves.
pub const PACKAGE_LOCK_SCHEMA: &str = "npa.package.lock.v0.1";

/// Generated package axiom report schema.
pub const PACKAGE_AXIOM_REPORT_SCHEMA: &str = "npa.package.axiom_report.v0.1";

/// Generated package theorem index schema.
pub const PACKAGE_THEOREM_INDEX_SCHEMA: &str = "npa.package.theorem_index.v0.1";

/// Generated package publish plan schema.
pub const PACKAGE_PUBLISH_PLAN_SCHEMA: &str = "npa.package.publish_plan.v0.1";

/// Generated high-trust release evidence schema.
///
/// This artifact is release metadata. It is not proof input and does not
/// replace source-free certificate verification.
pub const PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA: &str = "npa.package.verified_high_trust.v0.1";

/// Registry module metadata schema.
///
/// Registry metadata is distribution and search metadata, not trusted base.
pub const REGISTRY_MODULE_SCHEMA: &str = "npa.registry.module.v0.1";

/// Core spec profile used by the package manifest MVP.
pub const CORE_SPEC_V0_1: &str = "npa.core.v0.1";

/// Kernel compatibility profile used by the package manifest MVP.
pub const KERNEL_PROFILE_V0_1: &str = "npa.kernel.v0.1";

/// Canonical certificate format profile used by the package manifest MVP.
pub const CERTIFICATE_FORMAT_CANONICAL_V0_1: &str = "npa.certificate.canonical.v0.1";

/// Reference checker profile used by the package manifest MVP.
pub const CHECKER_PROFILE_REFERENCE_V0_1: &str = "npa.checker.reference.v0.1";

#[cfg(test)]
mod tests {
    use super::{
        CERTIFICATE_FORMAT_CANONICAL_V0_1, CHECKER_PROFILE_REFERENCE_V0_1, CORE_SPEC_V0_1,
        KERNEL_PROFILE_V0_1, PACKAGE_AXIOM_REPORT_SCHEMA, PACKAGE_LOCK_SCHEMA,
        PACKAGE_MANIFEST_SCHEMA, PACKAGE_PUBLISH_PLAN_SCHEMA, PACKAGE_THEOREM_INDEX_SCHEMA,
        PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA, REGISTRY_MODULE_SCHEMA,
    };

    #[test]
    fn package_schema_constants_match_clr00_contract() {
        assert_eq!(PACKAGE_MANIFEST_SCHEMA, "npa.package.v0.1");
        assert_eq!(PACKAGE_LOCK_SCHEMA, "npa.package.lock.v0.1");
        assert_eq!(PACKAGE_AXIOM_REPORT_SCHEMA, "npa.package.axiom_report.v0.1");
        assert_eq!(
            PACKAGE_THEOREM_INDEX_SCHEMA,
            "npa.package.theorem_index.v0.1"
        );
        assert_eq!(PACKAGE_PUBLISH_PLAN_SCHEMA, "npa.package.publish_plan.v0.1");
        assert_eq!(
            PACKAGE_VERIFIED_HIGH_TRUST_SCHEMA,
            "npa.package.verified_high_trust.v0.1"
        );
        assert_eq!(REGISTRY_MODULE_SCHEMA, "npa.registry.module.v0.1");
        assert_eq!(CORE_SPEC_V0_1, "npa.core.v0.1");
        assert_eq!(KERNEL_PROFILE_V0_1, "npa.kernel.v0.1");
        assert_eq!(
            CERTIFICATE_FORMAT_CANONICAL_V0_1,
            "npa.certificate.canonical.v0.1"
        );
        assert_eq!(CHECKER_PROFILE_REFERENCE_V0_1, "npa.checker.reference.v0.1");
    }
}
