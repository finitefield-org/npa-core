//! Deterministic package gate planning from changed paths.
//!
//! Gate plans are untrusted orchestration guidance. They recommend local
//! commands from path impact only; they do not accept proofs and are never proof
//! evidence.

use std::collections::BTreeSet;

/// Trust-boundary note emitted by package gate plans.
pub const PACKAGE_GATE_PLAN_TRUST_BOUNDARY_NOTE: &str =
    "gate-plan is untrusted orchestration guidance; it never accepts proofs or replaces canonical certificate/source-free verification";

const KERNEL_PHASE0_DOC_PATH: &str = concat!("develop/", "phase", "0", ".md");
const KERNEL_PHASE1_DOC_PATH: &str = concat!("develop/", "phase", "1", ".md");
const RELEASE_AUDIT_SCRIPT_PATH: &str = concat!("scripts/", "phase", "8", "-release-audit.sh");
const RELEASE_AUDIT_SCRIPT_COMMAND: &str = concat!(
    "(cd ../npa-core && ./scripts/",
    "phase",
    "8",
    "-release-audit.sh)"
);
const REGRESSION_SCRIPT_PATH: &str = concat!("scripts/", "phase", "9", "-regression.sh");
const CORE_FAST_GATE_COMMAND: &str = "(cd ../npa-core && ./scripts/check-fast.sh)";

/// Stable package gate impact class.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum PackageGateImpactClass {
    /// Only documentation or text planning files changed.
    DocsOnly,
    /// Proof corpus authoring artifacts changed without package metadata impact.
    ProofAuthoring,
    /// Package metadata, projections, generated package artifacts, or package tooling changed.
    PackageMetadataProjection,
    /// Checker, certificate, package lock, package verifier, or cache semantics changed.
    CheckerCertificateSemantics,
    /// Kernel or core calculus semantics changed.
    KernelCoreSemantics,
    /// Release or high-trust-adjacent policy/artifact paths changed.
    ReleaseHighTrustAdjacent,
}

impl PackageGateImpactClass {
    /// Stable JSON/CLI spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DocsOnly => "docs-only",
            Self::ProofAuthoring => "proof-authoring",
            Self::PackageMetadataProjection => "package-metadata-projection",
            Self::CheckerCertificateSemantics => "checker-certificate-semantics",
            Self::KernelCoreSemantics => "kernel-core-semantics",
            Self::ReleaseHighTrustAdjacent => "release-high-trust-adjacent",
        }
    }
}

/// Deterministic gate recommendation for a changed-file set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageGatePlan {
    /// Changed paths after normalization, sorted in deterministic order.
    pub changed_files: Vec<String>,
    /// Proof modules derivable from changed proof artifact paths.
    pub changed_modules: Vec<String>,
    /// Package generated artifacts derivable from changed paths.
    pub package_generated_artifacts: Vec<String>,
    /// Highest-impact class in the changed-file set.
    pub impact_class: PackageGateImpactClass,
    /// Commands required by the selected gate policy.
    pub required_commands: Vec<String>,
    /// Optional local accelerators that may shorten local feedback only.
    pub optional_local_acceleration_commands: Vec<String>,
    /// Deterministic reasons explaining every escalation.
    pub escalation_reasons: Vec<String>,
    /// Trust-boundary note. This is informational and not proof evidence.
    pub trust_boundary_note: String,
}

/// Build a deterministic package gate plan from changed paths.
///
/// The planner is intentionally path-only. It does not inspect proof content,
/// run checkers, query the network, or decide whether any proof is accepted.
pub fn package_gate_plan_from_paths<I, S>(changed_paths: I) -> PackageGatePlan
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let changed_files = changed_paths
        .into_iter()
        .filter_map(|path| normalize_changed_path(path.as_ref()))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let mut classes = BTreeSet::new();
    let mut changed_modules = BTreeSet::new();
    let mut package_generated_artifacts = BTreeSet::new();

    for path in &changed_files {
        classes.insert(classify_changed_path(path));
        if let Some(module) = proof_module_from_artifact_path(path) {
            changed_modules.insert(module);
        }
        if is_package_generated_artifact(path) {
            package_generated_artifacts.insert(path.clone());
        }
    }

    let impact_class = classes
        .iter()
        .next_back()
        .copied()
        .unwrap_or(PackageGateImpactClass::DocsOnly);

    PackageGatePlan {
        required_commands: required_commands_for_plan(impact_class, &classes, &changed_modules),
        optional_local_acceleration_commands: optional_commands_for_plan(
            impact_class,
            &classes,
            &changed_modules,
        ),
        escalation_reasons: escalation_reasons_for_classes(&classes),
        changed_files,
        changed_modules: changed_modules.into_iter().collect(),
        package_generated_artifacts: package_generated_artifacts.into_iter().collect(),
        impact_class,
        trust_boundary_note: PACKAGE_GATE_PLAN_TRUST_BOUNDARY_NOTE.to_owned(),
    }
}

fn normalize_changed_path(path: &str) -> Option<String> {
    let normalized = path.trim().replace('\\', "/");
    let normalized = normalized.trim_start_matches("./").to_owned();
    if normalized.is_empty() {
        None
    } else {
        Some(normalized)
    }
}

fn classify_changed_path(path: &str) -> PackageGateImpactClass {
    if is_release_high_trust_adjacent_path(path) {
        return PackageGateImpactClass::ReleaseHighTrustAdjacent;
    }
    if is_kernel_core_semantics_path(path) {
        return PackageGateImpactClass::KernelCoreSemantics;
    }
    if is_checker_certificate_semantics_path(path) {
        return PackageGateImpactClass::CheckerCertificateSemantics;
    }
    if is_package_metadata_projection_path(path) {
        return PackageGateImpactClass::PackageMetadataProjection;
    }
    if is_proof_authoring_path(path) {
        return PackageGateImpactClass::ProofAuthoring;
    }
    if is_doc_path(path) {
        PackageGateImpactClass::DocsOnly
    } else {
        PackageGateImpactClass::PackageMetadataProjection
    }
}

fn is_doc_path(path: &str) -> bool {
    path == "AGENTS.md"
        || path == "README.md"
        || path.starts_with("develop/")
        || path.starts_with("docs/")
        || path.starts_with("proofs/")
            && (path.ends_with(".md") || path.ends_with(".txt") || path.ends_with(".rst"))
        || path.ends_with(".md")
        || path.ends_with(".txt")
        || path.ends_with(".rst")
}

fn is_proof_authoring_path(path: &str) -> bool {
    proof_module_from_artifact_path(path).is_some()
}

fn is_package_metadata_projection_path(path: &str) -> bool {
    path == "proofs/npa-package.toml"
        || path == "proofs/manifest.toml"
        || is_package_generated_artifact(path)
        || path.starts_with("tools/proof-corpus/")
        || path == "scripts/check-corpus-authoring.sh"
        || path == "scripts/check-corpus-package.sh"
        || path == "scripts/check-corpus-full.sh"
        || path == "scripts/check-corpus.sh"
        || path == "crates/npa-cli/src/args.rs"
        || path == "crates/npa-cli/src/package.rs"
        || path == "crates/npa-cli/src/package_gate_plan.rs"
        || path == "crates/npa-package/src/gate_plan.rs"
        || matches!(
            path,
            "crates/npa-package/src/audit_selection.rs"
                | "crates/npa-package/src/axiom_report.rs"
                | "crates/npa-package/src/export_summary.rs"
                | "crates/npa-package/src/manifest.rs"
                | "crates/npa-package/src/name.rs"
                | "crates/npa-package/src/path.rs"
                | "crates/npa-package/src/publish_plan.rs"
                | "crates/npa-package/src/registry.rs"
                | "crates/npa-package/src/schema.rs"
                | "crates/npa-package/src/theorem_index.rs"
                | "crates/npa-package/src/validate.rs"
        )
}

fn is_checker_certificate_semantics_path(path: &str) -> bool {
    path.starts_with("crates/npa-cert/")
        || path.starts_with("crates/npa-checker-ref/")
        || path == "crates/npa-api/src/package_verifier.rs"
        || path.starts_with("crates/npa-api/src/independent_checker")
        || matches!(
            path,
            "crates/npa-package/src/artifacts.rs"
                | "crates/npa-package/src/audit_cache.rs"
                | "crates/npa-package/src/build_check_cache.rs"
                | "crates/npa-package/src/hash.rs"
                | "crates/npa-package/src/lock.rs"
        )
}

fn is_kernel_core_semantics_path(path: &str) -> bool {
    path.starts_with("crates/npa-kernel/")
        || path == "develop/core-spec-v0.1.md"
        || path == KERNEL_PHASE0_DOC_PATH
        || path == KERNEL_PHASE1_DOC_PATH
}

fn is_release_high_trust_adjacent_path(path: &str) -> bool {
    path == RELEASE_AUDIT_SCRIPT_PATH
        || path == REGRESSION_SCRIPT_PATH
        || path == "crates/npa-package/src/verified_high_trust.rs"
        || path == "crates/npa-cli/src/package_high_trust.rs"
        || path.contains("high-trust")
        || path.contains("verified_high_trust")
}

fn is_package_generated_artifact(path: &str) -> bool {
    path.starts_with("proofs/generated/")
        && (path.ends_with("package-lock.json")
            || path.ends_with("axiom-report.json")
            || path.ends_with("theorem-index.json")
            || path.ends_with("theorem-premise-report.json")
            || path.ends_with("ai-theorem-index.json")
            || path.ends_with("verified-export-summary.json")
            || path.ends_with("publish-plan.json"))
}

fn proof_module_from_artifact_path(path: &str) -> Option<String> {
    let proof_relative = path.strip_prefix("proofs/")?;
    if !(proof_relative.ends_with("/source.npa")
        || proof_relative.ends_with("/certificate.npcert")
        || proof_relative.ends_with("/meta.json")
        || proof_relative.ends_with("/replay.json"))
    {
        return None;
    }
    let mut parts = proof_relative.split('/').collect::<Vec<_>>();
    parts.pop()?;
    let start = parts
        .iter()
        .position(|part| part.chars().next().is_some_and(char::is_uppercase))?;
    if start >= parts.len() {
        return None;
    }
    Some(parts[start..].join("."))
}

fn required_commands_for_plan(
    impact_class: PackageGateImpactClass,
    classes: &BTreeSet<PackageGateImpactClass>,
    changed_modules: &BTreeSet<String>,
) -> Vec<String> {
    let mut commands = Vec::new();
    push_unique(&mut commands, "git diff --check".to_owned());

    if classes.contains(&PackageGateImpactClass::ProofAuthoring) {
        for module in changed_modules {
            push_unique(
                &mut commands,
                format!(
                    "cargo run -p npa-proof-corpus -- --module {module} --verified-cache authoring"
                ),
            );
        }
        push_unique(
            &mut commands,
            "./scripts/check-corpus-authoring.sh".to_owned(),
        );
    }

    if impact_class >= PackageGateImpactClass::PackageMetadataProjection {
        push_unique(&mut commands, CORE_FAST_GATE_COMMAND.to_owned());
        push_unique(
            &mut commands,
            "./scripts/check-corpus-package.sh".to_owned(),
        );
    }

    if impact_class >= PackageGateImpactClass::CheckerCertificateSemantics {
        push_unique(&mut commands, "./scripts/check-corpus-full.sh".to_owned());
    }

    if impact_class >= PackageGateImpactClass::ReleaseHighTrustAdjacent {
        push_unique(&mut commands, RELEASE_AUDIT_SCRIPT_COMMAND.to_owned());
    }

    commands
}

fn push_unique(values: &mut Vec<String>, value: String) {
    if !values.contains(&value) {
        values.push(value);
    }
}

fn optional_commands_for_plan(
    impact_class: PackageGateImpactClass,
    classes: &BTreeSet<PackageGateImpactClass>,
    changed_modules: &BTreeSet<String>,
) -> Vec<String> {
    let mut commands = Vec::new();

    if classes.contains(&PackageGateImpactClass::ProofAuthoring) {
        push_unique(
            &mut commands,
            "cargo run -p npa-proof-corpus -- --changed-only --verified-cache authoring".to_owned(),
        );
        for module in changed_modules {
            push_unique(
                &mut commands,
                format!("cargo run -p npa-proof-corpus -- --build-module {module}"),
            );
        }
    }

    if impact_class >= PackageGateImpactClass::PackageMetadataProjection {
        push_unique(
            &mut commands,
            "(cd ../npa-core && cargo test -p npa-cli package_cli_smoke)".to_owned(),
        );
        push_unique(
            &mut commands,
            "cargo run --manifest-path ../npa-core/Cargo.toml -p npa-cli -- package verify-certs --root proofs --checker fast --json"
                .to_owned(),
        );
        push_unique(
            &mut commands,
            "cargo run --manifest-path ../npa-core/Cargo.toml -p npa-cli -- package verify-certs --root proofs --checker fast --audit-cache local-hit --json"
                .to_owned(),
        );
    }

    commands
}

fn escalation_reasons_for_classes(classes: &BTreeSet<PackageGateImpactClass>) -> Vec<String> {
    let mut reasons = Vec::new();
    if classes.is_empty() || classes == &BTreeSet::from([PackageGateImpactClass::DocsOnly]) {
        reasons.push("docs-only changes avoid proof corpus package/full gates".to_owned());
        return reasons;
    }
    if classes.contains(&PackageGateImpactClass::ProofAuthoring) {
        reasons.push("proof authoring artifacts changed under proofs/".to_owned());
    }
    if classes.contains(&PackageGateImpactClass::PackageMetadataProjection) {
        reasons.push(
            "package metadata, projection, generated artifact, or package tooling changed"
                .to_owned(),
        );
    }
    if classes.contains(&PackageGateImpactClass::CheckerCertificateSemantics) {
        reasons.push("checker, certificate, package lock, package verifier, or audit cache semantics changed".to_owned());
    }
    if classes.contains(&PackageGateImpactClass::KernelCoreSemantics) {
        reasons.push("kernel or core semantics changed; full corpus and high-trust-adjacent review are required".to_owned());
    }
    if classes.contains(&PackageGateImpactClass::ReleaseHighTrustAdjacent) {
        reasons.push("release or high-trust-adjacent files changed".to_owned());
    }
    reasons
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn package_gate_plan_docs_only_avoids_package_and_full_gates() {
        let plan = package_gate_plan_from_paths([
            "develop/proof-corpus-package-audit-speed-plan.md",
            "proofs/README.md",
        ]);

        assert_eq!(plan.impact_class, PackageGateImpactClass::DocsOnly);
        assert_eq!(plan.required_commands, vec!["git diff --check"]);
        assert!(plan
            .escalation_reasons
            .contains(&"docs-only changes avoid proof corpus package/full gates".to_owned()));
        assert!(plan
            .required_commands
            .iter()
            .all(|command| !command.contains("check-corpus-package")
                && !command.contains("check-corpus-full")));
        assert!(plan.trust_boundary_note.contains("never accepts proofs"));
    }

    #[test]
    fn package_gate_plan_proof_authoring_includes_changed_modules() {
        let plan = package_gate_plan_from_paths([
            "proofs/Proofs/Ai/Basic/source.npa",
            "proofs/vendor/npa-std/Std/Logic/Eq/certificate.npcert",
        ]);

        assert_eq!(plan.impact_class, PackageGateImpactClass::ProofAuthoring);
        assert_eq!(
            plan.changed_modules,
            vec!["Proofs.Ai.Basic", "Std.Logic.Eq"]
        );
        assert!(plan.required_commands.iter().any(|command| command
            == "cargo run -p npa-proof-corpus -- --module Proofs.Ai.Basic --verified-cache authoring"));
        assert!(plan.required_commands.iter().any(|command| {
            command
            == "cargo run -p npa-proof-corpus -- --module Std.Logic.Eq --verified-cache authoring"
        }));
        assert!(plan
            .required_commands
            .contains(&"./scripts/check-corpus-authoring.sh".to_owned()));
    }

    #[test]
    fn package_gate_plan_generated_artifact_escalates_to_package_gate() {
        let plan = package_gate_plan_from_paths([
            "proofs/generated/package-lock.json",
            "proofs/generated/publish-plan.json",
        ]);

        assert_eq!(
            plan.impact_class,
            PackageGateImpactClass::PackageMetadataProjection
        );
        assert_eq!(
            plan.package_generated_artifacts,
            vec![
                "proofs/generated/package-lock.json",
                "proofs/generated/publish-plan.json"
            ]
        );
        assert!(plan
            .required_commands
            .contains(&"./scripts/check-corpus-package.sh".to_owned()));
        assert!(!plan
            .required_commands
            .contains(&"./scripts/check-corpus-full.sh".to_owned()));
    }

    #[test]
    fn package_gate_plan_checker_and_kernel_changes_escalate_to_full_gate() {
        let checker_plan = package_gate_plan_from_paths(["crates/npa-api/src/package_verifier.rs"]);
        assert_eq!(
            checker_plan.impact_class,
            PackageGateImpactClass::CheckerCertificateSemantics
        );
        assert!(checker_plan
            .required_commands
            .contains(&"./scripts/check-corpus-package.sh".to_owned()));
        assert!(checker_plan
            .required_commands
            .contains(&"./scripts/check-corpus-full.sh".to_owned()));

        let kernel_plan = package_gate_plan_from_paths(["crates/npa-kernel/src/lib.rs"]);
        assert_eq!(
            kernel_plan.impact_class,
            PackageGateImpactClass::KernelCoreSemantics
        );
        assert!(kernel_plan
            .required_commands
            .contains(&"./scripts/check-corpus-full.sh".to_owned()));
        assert!(kernel_plan
            .escalation_reasons
            .iter()
            .any(|reason| reason.contains("kernel or core semantics changed")));
    }
}
