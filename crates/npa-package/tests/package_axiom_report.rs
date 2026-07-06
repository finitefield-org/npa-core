use npa_cert::Name;
use npa_package::{
    package_axiom_report_summary, parse_package_hash, PackageArtifactOrigin,
    PackageAxiomPolicyStatus, PackageAxiomPolicyStatusKind, PackageAxiomPolicyViolation,
    PackageAxiomPolicyViolationReason, PackageAxiomReference, PackageAxiomReportModule,
    PackageHash,
};

const ONE_HASH: &str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
const TWO_HASH: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const THREE_HASH: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
const FOUR_HASH: &str = "sha256:4444444444444444444444444444444444444444444444444444444444444444";

fn name(value: &str) -> Name {
    Name::from_dotted(value)
}

fn hash(value: &str) -> PackageHash {
    parse_package_hash(value, "test").unwrap()
}

fn axiom_ref(module: &str, axiom: &str) -> PackageAxiomReference {
    PackageAxiomReference {
        module: name(module),
        name: name(axiom),
        export_hash: hash(ONE_HASH),
        decl_interface_hash: hash(TWO_HASH),
    }
}

fn module_entry(
    module: &str,
    origin: PackageArtifactOrigin,
    direct_axioms: Vec<PackageAxiomReference>,
    transitive_axioms: Vec<PackageAxiomReference>,
    violations: Vec<PackageAxiomPolicyViolation>,
) -> PackageAxiomReportModule {
    PackageAxiomReportModule {
        module: name(module),
        origin,
        export_hash: hash(ONE_HASH),
        certificate_hash: hash(TWO_HASH),
        axiom_report_hash: hash(THREE_HASH),
        certificate_file_hash: hash(FOUR_HASH),
        direct_axioms,
        transitive_axioms,
        policy_status: PackageAxiomPolicyStatus {
            status: if violations.is_empty() {
                PackageAxiomPolicyStatusKind::Ok
            } else {
                PackageAxiomPolicyStatusKind::Violation
            },
            violations,
        },
    }
}

#[test]
fn package_axiom_report_summary_counts_unique_axioms_policy_violations_and_origins() {
    let eq_rec = axiom_ref("Std.Logic.Eq", "Eq.rec");
    let custom = axiom_ref("Proofs.Custom", "Proofs.Custom.ax");
    let modules = vec![
        module_entry(
            "Proofs.A",
            PackageArtifactOrigin::Local,
            vec![eq_rec.clone(), eq_rec.clone()],
            vec![eq_rec.clone(), custom.clone()],
            vec![PackageAxiomPolicyViolation {
                axiom: custom.clone(),
                reason_code: PackageAxiomPolicyViolationReason::AxiomNotAllowlisted,
            }],
        ),
        module_entry(
            "Std.Logic.Eq",
            PackageArtifactOrigin::External,
            vec![eq_rec.clone()],
            vec![eq_rec],
            vec![],
        ),
    ];

    let summary = package_axiom_report_summary(&modules);

    assert_eq!(summary.module_count, 2);
    assert_eq!(summary.local_module_count, 1);
    assert_eq!(summary.external_module_count, 1);
    assert_eq!(summary.direct_axiom_count, 1);
    assert_eq!(summary.transitive_axiom_count, 2);
    assert_eq!(summary.policy_violation_count, 1);
}
