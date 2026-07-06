use npa_cert::Name;
use npa_package::{
    package_theorem_index_summary, parse_package_hash, PackageArtifactOrigin,
    PackageAxiomReference, PackageGlobalRef, PackageHash, PackagePath, PackageTheoremIndexArtifact,
    PackageTheoremIndexEntry, PackageTheoremIndexKind, PackageTheoremIndexMode,
    PackageTheoremStatement,
};

fn hash(byte: u8) -> PackageHash {
    parse_package_hash(&format!("sha256:{:064x}", byte), "test").unwrap()
}

fn name(value: &str) -> Name {
    Name::from_dotted(value)
}

fn entry(
    module: &str,
    declaration: &str,
    kind: PackageTheoremIndexKind,
    axiom_dependencies: Vec<PackageAxiomReference>,
) -> PackageTheoremIndexEntry {
    PackageTheoremIndexEntry {
        global_ref: PackageGlobalRef {
            module: name(module),
            name: name(declaration),
            export_hash: hash(1),
            certificate_hash: hash(2),
            decl_interface_hash: hash(3),
        },
        kind,
        statement: PackageTheoremStatement {
            core_hash: hash(4),
            head: None,
            constants: Vec::new(),
        },
        modes: vec![PackageTheoremIndexMode::Exact],
        tags: Vec::new(),
        axiom_dependencies,
        module_axiom_report_hash: hash(5),
        artifact: PackageTheoremIndexArtifact {
            origin: PackageArtifactOrigin::Local,
            certificate: PackagePath::new("Proofs/A/certificate.npcert"),
        },
    }
}

fn axiom_dependency(module: &str, declaration: &str) -> PackageAxiomReference {
    PackageAxiomReference {
        module: name(module),
        name: name(declaration),
        export_hash: hash(6),
        decl_interface_hash: hash(7),
    }
}

#[test]
fn package_theorem_index_summary_counts_entries_kinds_modules_and_axioms() {
    let entries = vec![
        entry(
            "Proofs.A",
            "thm",
            PackageTheoremIndexKind::Theorem,
            vec![axiom_dependency("Proofs.A", "Eq.rec")],
        ),
        entry("Proofs.A", "ax", PackageTheoremIndexKind::Axiom, Vec::new()),
        entry(
            "Proofs.B",
            "other",
            PackageTheoremIndexKind::Theorem,
            Vec::new(),
        ),
    ];

    let summary = package_theorem_index_summary(&entries);

    assert_eq!(summary.entry_count, 3);
    assert_eq!(summary.theorem_count, 2);
    assert_eq!(summary.axiom_count, 1);
    assert_eq!(summary.module_count, 2);
    assert_eq!(summary.entries_with_axioms_count, 1);
}
