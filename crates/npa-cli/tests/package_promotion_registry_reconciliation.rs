use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use npa_cert::Name;
use npa_package::{
    catalog_change_event_id, format_package_hash, package_file_hash,
    parse_and_validate_manifest_str, parse_catalog_registry_sync_attestation_json,
    parse_promotion_origin_registry_v3_json, promotion_legacy_target_reservation_id, PackageHash,
    PackagePath, PromotionAuditLocation, PromotionEvidence, PromotionLegacyTargetReservation,
    PromotionLifecycle, PromotionOriginRegistry, PromotionReservedTheorem, PromotionTargetRevision,
    MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA, MATHLIB_PROMOTION_REGISTRY_ID,
};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempRoot(PathBuf);

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn copy_tree(source: &Path, target: &Path) {
    fs::create_dir(target).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&source_path, &target_path);
        } else {
            fs::copy(source_path, target_path).unwrap();
        }
    }
}

fn run(binary: &Path, arguments: &[&OsStr]) -> Output {
    Command::new(binary).args(arguments).output().unwrap()
}

fn assert_passed(output: Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "command failed\nstdout: {stdout}\nstderr: {stderr}"
    );
    stdout.into_owned()
}

fn assert_failed_with_reason(output: Output, reason: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "command unexpectedly passed\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains(reason) || stderr.contains(reason),
        "missing reason {reason}\nstdout: {stdout}\nstderr: {stderr}"
    );
}

fn encode_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn generate_projections(binary: &Path, root: &Path) {
    let root = root.as_os_str();
    for arguments in [
        vec![
            OsStr::new("package"),
            OsStr::new("lock"),
            OsStr::new("write"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
        vec![
            OsStr::new("package"),
            OsStr::new("axiom-report"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
        vec![
            OsStr::new("package"),
            OsStr::new("index"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
        vec![
            OsStr::new("package"),
            OsStr::new("theorem-premise-report"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
        vec![
            OsStr::new("package"),
            OsStr::new("export-summary"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
        vec![
            OsStr::new("package"),
            OsStr::new("publish-plan"),
            OsStr::new("--root"),
            root,
            OsStr::new("--json"),
        ],
    ] {
        assert_passed(run(binary, &arguments));
    }
}

fn module_block(module: &str) -> String {
    let relative = module.replace('.', "/");
    let zero = "sha256:0000000000000000000000000000000000000000000000000000000000000000";
    format!(
        "\n[[modules]]\nmodule = \"{module}\"\nsource = \"{relative}/source.npa\"\ncertificate = \"{relative}/certificate.npcert\"\nmeta = \"{relative}/meta.json\"\nreplay = \"{relative}/replay.json\"\nproducer_profile = \"human-surface-explicit-term\"\nexpected_source_hash = \"{zero}\"\nexpected_certificate_file_hash = \"{zero}\"\nexpected_export_hash = \"{zero}\"\nexpected_axiom_report_hash = \"{zero}\"\nexpected_certificate_hash = \"{zero}\"\nimports = []\ndefinitions = []\ntheorems = []\naxioms = []\n"
    )
}

fn prepare_module_package(binary: &Path, root: &Path, version: &str, modules: &[&str]) {
    let manifest_path = root.join("npa-package.toml");
    let mut manifest = fs::read_to_string(&manifest_path)
        .unwrap()
        .replace("version = \"0.1.0\"", &format!("version = \"{version}\""))
        .replace("modules = []", "");
    for module in modules {
        manifest.push_str(&module_block(module));
        let directory = root.join(module.replace('.', "/"));
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("source.npa"), "").unwrap();
    }
    fs::write(&manifest_path, manifest).unwrap();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("build-certs"),
            OsStr::new("--root"),
            root.as_os_str(),
            OsStr::new("--build-check-cache"),
            OsStr::new("off"),
            OsStr::new("--update-manifest-hashes"),
            OsStr::new("--json"),
        ],
    ));
    for module in modules {
        fs::write(
            root.join(module.replace('.', "/")).join("replay.json"),
            "{}\n",
        )
        .unwrap();
    }
    generate_projections(binary, root);
}

fn write_legacy_registry(root: &Path) -> Vec<u8> {
    let manifest = parse_and_validate_manifest_str(
        &fs::read_to_string(root.join("npa-package.toml")).unwrap(),
    )
    .unwrap()
    .into_manifest();
    let module = &manifest.modules[0];
    let revision = PromotionTargetRevision::<PromotionReservedTheorem> {
        target_version: manifest.version.clone(),
        target_source_file_hash: package_file_hash(
            &fs::read(root.join(module.source.as_str())).unwrap(),
        ),
        target_certificate_file_hash: package_file_hash(
            &fs::read(root.join(module.certificate.as_str())).unwrap(),
        ),
        target_certificate_hash: module.expected_certificate_hash,
        target_export_hash: module.expected_export_hash,
        target_axiom_report_hash: module.expected_axiom_report_hash,
        theorems: Vec::new(),
    };
    let target_module = module.module.clone();
    let mut registry = PromotionOriginRegistry {
        schema: MATHLIB_PROMOTION_ORIGIN_REGISTRY_SCHEMA.to_owned(),
        registry_id: MATHLIB_PROMOTION_REGISTRY_ID.to_owned(),
        registry_version: 1,
        generation: 1,
        target_package: manifest.package,
        entries: Vec::new(),
        unresolved_legacy_targets: vec![PromotionLegacyTargetReservation {
            reservation_id: promotion_legacy_target_reservation_id(&target_module, &revision)
                .unwrap(),
            lifecycle: PromotionLifecycle::Active,
            target_module,
            target_revisions: vec![revision],
            evidence: PromotionEvidence::LegacyAudit {
                audit_location: PromotionAuditLocation {
                    repository: "npa-mathlib".to_owned(),
                    path: PackagePath::new("docs/promotion/legacy.md"),
                },
                audit_file_hash: PackageHash::new([7; 32]),
            },
        }],
        registry_hash: PackageHash::new([0; 32]),
        proof_evidence: false,
    };
    registry.refresh_hash().unwrap();
    registry.canonical_json().unwrap().into_bytes()
}

#[test]
fn reconciliation_dry_run_apply_validate_and_repeat_are_consistent() {
    let temporary = TempRoot(std::env::temp_dir().join(format!(
        "npa-registry-reconciliation-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    )));
    fs::create_dir(&temporary.0).unwrap();
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = repository.join("testdata/package/npa-mathlib-declaration-baseline");
    let previous = temporary.0.join("previous");
    let current = temporary.0.join("current");
    copy_tree(&fixture, &previous);
    copy_tree(&fixture, &current);
    let manifest = fs::read_to_string(current.join("npa-package.toml"))
        .unwrap()
        .replace("version = \"0.1.0\"", "version = \"0.1.1\"");
    fs::write(current.join("npa-package.toml"), manifest).unwrap();
    fs::create_dir_all(current.join("docs/promotion")).unwrap();
    fs::write(
        current.join("docs/promotion/audit.md"),
        "catalog reconciliation audit\n",
    )
    .unwrap();

    let binary = Path::new(env!("CARGO_BIN_EXE_npa"));
    generate_projections(binary, &current);
    let common = [
        OsStr::new("package"),
        OsStr::new("reconcile-promotion-origin-registry"),
        OsStr::new("--root"),
        current.as_os_str(),
        OsStr::new("--previous-target-root"),
        previous.as_os_str(),
        OsStr::new("--audit"),
        OsStr::new("docs/promotion/audit.md"),
        OsStr::new("--out"),
        OsStr::new("docs/promotion/sync.json"),
        OsStr::new("--json"),
    ];

    let mut dry_run = common.to_vec();
    dry_run.push(OsStr::new("--dry-run"));
    let dry_run_output = assert_passed(run(binary, &dry_run));
    assert!(dry_run_output.contains("\"reason_code\":\"dry_run\""));
    assert!(!current.join("docs/promotion/sync.json").exists());

    let mut apply = common.to_vec();
    apply.push(OsStr::new("--apply"));
    let old_registry = fs::read(current.join("promotion-origins.json")).unwrap();
    assert_passed(run(binary, &apply));
    assert!(current.join("docs/promotion/sync.json").is_file());
    let new_registry = fs::read(current.join("promotion-origins.json")).unwrap();
    let attestation = fs::read(current.join("docs/promotion/sync.json")).unwrap();

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("validate-promotion-origin-registry"),
            OsStr::new("--root"),
            current.as_os_str(),
            OsStr::new("--json"),
        ],
    ));
    let mut forged_attestation =
        parse_catalog_registry_sync_attestation_json(std::str::from_utf8(&attestation).unwrap())
            .unwrap();
    forged_attestation.input_registry.registry_hash = PackageHash::new([99; 32]);
    forged_attestation.refresh_hash().unwrap();
    let mut forged_registry =
        parse_promotion_origin_registry_v3_json(std::str::from_utf8(&new_registry).unwrap())
            .unwrap();
    let forged_event = forged_registry.catalog_change_events.last_mut().unwrap();
    forged_event.attestation.payload_hash = forged_attestation.attestation_hash;
    forged_event.event_id = catalog_change_event_id(forged_event).unwrap();
    forged_registry.refresh_hash().unwrap();
    fs::write(
        current.join("docs/promotion/sync.json"),
        forged_attestation.canonical_json().unwrap(),
    )
    .unwrap();
    fs::write(
        current.join("promotion-origins.json"),
        forged_registry.canonical_json().unwrap(),
    )
    .unwrap();
    assert_failed_with_reason(
        run(binary, &apply),
        "promotion_registry_reconciliation_partial_apply",
    );
    fs::write(current.join("promotion-origins.json"), &new_registry).unwrap();
    fs::write(current.join("docs/promotion/sync.json"), &attestation).unwrap();

    fs::write(current.join("docs/promotion/sync.json"), "{}\n").unwrap();
    assert_failed_with_reason(
        run(binary, &apply),
        "promotion_registry_reconciliation_partial_apply",
    );
    fs::write(current.join("docs/promotion/sync.json"), &attestation).unwrap();

    fs::write(current.join("promotion-origins.json"), &old_registry).unwrap();
    let journal_directory = current.join("target/registry-reconciliation");
    fs::create_dir_all(&journal_directory).unwrap();
    let root_hash = package_file_hash(
        fs::canonicalize(&current)
            .unwrap()
            .to_string_lossy()
            .as_bytes(),
    );
    let legacy_journal = format!(
        concat!(
            "{{\"schema\":\"npa.mathlib.catalog_registry_recovery.v1\",",
            "\"root_hash\":\"{}\",\"out_path\":\"docs/promotion/sync.json\",",
            "\"old_registry_file_hash\":\"{}\",\"attestation_hex\":\"{}\",",
            "\"registry_hex\":\"{}\",\"proof_evidence\":false}}\n"
        ),
        format_package_hash(&root_hash),
        format_package_hash(&package_file_hash(&old_registry)),
        encode_hex(&attestation),
        encode_hex(&new_registry),
    );
    let legacy_journal_path = journal_directory.join("legacy.json");
    let forged_legacy_journal = legacy_journal.replace(
        &format_package_hash(&package_file_hash(&old_registry)),
        &format_package_hash(&PackageHash::new([98; 32])),
    );
    fs::write(&legacy_journal_path, forged_legacy_journal).unwrap();
    assert_failed_with_reason(
        run(
            binary,
            &[
                OsStr::new("package"),
                OsStr::new("reconcile-promotion-origin-registry"),
                OsStr::new("--root"),
                current.as_os_str(),
                OsStr::new("--recover"),
                OsStr::new("target/registry-reconciliation/legacy.json"),
                OsStr::new("--json"),
            ],
        ),
        "promotion_registry_reconciliation_recovery_invalid",
    );
    fs::write(&legacy_journal_path, legacy_journal).unwrap();
    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("reconcile-promotion-origin-registry"),
            OsStr::new("--root"),
            current.as_os_str(),
            OsStr::new("--recover"),
            OsStr::new("target/registry-reconciliation/legacy.json"),
            OsStr::new("--json"),
        ],
    ));
    assert_eq!(
        fs::read(current.join("promotion-origins.json")).unwrap(),
        new_registry
    );
    assert!(!legacy_journal_path.exists());

    let repeated = assert_passed(run(binary, &apply));
    assert!(repeated.contains("\"reason_code\":\"already_applied\""));

    let stale_manifest = fs::read_to_string(current.join("npa-package.toml"))
        .unwrap()
        .replace("version = \"0.1.1\"", "version = \"0.1.2\"");
    fs::write(current.join("npa-package.toml"), stale_manifest).unwrap();
    assert!(!run(binary, &apply).status.success());
}

#[test]
fn reconciliation_covers_legacy_revision_and_three_catalog_additions() {
    let temporary = TempRoot(std::env::temp_dir().join(format!(
        "npa-registry-topology-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    )));
    fs::create_dir(&temporary.0).unwrap();
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = repository.join("testdata/package/npa-mathlib-declaration-baseline");
    let previous = temporary.0.join("previous");
    let current = temporary.0.join("current");
    copy_tree(&fixture, &previous);
    copy_tree(&fixture, &current);
    let binary = Path::new(env!("CARGO_BIN_EXE_npa"));
    prepare_module_package(binary, &previous, "0.2.1", &["Mathlib.Legacy"]);
    prepare_module_package(
        binary,
        &current,
        "0.2.4",
        &[
            "Mathlib.Legacy",
            "Mathlib.NewOne",
            "Mathlib.NewTwo",
            "Mathlib.NewThree",
        ],
    );
    let registry = write_legacy_registry(&previous);
    fs::write(previous.join("promotion-origins.json"), &registry).unwrap();
    fs::write(current.join("promotion-origins.json"), &registry).unwrap();
    fs::create_dir_all(current.join("docs/promotion")).unwrap();
    fs::write(
        current.join("docs/promotion/audit.md"),
        "catalog topology reconciliation audit\n",
    )
    .unwrap();

    assert_passed(run(
        binary,
        &[
            OsStr::new("package"),
            OsStr::new("reconcile-promotion-origin-registry"),
            OsStr::new("--root"),
            current.as_os_str(),
            OsStr::new("--previous-target-root"),
            previous.as_os_str(),
            OsStr::new("--audit"),
            OsStr::new("docs/promotion/audit.md"),
            OsStr::new("--out"),
            OsStr::new("docs/promotion/topology-sync.json"),
            OsStr::new("--apply"),
            OsStr::new("--json"),
        ],
    ));
    let reconciled = parse_promotion_origin_registry_v3_json(
        &fs::read_to_string(current.join("promotion-origins.json")).unwrap(),
    )
    .unwrap();
    let event = reconciled.catalog_change_events.last().unwrap();
    assert_eq!(event.revised_routes.len(), 1);
    assert_eq!(
        event.revised_routes[0].target_module,
        Name::from_dotted("Mathlib.Legacy")
    );
    assert_eq!(event.added_targets.len(), 3);
}
