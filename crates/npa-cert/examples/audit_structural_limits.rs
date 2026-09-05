use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    io::{self, BufRead, BufReader, Read, Write},
    process::{self, Command, Stdio},
};

use npa_cert::{
    audit_certificate_structural_limits, verify_module_cert_hashes, CertificateStructuralAudit,
    CertificateStructuralImportAudit, Hash, Name, MAX_CERTIFICATE_BYTES,
    MAX_CERTIFICATE_EXPANDED_NODES, MAX_CLOSURE_EXPANDED_NODES, MAX_CLOSURE_MODULES,
    MAX_DECLARATIONS, MAX_EXPORTS, MAX_IMPORTS, MAX_LEVEL_TABLE_NODES, MAX_NAME_TABLE_ENTRIES,
    MAX_NESTED_VECTOR_ENTRIES, MAX_ROOT_EXPANDED_NODES, MAX_STRUCTURAL_DEPTH, MAX_TERM_TABLE_NODES,
};

#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;

use closed_private_tree::InvocationReadRoot;

const MAX_DEPENDENCY_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;

#[derive(Clone)]
struct Maximum {
    limit: usize,
    observed: usize,
    module: String,
    certificate_hash: String,
    path: String,
}

struct AuditRecord {
    path: String,
    audit: CertificateStructuralAudit,
    root: bool,
}

type FullIdentity = (Name, Hash, Hash);
type ExportIdentity = (Name, Hash);

#[derive(Debug)]
struct ResolvedAuditNode {
    record: usize,
    identity: FullIdentity,
}

fn full_identity(audit: &CertificateStructuralAudit) -> FullIdentity {
    (
        audit.module.clone(),
        audit.export_hash,
        audit.certificate_hash,
    )
}

fn common_path_prefix_len(lhs: &str, rhs: &str) -> usize {
    lhs.split(['/', '\\'])
        .zip(rhs.split(['/', '\\']))
        .take_while(|(lhs, rhs)| lhs == rhs)
        .count()
}

fn nearest_candidate(
    records: &[AuditRecord],
    owner: usize,
    candidates: &[usize],
    allow_distinct_identities: bool,
) -> Result<usize, String> {
    let best_score = candidates
        .iter()
        .map(|candidate| {
            (
                common_path_prefix_len(&records[owner].path, &records[*candidate].path),
                records[*candidate].root,
            )
        })
        .max()
        .ok_or_else(|| "no tracked candidate".to_owned())?;
    let mut best = candidates
        .iter()
        .copied()
        .filter(|candidate| {
            (
                common_path_prefix_len(&records[owner].path, &records[*candidate].path),
                records[*candidate].root,
            ) == best_score
        })
        .collect::<Vec<_>>();
    best.sort_by(|lhs, rhs| records[*lhs].path.cmp(&records[*rhs].path));
    if !allow_distinct_identities {
        let identities = best
            .iter()
            .map(|candidate| full_identity(&records[*candidate].audit))
            .collect::<BTreeSet<_>>();
        if identities.len() > 1 {
            return Err(format!(
                "ambiguous unhashed import from {}: {} equally near tracked identities",
                records[owner].path,
                identities.len()
            ));
        }
    }
    best.first()
        .copied()
        .ok_or_else(|| "no tracked candidate".to_owned())
}

fn resolve_import(
    records: &[AuditRecord],
    exact: &BTreeMap<FullIdentity, Vec<usize>>,
    exports: &BTreeMap<ExportIdentity, Vec<usize>>,
    owner: usize,
    import: &CertificateStructuralImportAudit,
) -> Result<ResolvedAuditNode, String> {
    if let Some(certificate_hash) = import.certificate_hash {
        let key = (import.module.clone(), import.export_hash, certificate_hash);
        if let Some(candidates) = exact.get(&key) {
            return Ok(ResolvedAuditNode {
                record: nearest_candidate(records, owner, candidates, true)?,
                identity: key,
            });
        }
        Err(format!(
            "unresolved exact import {} export={} certificate={} from {} (certificate={})",
            import.module.0.join("."),
            hex(&import.export_hash),
            hex(&certificate_hash),
            records[owner].path,
            hex(&records[owner].audit.certificate_hash)
        ))
    } else {
        let key = (import.module.clone(), import.export_hash);
        let candidates = exports.get(&key).ok_or_else(|| {
            format!(
                "unresolved export import {} export={} from {} (certificate={})",
                import.module.0.join("."),
                hex(&import.export_hash),
                records[owner].path,
                hex(&records[owner].audit.certificate_hash)
            )
        })?;
        let record = nearest_candidate(records, owner, candidates, false)?;
        Ok(ResolvedAuditNode {
            record,
            identity: full_identity(&records[record].audit),
        })
    }
}

fn closure_measurements(
    records: &[AuditRecord],
    exact: &BTreeMap<FullIdentity, Vec<usize>>,
    exports: &BTreeMap<ExportIdentity, Vec<usize>>,
    root: usize,
) -> Result<(usize, usize), String> {
    let mut visited = BTreeSet::new();
    let mut pending = vec![ResolvedAuditNode {
        record: root,
        identity: full_identity(&records[root].audit),
    }];
    let mut expanded_nodes = 0usize;
    while let Some(ResolvedAuditNode { record, identity }) = pending.pop() {
        if !visited.insert(identity) {
            continue;
        }
        expanded_nodes =
            expanded_nodes.saturating_add(records[record].audit.certificate_expanded_nodes);
        for import in &records[record].audit.direct_imports {
            pending.push(resolve_import(records, exact, exports, record, import)?);
        }
    }
    Ok((visited.len(), expanded_nodes))
}

fn parse_hash(value: &str, field: &str, line: usize) -> Result<Hash, String> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!(
            "dependency manifest line {line} has invalid {field}"
        ));
    }
    let mut hash = [0; 32];
    for (index, byte) in hash.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).map_err(|error| {
            format!("dependency manifest line {line} has invalid {field}: {error}")
        })?;
    }
    Ok(hash)
}

fn load_committed_dependencies(
    records: &mut Vec<AuditRecord>,
    inputs: &InvocationReadRoot,
    manifest_path: &str,
) -> Result<(), String> {
    let manifest = String::from_utf8(inputs.read(
        std::path::Path::new(manifest_path),
        MAX_DEPENDENCY_MANIFEST_BYTES,
        "dependency manifest",
    )?)
    .map_err(|_| format!("dependency manifest {manifest_path} is not UTF-8"))?;
    let mut lines = manifest.lines();
    let expected_header =
        "module\texport_hash\tcertificate_hash\tsource_repository\tsource_commit\tsource_path\tfixture_path";
    if lines.next() != Some(expected_header) {
        return Err(format!(
            "dependency manifest {manifest_path} has an invalid header"
        ));
    }
    let mut identities = BTreeSet::new();
    for (offset, line) in lines.enumerate() {
        let line_number = offset + 2;
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 7 || fields.iter().any(|field| field.is_empty()) {
            return Err(format!(
                "dependency manifest line {line_number} must contain seven non-empty fields"
            ));
        }
        let expected_identity = (
            Name::from_dotted(fields[0]),
            parse_hash(fields[1], "export_hash", line_number)?,
            parse_hash(fields[2], "certificate_hash", line_number)?,
        );
        if !identities.insert(expected_identity.clone()) {
            return Err(format!(
                "dependency manifest line {line_number} repeats certificate identity {}",
                fields[0]
            ));
        }
        if fields[3] != "https://github.com/finitefield-org/npa-mathlib"
            || fields[4].len() != 40
            || !fields[4].bytes().all(|byte| byte.is_ascii_hexdigit())
            || !fields[5].ends_with("/certificate.npcert")
        {
            return Err(format!(
                "dependency manifest line {line_number} has invalid source provenance"
            ));
        }
        let fixture_path = std::path::Path::new(manifest_path)
            .parent()
            .ok_or_else(|| format!("dependency manifest {manifest_path} has no parent directory"))?
            .join(fields[6]);
        let fixture_display = fixture_path.to_string_lossy();
        let bytes = inputs
            .read(
                &fixture_path,
                u64::try_from(MAX_CERTIFICATE_BYTES).map_err(|error| error.to_string())?,
                "dependency certificate",
            )
            .map_err(|error| format!("failed to read {fixture_display}: {error}"))?;
        verify_module_cert_hashes(&bytes).map_err(|error| {
            format!("failed to validate hashes for {fixture_display}: {error:?}")
        })?;
        let audit = audit_certificate_structural_limits(&bytes)
            .map_err(|error| format!("failed to audit {fixture_display}: {error:?}"))?;
        if full_identity(&audit) != expected_identity {
            return Err(format!(
                "dependency manifest identity does not match {fixture_display}"
            ));
        }
        records.push(AuditRecord {
            path: fixture_display.into_owned(),
            audit,
            root: false,
        });
    }
    if identities.is_empty() {
        return Err(format!(
            "dependency manifest {manifest_path} contains no dependencies"
        ));
    }
    Ok(())
}

fn load_head_history_dependencies(records: &mut Vec<AuditRecord>) -> Result<(), String> {
    let shallow = Command::new("/usr/bin/git")
        .args(["rev-parse", "--is-shallow-repository"])
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        .output()
        .map_err(|error| format!("failed to inspect Git clone depth: {error}"))?;
    if !shallow.status.success() {
        return Err(format!(
            "failed to inspect Git clone depth: {}",
            String::from_utf8_lossy(&shallow.stderr).trim()
        ));
    }
    match String::from_utf8_lossy(&shallow.stdout).trim() {
        "false" => {}
        "true" => {
            return Err(
                "certificate closure audit requires the complete HEAD ancestry; shallow clones are unsupported"
                    .to_owned(),
            );
        }
        value => {
            return Err(format!(
                "unexpected Git shallow-repository response: {value}"
            ));
        }
    }

    let listed = Command::new("/usr/bin/git")
        .args(["rev-list", "--objects", "HEAD"])
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        .output()
        .map_err(|error| format!("failed to list HEAD Git objects: {error}"))?;
    if !listed.status.success() {
        return Err(format!(
            "failed to list HEAD Git objects: {}",
            String::from_utf8_lossy(&listed.stderr).trim()
        ));
    }

    let mut objects = BTreeMap::<String, String>::new();
    for line in String::from_utf8(listed.stdout)
        .map_err(|error| format!("HEAD Git object list is not UTF-8: {error}"))?
        .lines()
    {
        let Some((object, path)) = line.split_once(' ') else {
            continue;
        };
        if path.ends_with(".npcert") {
            objects
                .entry(object.to_owned())
                .and_modify(|current| {
                    if path < current {
                        *current = path.to_owned();
                    }
                })
                .or_insert_with(|| path.to_owned());
        }
    }

    let mut child = Command::new("/usr/bin/git")
        .args(["cat-file", "--batch"])
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start Git object reader: {error}"))?;
    let mut input = child
        .stdin
        .take()
        .ok_or_else(|| "Git object reader has no stdin".to_owned())?;
    let mut output = BufReader::new(
        child
            .stdout
            .take()
            .ok_or_else(|| "Git object reader has no stdout".to_owned())?,
    );

    for (object, path) in objects {
        writeln!(input, "{object}")
            .and_then(|()| input.flush())
            .map_err(|error| format!("failed to request Git object {object}: {error}"))?;
        let mut header = String::new();
        output
            .read_line(&mut header)
            .map_err(|error| format!("failed to read Git object header for {object}: {error}"))?;
        let fields = header.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[1] != "blob" {
            return Err(format!(
                "unexpected Git object header for {object}: {}",
                header.trim_end()
            ));
        }
        let size = fields[2]
            .parse::<usize>()
            .map_err(|error| format!("invalid Git object size for {object}: {error}"))?;
        let bytes = if size <= MAX_CERTIFICATE_BYTES {
            let mut bytes = vec![0; size];
            output
                .read_exact(&mut bytes)
                .map_err(|error| format!("failed to read Git object {object}: {error}"))?;
            Some(bytes)
        } else {
            let copied = io::copy(
                &mut Read::by_ref(&mut output).take(size as u64),
                &mut io::sink(),
            )
            .map_err(|error| format!("failed to skip oversized Git object {object}: {error}"))?;
            if copied != size as u64 {
                return Err(format!(
                    "oversized Git object {object} ended after {copied} of {size} bytes"
                ));
            }
            None
        };
        let mut separator = [0];
        output
            .read_exact(&mut separator)
            .map_err(|error| format!("failed to finish Git object {object}: {error}"))?;
        if separator != *b"\n" {
            return Err(format!("Git object {object} has no batch separator"));
        }
        let Some(bytes) = bytes else {
            continue;
        };
        if verify_module_cert_hashes(&bytes).is_err() {
            continue;
        }
        let Ok(audit) = audit_certificate_structural_limits(&bytes) else {
            continue;
        };
        records.push(AuditRecord {
            path,
            audit,
            root: false,
        });
    }
    drop(input);
    drop(output);
    let status = child
        .wait()
        .map_err(|error| format!("failed to wait for Git object reader: {error}"))?;
    if !status.success() {
        return Err(format!("Git object reader exited with {status}"));
    }
    Ok(())
}

fn measurements(
    audit: &CertificateStructuralAudit,
    closure_modules: usize,
    closure_expanded_nodes: usize,
) -> [(&'static str, usize, usize); 13] {
    [
        (
            "certificate_bytes",
            MAX_CERTIFICATE_BYTES,
            audit.certificate_bytes,
        ),
        ("imports", MAX_IMPORTS, audit.imports),
        (
            "name_table_entries",
            MAX_NAME_TABLE_ENTRIES,
            audit.name_table_entries,
        ),
        (
            "level_table_nodes",
            MAX_LEVEL_TABLE_NODES,
            audit.level_table_nodes,
        ),
        (
            "term_table_nodes",
            MAX_TERM_TABLE_NODES,
            audit.term_table_nodes,
        ),
        ("declarations", MAX_DECLARATIONS, audit.declarations),
        ("exports", MAX_EXPORTS, audit.exports),
        (
            "nested_vector_entries",
            MAX_NESTED_VECTOR_ENTRIES,
            audit.nested_vector_entries,
        ),
        (
            "structural_depth",
            MAX_STRUCTURAL_DEPTH,
            audit.structural_depth,
        ),
        (
            "root_expanded_nodes",
            MAX_ROOT_EXPANDED_NODES,
            audit.root_expanded_nodes,
        ),
        (
            "certificate_expanded_nodes",
            MAX_CERTIFICATE_EXPANDED_NODES,
            audit.certificate_expanded_nodes,
        ),
        ("closure_modules", MAX_CLOSURE_MODULES, closure_modules),
        (
            "closure_expanded_nodes",
            MAX_CLOSURE_EXPANDED_NODES,
            closure_expanded_nodes,
        ),
    ]
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write;
        write!(&mut encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

fn main() {
    let mut maxima = BTreeMap::<&'static str, Maximum>::new();
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let dependency_manifest = match arguments.as_slice() {
        [flag, manifest] if flag == "--stdin0-with-dependencies" => Some(manifest.clone()),
        _ => None,
    };
    let paths = if arguments == ["--stdin0"] || dependency_manifest.is_some() {
        let mut input = Vec::new();
        io::stdin().read_to_end(&mut input).unwrap_or_else(|error| {
            eprintln!("failed to read tracked paths: {error}");
            process::exit(1);
        });
        input
            .split(|byte| *byte == 0)
            .filter(|path| !path.is_empty())
            .map(|path| {
                String::from_utf8(path.to_vec()).unwrap_or_else(|error| {
                    eprintln!("tracked path is not UTF-8: {error}");
                    process::exit(1);
                })
            })
            .collect()
    } else {
        arguments
    };
    let inputs =
        InvocationReadRoot::current("structural audit transaction").unwrap_or_else(|error| {
            eprintln!("failed to retain structural audit input root: {error}");
            process::exit(1);
        });
    let mut records = Vec::new();
    for path in paths {
        let bytes = inputs
            .read(
                std::path::Path::new(&path),
                u64::try_from(MAX_CERTIFICATE_BYTES).expect("certificate limit fits u64"),
                "certificate audit input",
            )
            .unwrap_or_else(|error| {
                eprintln!("failed to read {path}: {error}");
                process::exit(1);
            });
        let audit = audit_certificate_structural_limits(&bytes).unwrap_or_else(|error| {
            eprintln!("failed to audit {path}: {error:?}");
            process::exit(1);
        });
        records.push(AuditRecord {
            path,
            audit,
            root: true,
        });
    }
    if let Some(manifest_path) = dependency_manifest {
        load_committed_dependencies(&mut records, &inputs, &manifest_path).unwrap_or_else(
            |error| {
                eprintln!("failed to load committed certificate dependencies: {error}");
                process::exit(1);
            },
        );
        load_head_history_dependencies(&mut records).unwrap_or_else(|error| {
            eprintln!("failed to load HEAD certificate history: {error}");
            process::exit(1);
        });
    }
    inputs
        .verify("structural audit transaction")
        .unwrap_or_else(|error| {
            eprintln!("structural audit input tree changed during the audit: {error}");
            process::exit(1);
        });
    let mut exact = BTreeMap::<FullIdentity, Vec<usize>>::new();
    let mut exports = BTreeMap::<ExportIdentity, Vec<usize>>::new();
    for (index, record) in records.iter().enumerate() {
        exact
            .entry(full_identity(&record.audit))
            .or_default()
            .push(index);
        exports
            .entry((record.audit.module.clone(), record.audit.export_hash))
            .or_default()
            .push(index);
    }
    for candidates in exact.values() {
        let first = &records[candidates[0]].audit;
        if candidates.iter().skip(1).any(|candidate| {
            let audit = &records[*candidate].audit;
            audit.certificate_expanded_nodes != first.certificate_expanded_nodes
                || audit.direct_imports != first.direct_imports
        }) {
            eprintln!(
                "conflicting structural metadata for certificate identity {}",
                first.module.0.join(".")
            );
            process::exit(1);
        }
    }
    for (index, record) in records.iter().enumerate().filter(|(_, record)| record.root) {
        let path = &record.path;
        let audit = &record.audit;
        let (closure_modules, closure_expanded_nodes) =
            closure_measurements(&records, &exact, &exports, index).unwrap_or_else(|error| {
                eprintln!("failed to resolve closure for {path}: {error}");
                process::exit(1);
            });
        let module = audit.module.0.join(".");
        let certificate_hash = hex(&audit.certificate_hash);
        for (kind, limit, observed) in measurements(audit, closure_modules, closure_expanded_nodes)
        {
            let replace = maxima.get(kind).is_none_or(|current| {
                observed > current.observed
                    || (observed == current.observed && path.as_str() < current.path.as_str())
            });
            if replace {
                maxima.insert(
                    kind,
                    Maximum {
                        limit,
                        observed,
                        module: module.clone(),
                        certificate_hash: certificate_hash.clone(),
                        path: path.clone(),
                    },
                );
            }
        }
    }
    println!("limit_kind\tlimit\tmaximum\tmodule\tcertificate_hash\tpath");
    let mut blocked = false;
    for (kind, maximum) in maxima {
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}",
            kind,
            maximum.limit,
            maximum.observed,
            maximum.module,
            maximum.certificate_hash,
            maximum.path
        );
        if maximum.observed.saturating_mul(2) >= maximum.limit {
            eprintln!(
                "{kind} maximum {} is at or above 50% of limit {}",
                maximum.observed, maximum.limit
            );
            blocked = true;
        }
    }
    if blocked {
        process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct CurrentDirectoryGuard(std::path::PathBuf);

    impl CurrentDirectoryGuard {
        fn change_to(path: &std::path::Path) -> Self {
            let original = std::env::current_dir().unwrap();
            std::env::set_current_dir(path).unwrap();
            Self(original)
        }
    }

    impl Drop for CurrentDirectoryGuard {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.0).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn structural_audit_input_reader_rejects_links_oversized_and_root_replacement() {
        use std::os::unix::fs::symlink;

        let current = std::env::current_dir().unwrap().canonicalize().unwrap();
        let root = current.join(format!(
            "npa-structural-audit-reader-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("real")).unwrap();
        std::fs::write(root.join("real/certificate.npcert"), b"cert").unwrap();
        let maximum = u64::try_from(MAX_CERTIFICATE_BYTES).unwrap();
        let inputs = InvocationReadRoot::current("test audit transaction").unwrap();
        let relative_root = root.strip_prefix(&current).unwrap();
        assert_eq!(
            inputs
                .read(
                    &relative_root.join("real/certificate.npcert"),
                    maximum,
                    "test certificate",
                )
                .unwrap(),
            b"cert"
        );
        symlink(root.join("real"), root.join("linked")).unwrap();
        assert!(inputs
            .read(
                &relative_root.join("linked/certificate.npcert"),
                maximum,
                "linked certificate",
            )
            .is_err());
        let oversized = std::fs::File::create(root.join("real/oversized.npcert")).unwrap();
        oversized.set_len(maximum + 1).unwrap();
        assert!(inputs
            .read(
                &relative_root.join("real/oversized.npcert"),
                maximum,
                "oversized certificate",
            )
            .is_err());
        assert!(inputs
            .read(
                std::path::Path::new("../escape.npcert"),
                maximum,
                "escaping certificate",
            )
            .is_err());
        let relocated = root.with_extension("relocated");
        std::fs::rename(&root, &relocated).unwrap();
        std::fs::create_dir_all(root.join("real")).unwrap();
        std::fs::write(root.join("real/certificate.npcert"), b"replacement").unwrap();
        assert!(inputs.verify("test audit transaction").is_err());
        assert_eq!(
            std::fs::read(relocated.join("real/certificate.npcert")).unwrap(),
            b"cert"
        );
        assert_eq!(
            std::fs::read(root.join("real/certificate.npcert")).unwrap(),
            b"replacement"
        );
        std::fs::remove_dir_all(root).unwrap();
        std::fs::remove_dir_all(relocated).unwrap();
    }

    fn record(module: &str, export: u8, certificate: u8, root: bool) -> AuditRecord {
        AuditRecord {
            path: format!("proofs/{module}/certificate.npcert"),
            audit: CertificateStructuralAudit {
                module: Name::from_dotted(module),
                export_hash: [export; 32],
                certificate_hash: [certificate; 32],
                direct_imports: vec![],
                certificate_bytes: 1,
                imports: 0,
                name_table_entries: 0,
                level_table_nodes: 0,
                term_table_nodes: 0,
                declarations: 0,
                exports: 0,
                nested_vector_entries: 0,
                structural_depth: 0,
                root_expanded_nodes: 0,
                certificate_expanded_nodes: 1,
            },
            root,
        }
    }

    fn indexes(
        records: &[AuditRecord],
    ) -> (
        BTreeMap<FullIdentity, Vec<usize>>,
        BTreeMap<ExportIdentity, Vec<usize>>,
    ) {
        let mut exact = BTreeMap::<FullIdentity, Vec<usize>>::new();
        let mut exports = BTreeMap::<ExportIdentity, Vec<usize>>::new();
        for (index, record) in records.iter().enumerate() {
            exact
                .entry(full_identity(&record.audit))
                .or_default()
                .push(index);
            exports
                .entry((record.audit.module.clone(), record.audit.export_hash))
                .or_default()
                .push(index);
        }
        (exact, exports)
    }

    #[test]
    fn unavailable_exact_import_does_not_substitute_same_module() {
        let records = vec![
            record("Owner", 1, 1, true),
            record("Dependency", 2, 2, true),
        ];
        let (exact, exports) = indexes(&records);
        let import = CertificateStructuralImportAudit {
            module: Name::from_dotted("Dependency"),
            export_hash: [2; 32],
            certificate_hash: Some([3; 32]),
        };

        assert!(resolve_import(&records, &exact, &exports, 0, &import)
            .unwrap_err()
            .contains("unresolved exact import"));
    }

    #[test]
    fn exact_import_can_resolve_historical_dependency() {
        let records = vec![
            record("Owner", 1, 1, true),
            record("Dependency", 2, 3, false),
        ];
        let (exact, exports) = indexes(&records);
        let import = CertificateStructuralImportAudit {
            module: Name::from_dotted("Dependency"),
            export_hash: [2; 32],
            certificate_hash: Some([3; 32]),
        };

        assert_eq!(
            resolve_import(&records, &exact, &exports, 0, &import)
                .unwrap()
                .record,
            1
        );
    }

    #[test]
    fn unavailable_exact_import_without_module_evidence_fails_closed() {
        let records = vec![record("Owner", 1, 1, true)];
        let (exact, exports) = indexes(&records);
        let import = CertificateStructuralImportAudit {
            module: Name::from_dotted("Dependency"),
            export_hash: [2; 32],
            certificate_hash: Some([3; 32]),
        };

        assert!(resolve_import(&records, &exact, &exports, 0, &import)
            .unwrap_err()
            .contains("unresolved exact import"));
    }

    #[test]
    fn unresolved_unhashed_import_fails_closed() {
        let records = vec![record("Owner", 1, 1, true)];
        let (exact, exports) = indexes(&records);
        let import = CertificateStructuralImportAudit {
            module: Name::from_dotted("Dependency"),
            export_hash: [2; 32],
            certificate_hash: None,
        };

        assert!(resolve_import(&records, &exact, &exports, 0, &import)
            .unwrap_err()
            .contains("unresolved export import"));
    }

    #[test]
    fn retired_committed_dependency_manifest_is_not_current_input() {
        let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .unwrap()
            .join("testdata/certificate-structural-history/dependencies.tsv");
        let mut records = Vec::new();
        let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .unwrap();
        let _current = CurrentDirectoryGuard::change_to(&workspace);
        let inputs = InvocationReadRoot::current("committed dependency test").unwrap();
        let manifest = manifest.strip_prefix(&workspace).unwrap();
        let error = load_committed_dependencies(&mut records, &inputs, manifest.to_str().unwrap())
            .expect_err("retired certificate history must not decode as current input");

        assert!(records.is_empty());
        assert!(error.contains(
            "UnsupportedFormat { format: \"NPA-CERT-0.1\", core_spec: \"NPA-Core-0.1\" }"
        ));
    }
}
