use std::collections::BTreeSet;
use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use npa_cert::{
    verify_module_cert, verify_module_cert_hashes, AxiomPolicy, Hash, ImportEntry, ModuleCert,
    Name, VerifierSession,
};

#[path = "support/policy_toml.rs"]
mod policy_toml;
#[path = "support/source_free_fs.rs"]
mod source_free_fs;

struct Candidate {
    bytes: Vec<u8>,
    certificate: ModuleCert,
}

const MAX_IMPORT_CANDIDATES: usize = 4_096;
const MAX_IMPORT_DEPTH: usize = 1_024;
const MAX_IMPORT_DIRECTORY_DEPTH: usize = 128;
const MAX_IMPORT_DIRECTORY_ENTRIES: usize = 16_384;
const MAX_CERTIFICATE_BYTES: usize = 64 * 1024 * 1024;
const MAX_IMPORT_CANDIDATE_BYTES: usize = MAX_CERTIFICATE_BYTES;

enum BoundedReadError {
    Unavailable,
    ResourceLimit,
}

fn is_source_or_replay_path(path: &Path) -> bool {
    source_free_fs::is_source_or_replay_path(path)
}

fn read_bounded_file(path: &Path, limit: usize) -> Result<Vec<u8>, BoundedReadError> {
    match source_free_fs::read_bounded_file(path, limit) {
        Ok(bytes) => Ok(bytes),
        Err(source_free_fs::SourceFreeFsError::ResourceLimit { .. }) => {
            Err(BoundedReadError::ResourceLimit)
        }
        Err(
            source_free_fs::SourceFreeFsError::Unavailable
            | source_free_fs::SourceFreeFsError::Symlink,
        ) => Err(BoundedReadError::Unavailable),
    }
}

fn load_candidates(directory: &Path) -> Result<Vec<Candidate>, ()> {
    if is_source_or_replay_path(directory) {
        return Err(());
    }
    source_free_fs::collect_bounded_files(
        directory,
        std::ffi::OsStr::new("npcert"),
        MAX_IMPORT_DIRECTORY_DEPTH,
        MAX_IMPORT_DIRECTORY_ENTRIES,
        MAX_IMPORT_CANDIDATES,
        MAX_IMPORT_CANDIDATE_BYTES,
        &is_source_or_replay_path,
    )
    .map_err(|_| ())?
    .into_iter()
    .map(|file| prepare_candidate(file.bytes))
    .collect()
}

fn prepare_candidate(bytes: Vec<u8>) -> Result<Candidate, ()> {
    let certificate = verify_module_cert_hashes(&bytes).map_err(|_| ())?;
    Ok(Candidate { bytes, certificate })
}

#[cfg(test)]
fn load_candidates_from_paths_with_budget(
    paths: Vec<PathBuf>,
    max_candidate_bytes: usize,
) -> Result<Vec<Candidate>, ()> {
    let mut total_bytes = 0;
    let mut candidates = Vec::with_capacity(paths.len());
    for path in paths {
        let remaining_bytes = max_candidate_bytes.checked_sub(total_bytes).ok_or(())?;
        let bytes = read_bounded_file(&path, remaining_bytes).map_err(|_| ())?;
        total_bytes = total_bytes.checked_add(bytes.len()).ok_or(())?;
        candidates.push(prepare_candidate(bytes)?);
    }
    Ok(candidates)
}

fn find_candidate(candidates: &[Candidate], import: &ImportEntry) -> Result<usize, ()> {
    let certificate_hash = import.certificate_hash.ok_or(())?;
    let matches = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| {
            candidate.certificate.header.module == import.module
                && candidate.certificate.hashes.export_hash == import.export_hash
                && candidate.certificate.hashes.certificate_hash == certificate_hash
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(()),
    }
}

fn validate_unique_candidates(candidates: &[Candidate]) -> Result<(), ()> {
    let mut seen = BTreeSet::new();
    for candidate in candidates {
        if !seen.insert((
            candidate.certificate.header.module.clone(),
            candidate.certificate.hashes.export_hash,
            candidate.certificate.hashes.certificate_hash,
        )) {
            return Err(());
        }
    }
    Ok(())
}

fn verify_candidate(
    index: usize,
    depth: usize,
    candidates: &[Candidate],
    visiting: &mut BTreeSet<Hash>,
    verified: &mut BTreeSet<Hash>,
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<(), ()> {
    if depth > MAX_IMPORT_DEPTH {
        return Err(());
    }
    let candidate = &candidates[index];
    let identity = candidate.certificate.hashes.certificate_hash;
    if verified.contains(&identity) {
        return Ok(());
    }
    if !visiting.insert(identity) {
        return Err(());
    }
    for import in &candidate.certificate.imports {
        let dependency = find_candidate(candidates, import)?;
        verify_candidate(
            dependency,
            depth + 1,
            candidates,
            visiting,
            verified,
            session,
            policy,
        )?;
    }
    visiting.remove(&identity);
    verify_module_cert(&candidate.bytes, session, policy).map_err(|_| ())?;
    verified.insert(identity);
    Ok(())
}

fn verify_leaf(
    bytes: &[u8],
    import_directory: &Path,
    policy: &AxiomPolicy,
) -> Result<(npa_cert::VerifiedModule, Hash), ()> {
    let certificate = verify_module_cert_hashes(bytes).map_err(|_| ())?;
    let axiom_report_hash = certificate.hashes.axiom_report_hash;
    let candidates = load_candidates(import_directory)?;
    validate_unique_candidates(&candidates)?;
    let mut session = VerifierSession::new();
    let mut visiting = BTreeSet::new();
    let mut verified = BTreeSet::new();
    for import in &certificate.imports {
        let dependency = find_candidate(&candidates, import)?;
        verify_candidate(
            dependency,
            1,
            &candidates,
            &mut visiting,
            &mut verified,
            &mut session,
            policy,
        )?;
    }
    let verified = verify_module_cert(bytes, &mut session, policy).map_err(|_| ())?;
    Ok((verified, axiom_report_hash))
}

fn load_policy(path: &Path) -> Result<AxiomPolicy, ()> {
    let source = String::from_utf8(read_bounded_file(path, MAX_CERTIFICATE_BYTES).map_err(|_| ())?)
        .map_err(|_| ())?;
    let names = policy_toml::parse(&source)?;
    let mut policy = AxiomPolicy::high_trust();
    // The independent checkers treat the exact initial-environment Eq recursor
    // as a standard exception rather than a custom axiom.
    policy
        .allowlisted_axioms
        .insert(Name::from_dotted("Eq.rec"));
    for axiom in names {
        policy.allowlisted_axioms.insert(Name::from_dotted(axiom));
    }
    Ok(policy)
}

fn hash_wire(hash: Hash) -> String {
    let mut wire = String::from("sha256:");
    for byte in hash {
        wire.push_str(&format!("{byte:02x}"));
    }
    wire
}

fn checked_json(module: &npa_cert::VerifiedModule, axiom_report_hash: Hash) -> String {
    format!(
        concat!(
            "{{\n",
            "  \"status\": \"checked\",\n",
            "  \"module\": \"{}\",\n",
            "  \"certificate_hash\": \"{}\",\n",
            "  \"export_hash\": \"{}\",\n",
            "  \"axiom_report_hash\": \"{}\"\n",
            "}}"
        ),
        module.module().as_dotted(),
        hash_wire(module.certificate_hash()),
        hash_wire(module.export_hash()),
        hash_wire(axiom_report_hash),
    )
}

fn main() -> ExitCode {
    let mut arguments = env::args_os().skip(1);
    let Some(certificate_path) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_fast CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    let Some(import_directory) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_fast CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    let Some(policy_path) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: verify_ext_fast CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    };
    if arguments.next().is_some() {
        eprintln!("usage: verify_ext_fast CERTIFICATE IMPORT_DIRECTORY POLICY");
        return ExitCode::from(2);
    }
    if is_source_or_replay_path(&certificate_path)
        || !source_free_fs::is_certificate_path(&certificate_path)
    {
        println!("{{\n  \"status\": \"failed\"\n}}");
        return ExitCode::from(1);
    }
    if is_source_or_replay_path(&policy_path) {
        println!("{{\n  \"status\": \"failed\"\n}}");
        return ExitCode::from(1);
    }
    let bytes = match read_bounded_file(&certificate_path, MAX_CERTIFICATE_BYTES) {
        Ok(bytes) => bytes,
        Err(BoundedReadError::Unavailable) => {
            println!("{{\n  \"status\": \"failed\"\n}}");
            return ExitCode::from(1);
        }
        Err(BoundedReadError::ResourceLimit) => {
            println!("{{\n  \"status\": \"failed\"\n}}");
            return ExitCode::from(1);
        }
    };
    let policy = match load_policy(&policy_path) {
        Ok(policy) => policy,
        Err(()) => {
            println!("{{\n  \"status\": \"failed\"\n}}");
            return ExitCode::from(1);
        }
    };
    match verify_leaf(&bytes, &import_directory, &policy) {
        Ok((module, axiom_report_hash)) => {
            println!("{}", checked_json(&module, axiom_report_hash));
            ExitCode::SUCCESS
        }
        Err(()) => {
            println!("{{\n  \"status\": \"failed\"\n}}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MUTUAL: &[u8] = include_bytes!(
        "../../../checkers/npa-checker-ext/test/fixtures/conformance/mutual-v0.2.npcert"
    );

    #[test]
    fn candidate_preparation_rejects_malformed_and_hash_mismatched_bytes() {
        assert!(prepare_candidate(b"not a certificate".to_vec()).is_err());

        let mut corrupted = MUTUAL.to_vec();
        *corrupted.last_mut().expect("certificate hash trailer") ^= 1;
        assert!(prepare_candidate(corrupted).is_err());
    }

    #[test]
    fn candidate_loading_enforces_aggregate_bytes_and_source_exclusion() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../checkers/npa-checker-ext/test/fixtures/conformance/mutual-v0.2.npcert");
        let aggregate_bytes = MUTUAL.len() * 2;
        assert_eq!(
            load_candidates_from_paths_with_budget(
                vec![fixture.clone(), fixture.clone()],
                aggregate_bytes,
            )
            .expect("exact aggregate byte budget")
            .len(),
            2
        );
        assert!(load_candidates_from_paths_with_budget(
            vec![fixture.clone(), fixture],
            aggregate_bytes - 1,
        )
        .is_err());
        assert!(is_source_or_replay_path(Path::new(
            "/imports/hidden.npa/unrelated.npcert"
        )));
        assert!(is_source_or_replay_path(Path::new(
            "/imports/replay.json/unrelated.npcert"
        )));
        assert!(!is_source_or_replay_path(Path::new(
            "/imports/replay.json.backup/unrelated.npcert"
        )));
        assert!(source_free_fs::is_certificate_path(Path::new(
            "/certs/.npcert"
        )));
        assert!(!source_free_fs::is_certificate_path(Path::new(
            "/certs/module.npa"
        )));
    }
}
