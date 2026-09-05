use std::env;
use std::path::{Component, Path, PathBuf};
use std::process;

use npa_api::{
    format_hash_string, independent_checker_file_hash,
    independent_checker_validate_selected_checker_identity_manifest,
    parse_independent_checker_axiom_policy_toml, parse_independent_checker_binary_registry,
    parse_independent_checker_identity_manifest, parse_independent_checker_runner_policy,
    IndependentCheckerBinaryRegistryRootKind,
};
use npa_cli::fs::BoundedReadRoot;

const RUNNER_ID: &str = "npa-cli-package-external-runner";
const RUNNER_VERSION: &str = "0.1.0";
const MAX_POLICY_BYTES: u64 = 4 * 1024 * 1024;
const MAX_IDENTITY_BYTES: u64 = 4 * 1024 * 1024;
const MAX_REGISTRY_BYTES: u64 = 4 * 1024 * 1024;
const MAX_AXIOM_POLICY_BYTES: u64 = 4 * 1024 * 1024;
const MAX_CHECKER_BINARY_BYTES: u64 = 1024 * 1024 * 1024;

fn output_schema() -> &'static str {
    match env!("CARGO_CRATE_NAME") {
        "inspect_ext_v0_3_policy" => "npa.checker_ext.toolchain_v0_3.policy_preflight.v1",
        "inspect_ext_v0_4_policy" => "npa.checker_ext.toolchain_v0_4.policy_preflight.v1",
        "inspect_ext_v0_5_policy" => "npa.checker_ext.toolchain_v0_5.policy_preflight.v1",
        "inspect_ext_v0_6_policy" => "npa.checker_ext.toolchain_v0_6.policy_preflight.v1",
        "inspect_ext_current_policy" => "npa.checker_ext.toolchain_v0_9.policy_preflight.v1",
        name => panic!("unsupported versioned preflight example: {name}"),
    }
}

fn expected_external_checker_version() -> &'static str {
    match env!("CARGO_CRATE_NAME") {
        "inspect_ext_v0_3_policy"
        | "inspect_ext_v0_4_policy"
        | "inspect_ext_v0_5_policy"
        | "inspect_ext_v0_6_policy" => "0.2.0",
        "inspect_ext_current_policy" => "0.4.0",
        name => panic!("unsupported versioned preflight example: {name}"),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Inputs {
    root: PathBuf,
    runner_policy: PathBuf,
    checker_registry: PathBuf,
}

fn parse_inputs<I>(args: I) -> Result<Inputs, String>
where
    I: IntoIterator<Item = String>,
{
    let mut root = None;
    let mut runner_policy = None;
    let mut checker_registry = None;
    let mut args = args.into_iter();
    while let Some(flag) = args.next() {
        let slot = match flag.as_str() {
            "--root" => &mut root,
            "--runner-policy" => &mut runner_policy,
            "--checker-registry" => &mut checker_registry,
            _ => return Err(format!("unknown argument: {flag}")),
        };
        if slot.is_some() {
            return Err(format!("duplicate argument: {flag}"));
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {flag}"))?;
        if value.starts_with("--") {
            return Err(format!("missing value for {flag}"));
        }
        *slot = Some(value);
    }
    Ok(Inputs {
        root: PathBuf::from(root.ok_or("missing required --root")?),
        runner_policy: PathBuf::from(runner_policy.ok_or("missing required --runner-policy")?),
        checker_registry: PathBuf::from(
            checker_registry.ok_or("missing required --checker-registry")?,
        ),
    })
}

fn checked_locator(locator: &Path) -> Result<&Path, String> {
    if locator.as_os_str().is_empty()
        || locator.is_absolute()
        || locator
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "locator must be nonempty canonical relative path: {}",
            locator.display()
        ));
    }
    Ok(locator)
}

fn read_bytes(root: &BoundedReadRoot, path: &Path, maximum_bytes: u64) -> Result<Vec<u8>, String> {
    root.read(checked_locator(path)?, maximum_bytes)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))
}

fn json_string(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character < ' ' => {
                output.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

fn inspect(inputs: &Inputs) -> Result<String, String> {
    let root = BoundedReadRoot::open(&inputs.root)
        .map_err(|error| format!("cannot open root {}: {error}", inputs.root.display()))?;
    let policy_path = checked_locator(&inputs.runner_policy)?;
    let registry_path = checked_locator(&inputs.checker_registry)?;
    let policy_bytes = read_bytes(&root, policy_path, MAX_POLICY_BYTES)?;
    let policy_source = String::from_utf8(policy_bytes.clone())
        .map_err(|_| format!("runner policy is not UTF-8: {}", policy_path.display()))?;
    let policy = parse_independent_checker_runner_policy(&policy_source)
        .map_err(|error| format!("runner policy invalid: {error:?}"))?;
    if policy.required_checker_profiles != ["fast-kernel", "reference", "external"] {
        return Err("required checker profile order mismatch".to_owned());
    }
    let allowlist_profiles = policy
        .checker_allowlist
        .iter()
        .map(|entry| entry.profile.as_str())
        .collect::<Vec<_>>();
    if allowlist_profiles != ["external", "fast-kernel", "reference"] {
        return Err("checker allowlist is not bytewise ascending".to_owned());
    }

    let identity_reference = policy
        .checker_identity_manifest
        .as_ref()
        .ok_or("runner policy is missing checker identity manifest")?;
    let identity_path = checked_locator(Path::new(&identity_reference.path))?;
    let identity_bytes = read_bytes(&root, identity_path, MAX_IDENTITY_BYTES)?;
    let identity_hash = independent_checker_file_hash(&identity_bytes);
    if identity_hash != identity_reference.manifest_hash {
        return Err("identity manifest raw hash mismatch".to_owned());
    }
    let identity_source = String::from_utf8(identity_bytes).map_err(|_| {
        format!(
            "identity manifest is not UTF-8: {}",
            identity_path.display()
        )
    })?;
    let identity = parse_independent_checker_identity_manifest(&identity_source)
        .map_err(|error| format!("identity manifest invalid: {error:?}"))?;
    let identity_profiles = identity
        .checkers
        .iter()
        .map(|entry| entry.profile.as_str())
        .collect::<Vec<_>>();
    if identity_profiles != ["external", "fast-kernel", "reference"] {
        return Err("identity manifest is not bytewise ascending".to_owned());
    }
    for selected in &policy.checker_allowlist {
        independent_checker_validate_selected_checker_identity_manifest(selected, &identity)
            .map_err(|error| format!("identity selection mismatch: {error:?}"))?;
    }
    let expected_runner_build_hash =
        independent_checker_file_hash(format!("{RUNNER_ID}:{RUNNER_VERSION}").as_bytes());
    if identity.generated_by.runner_id != RUNNER_ID
        || identity.generated_by.runner_version != RUNNER_VERSION
        || identity.generated_by.runner_build_hash != expected_runner_build_hash
    {
        return Err("identity generated_by does not match package runner".to_owned());
    }

    let external_selected = policy
        .selected_checker_policy("external")
        .ok_or("runner policy is missing external checker")?;
    let external_identity = identity
        .checkers
        .iter()
        .find(|entry| entry.profile == "external")
        .ok_or("identity manifest is missing external checker")?;
    let expected_external_version = expected_external_checker_version();
    if external_identity.checker_version.as_deref() != Some(expected_external_version) {
        return Err(format!(
            "external checker version is not {expected_external_version}"
        ));
    }
    if identity
        .checkers
        .iter()
        .filter(|entry| entry.profile != "external")
        .any(|entry| entry.checker_version.is_some())
    {
        return Err("fixture-only checker identity carries a version".to_owned());
    }

    let registry_bytes = read_bytes(&root, registry_path, MAX_REGISTRY_BYTES)?;
    let registry_source = String::from_utf8(registry_bytes.clone())
        .map_err(|_| format!("checker registry is not UTF-8: {}", registry_path.display()))?;
    let registry = parse_independent_checker_binary_registry(&registry_source)
        .map_err(|error| format!("checker registry invalid: {error:?}"))?;
    if registry.root_kind != IndependentCheckerBinaryRegistryRootKind::Workspace
        || registry.entries.len() != 1
    {
        return Err("checker registry must have one workspace entry".to_owned());
    }
    let registry_entry = &registry.entries[0];
    if registry_entry.binary_id != external_selected.binary_id {
        return Err("checker registry binary id mismatch".to_owned());
    }
    let checker_path = checked_locator(Path::new(&registry_entry.path))?;
    let checker_hash =
        independent_checker_file_hash(&read_bytes(&root, checker_path, MAX_CHECKER_BINARY_BYTES)?);
    if checker_hash != external_selected.binary_hash {
        return Err("checker binary raw hash mismatch".to_owned());
    }

    let axiom_path = checked_locator(Path::new(&policy.axiom_policy.path))?;
    let axiom_bytes = read_bytes(&root, axiom_path, MAX_AXIOM_POLICY_BYTES)?;
    if independent_checker_file_hash(&axiom_bytes) != policy.axiom_policy.hash {
        return Err("axiom policy raw hash mismatch".to_owned());
    }
    let axiom_source = String::from_utf8(axiom_bytes)
        .map_err(|_| format!("axiom policy is not UTF-8: {}", axiom_path.display()))?;
    parse_independent_checker_axiom_policy_toml(&axiom_source)
        .map_err(|error| format!("axiom policy invalid: {error:?}"))?;

    Ok(format!(
        concat!(
            "{{\"schema\":{},\"runner_policy_path\":{},",
            "\"runner_policy_sha256\":{},\"runner_policy_file_sha256\":{},",
            "\"identity_manifest_path\":{},\"identity_manifest_sha256\":{},",
            "\"checker_registry_path\":{},\"checker_registry_sha256\":{},",
            "\"axiom_policy_path\":{},\"axiom_policy_sha256\":{},",
            "\"checker_binary_path\":{},\"checker_binary_id\":{},",
            "\"checker_binary_sha256\":{},\"checker_id\":{},",
            "\"checker_version\":{},\"checker_build_hash\":{},",
            "\"runner_id\":{},\"runner_version\":{},\"runner_build_hash\":{}}}"
        ),
        json_string(output_schema()),
        json_string(&inputs.runner_policy.to_string_lossy()),
        json_string(&format_hash_string(&policy.policy_hash())),
        json_string(&format_hash_string(&independent_checker_file_hash(
            &policy_bytes
        ))),
        json_string(&identity_reference.path),
        json_string(&format_hash_string(&identity_hash)),
        json_string(&inputs.checker_registry.to_string_lossy()),
        json_string(&format_hash_string(&independent_checker_file_hash(
            &registry_bytes
        ))),
        json_string(&policy.axiom_policy.path),
        json_string(&format_hash_string(&policy.axiom_policy.hash)),
        json_string(&registry_entry.path),
        json_string(&external_selected.binary_id),
        json_string(&format_hash_string(&checker_hash)),
        json_string(&external_selected.checker_id),
        json_string(external_identity.checker_version.as_deref().unwrap()),
        json_string(&format_hash_string(&external_selected.build_hash)),
        json_string(&identity.generated_by.runner_id),
        json_string(&identity.generated_by.runner_version),
        json_string(&format_hash_string(
            &identity.generated_by.runner_build_hash
        )),
    ))
}

fn main() {
    let inputs = parse_inputs(env::args().skip(1)).unwrap_or_else(|error| {
        eprintln!("{}: {error}", env!("CARGO_CRATE_NAME"));
        process::exit(2);
    });
    let output = inspect(&inputs).unwrap_or_else(|error| {
        eprintln!("{}: {error}", env!("CARGO_CRATE_NAME"));
        process::exit(1);
    });
    println!("{output}");
}

#[cfg(test)]
mod tests {
    use super::{
        checked_locator, expected_external_checker_version, output_schema, parse_inputs,
        read_bytes, Inputs, MAX_POLICY_BYTES,
    };
    use std::path::{Path, PathBuf};

    use npa_cli::fs::BoundedReadRoot;

    fn parse(args: &[&str]) -> Result<Inputs, String> {
        parse_inputs(args.iter().map(|arg| (*arg).to_owned()))
    }

    #[test]
    fn parser_accepts_exact_inputs() {
        assert_eq!(
            parse(&[
                "--root",
                "proofs",
                "--runner-policy",
                "ci/runner.release.json",
                "--checker-registry",
                "ci/checker-binaries.json",
            ]),
            Ok(Inputs {
                root: PathBuf::from("proofs"),
                runner_policy: PathBuf::from("ci/runner.release.json"),
                checker_registry: PathBuf::from("ci/checker-binaries.json"),
            })
        );
    }

    #[test]
    fn output_schema_matches_versioned_example_entry_point() {
        let expected = match env!("CARGO_CRATE_NAME") {
            "inspect_ext_v0_3_policy" => "npa.checker_ext.toolchain_v0_3.policy_preflight.v1",
            "inspect_ext_v0_4_policy" => "npa.checker_ext.toolchain_v0_4.policy_preflight.v1",
            "inspect_ext_v0_5_policy" => "npa.checker_ext.toolchain_v0_5.policy_preflight.v1",
            "inspect_ext_v0_6_policy" => "npa.checker_ext.toolchain_v0_6.policy_preflight.v1",
            "inspect_ext_current_policy" => "npa.checker_ext.toolchain_v0_9.policy_preflight.v1",
            name => panic!("unexpected example target: {name}"),
        };
        assert_eq!(output_schema(), expected);
    }

    #[test]
    fn external_checker_version_matches_versioned_example_entry_point() {
        let expected = match env!("CARGO_CRATE_NAME") {
            "inspect_ext_v0_3_policy"
            | "inspect_ext_v0_4_policy"
            | "inspect_ext_v0_5_policy"
            | "inspect_ext_v0_6_policy" => "0.2.0",
            "inspect_ext_current_policy" => "0.4.0",
            name => panic!("unexpected example target: {name}"),
        };
        assert_eq!(expected_external_checker_version(), expected);
    }

    #[test]
    fn parser_rejects_missing_duplicate_unknown_and_flag_values() {
        let complete = [
            "--root",
            "proofs",
            "--runner-policy",
            "ci/runner.release.json",
            "--checker-registry",
            "ci/checker-binaries.json",
        ];
        for flag in ["--root", "--runner-policy", "--checker-registry"] {
            let position = complete.iter().position(|value| *value == flag).unwrap();
            let reduced = complete
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != position && *index != position + 1)
                .map(|(_, value)| *value)
                .collect::<Vec<_>>();
            assert!(parse(&reduced).unwrap_err().contains(flag));
        }
        assert_eq!(
            parse(&["--root", "proofs", "--root", "other"]).unwrap_err(),
            "duplicate argument: --root"
        );
        assert_eq!(
            parse(&["--unknown", "value"]).unwrap_err(),
            "unknown argument: --unknown"
        );
        assert_eq!(
            parse(&["--root", "--runner-policy"]).unwrap_err(),
            "missing value for --root"
        );
    }

    #[test]
    fn checked_locator_rejects_noncanonical_locators() {
        for locator in ["", "/absolute", "../escape", "a/../escape", "./dot"] {
            assert!(checked_locator(Path::new(locator)).is_err(), "{locator}");
        }
        assert_eq!(
            checked_locator(Path::new("ci/policy.json")).unwrap(),
            Path::new("ci/policy.json")
        );
    }

    #[cfg(unix)]
    #[test]
    fn retained_policy_root_rejects_links_and_oversized_inputs() {
        use std::os::unix::fs::symlink;

        let root = std::env::temp_dir().join(format!(
            "npa-inspect-ext-policy-reader-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("real")).unwrap();
        std::fs::write(root.join("real/policy.json"), b"{}\n").unwrap();
        let reader = BoundedReadRoot::open(&root).unwrap();
        assert_eq!(
            read_bytes(&reader, Path::new("real/policy.json"), MAX_POLICY_BYTES).unwrap(),
            b"{}\n"
        );
        symlink(root.join("real"), root.join("linked")).unwrap();
        assert!(read_bytes(&reader, Path::new("linked/policy.json"), MAX_POLICY_BYTES).is_err());
        let oversized = std::fs::File::create(root.join("real/oversized.json")).unwrap();
        oversized.set_len(MAX_POLICY_BYTES + 1).unwrap();
        assert!(read_bytes(&reader, Path::new("real/oversized.json"), MAX_POLICY_BYTES).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
}
