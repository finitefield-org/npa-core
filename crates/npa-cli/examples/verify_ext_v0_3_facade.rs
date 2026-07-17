use std::env;
use std::path::PathBuf;
use std::process;

use npa_cli::args::{
    PackageAuditCacheMode, PackageChecker, PackageLockInputMode, PackageTimingMode,
    PackageVerifierMemoMode,
};
use npa_cli::package_api::v1::{common_options, external_checker_options, verify_certs_full};
use npa_cli::package_verify::run_package_verify_certs;

#[derive(Debug, Eq, PartialEq)]
struct Inputs {
    root: PathBuf,
    runner_policy: PathBuf,
    runner_policy_hash: String,
    checker_registry: PathBuf,
}

fn parse_inputs<I>(args: I) -> Result<Inputs, String>
where
    I: IntoIterator<Item = String>,
{
    let mut root = None;
    let mut runner_policy = None;
    let mut runner_policy_hash = None;
    let mut checker_registry = None;
    let mut args = args.into_iter();

    while let Some(flag) = args.next() {
        let slot = match flag.as_str() {
            "--root" => &mut root,
            "--runner-policy" => &mut runner_policy,
            "--runner-policy-hash" => &mut runner_policy_hash,
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
        runner_policy_hash: runner_policy_hash.ok_or("missing required --runner-policy-hash")?,
        checker_registry: PathBuf::from(
            checker_registry.ok_or("missing required --checker-registry")?,
        ),
    })
}

fn run(inputs: Inputs) -> i32 {
    let external = external_checker_options(
        inputs.runner_policy,
        inputs.runner_policy_hash,
        inputs.checker_registry,
    );
    let request = verify_certs_full(common_options(inputs.root, true), PackageChecker::External)
        .with_jobs(1)
        .with_audit_cache(PackageAuditCacheMode::Off)
        .with_verifier_memo(PackageVerifierMemoMode::Off)
        .with_timings(PackageTimingMode::Off)
        .with_package_lock_mode(PackageLockInputMode::CheckedFile)
        .with_external(external);
    let result = run_package_verify_certs(request);
    println!("{}", result.render_json());
    i32::from(result.exit_code().as_u8())
}

fn main() {
    let inputs = parse_inputs(env::args().skip(1)).unwrap_or_else(|error| {
        eprintln!("{}: {error}", env!("CARGO_CRATE_NAME"));
        process::exit(2);
    });
    process::exit(run(inputs));
}

#[cfg(test)]
mod tests {
    use super::{parse_inputs, Inputs};
    use std::path::PathBuf;

    fn parse(args: &[&str]) -> Result<Inputs, String> {
        parse_inputs(args.iter().map(|arg| (*arg).to_owned()))
    }

    fn valid_args() -> [&'static str; 8] {
        [
            "--root",
            "proofs",
            "--runner-policy",
            "ci/runner.release.json",
            "--runner-policy-hash",
            "sha256:abc",
            "--checker-registry",
            "ci/checker-binaries.json",
        ]
    }

    #[test]
    fn parser_accepts_exact_inputs() {
        assert_eq!(
            parse(&valid_args()),
            Ok(Inputs {
                root: PathBuf::from("proofs"),
                runner_policy: PathBuf::from("ci/runner.release.json"),
                runner_policy_hash: "sha256:abc".to_owned(),
                checker_registry: PathBuf::from("ci/checker-binaries.json"),
            })
        );
    }

    #[test]
    fn parser_rejects_each_missing_input() {
        for flag in [
            "--root",
            "--runner-policy",
            "--runner-policy-hash",
            "--checker-registry",
        ] {
            let args = valid_args();
            let position = args.iter().position(|arg| *arg == flag).unwrap();
            let reduced = args
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != position && *index != position + 1)
                .map(|(_, value)| *value)
                .collect::<Vec<_>>();
            assert!(
                parse(&reduced).unwrap_err().contains(flag),
                "missing {flag} must be identified"
            );
        }
    }

    #[test]
    fn parser_rejects_duplicate_unknown_and_flag_shaped_values() {
        let mut duplicate = valid_args().to_vec();
        duplicate.extend(["--root", "other"]);
        assert_eq!(parse(&duplicate).unwrap_err(), "duplicate argument: --root");
        assert_eq!(
            parse(&["--unknown", "value"]).unwrap_err(),
            "unknown argument: --unknown"
        );
        assert_eq!(
            parse(&["--root", "--runner-policy"]).unwrap_err(),
            "missing value for --root"
        );
    }
}
