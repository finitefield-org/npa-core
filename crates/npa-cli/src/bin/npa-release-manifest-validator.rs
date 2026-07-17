//! Standalone generated-artifact release-manifest validator.

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use npa_cli::release_manifest::validate_release_manifest;

const USAGE: &str = "Usage: npa-release-manifest-validator [--require-v0.2] MANIFEST";

fn main() -> ExitCode {
    let mut require_v0_2 = false;
    let mut manifest = None;
    let mut positional_only = false;
    for argument in std::env::args().skip(1) {
        match argument.as_str() {
            "--" if !positional_only => positional_only = true,
            "--require-v0.2" if !positional_only => require_v0_2 = true,
            "--help" | "-h" if !positional_only => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            value if !positional_only && value.starts_with('-') => {
                eprintln!("error: unsupported option '{value}'\n{USAGE}");
                return ExitCode::from(2);
            }
            value if manifest.is_none() => manifest = Some(PathBuf::from(value)),
            value => {
                eprintln!("error: unexpected argument '{value}'\n{USAGE}");
                return ExitCode::from(2);
            }
        }
    }
    let Some(manifest) = manifest else {
        eprintln!("error: missing release manifest path\n{USAGE}");
        return ExitCode::from(2);
    };

    let source = match fs::read_to_string(&manifest) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("error: {error}");
            return ExitCode::FAILURE;
        }
    };
    match validate_release_manifest(&source, require_v0_2) {
        Ok(validation) => {
            println!("{}", validation.render_json());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}
