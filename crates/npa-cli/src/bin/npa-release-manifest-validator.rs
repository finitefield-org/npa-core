//! Standalone generated-artifact release-manifest validator.

use std::path::PathBuf;
use std::process::ExitCode;

use npa_cli::fs::read_bounded_regular_file;
use npa_cli::release_manifest::{validate_current_release_manifest, validate_release_manifest};

const USAGE: &str =
    "Usage: npa-release-manifest-validator [--require-v0.2 | --require-v0.3] MANIFEST";
const MAX_RELEASE_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;

fn main() -> ExitCode {
    let mut require_v0_2 = false;
    let mut require_v0_3 = false;
    let mut manifest = None;
    let mut positional_only = false;
    for argument in std::env::args().skip(1) {
        match argument.as_str() {
            "--" if !positional_only => positional_only = true,
            "--require-v0.2" if !positional_only => require_v0_2 = true,
            "--require-v0.3" if !positional_only => require_v0_3 = true,
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
    if require_v0_2 && require_v0_3 {
        eprintln!("error: --require-v0.2 and --require-v0.3 are mutually exclusive\n{USAGE}");
        return ExitCode::from(2);
    }

    let source =
        match read_bounded_regular_file(&manifest, MAX_RELEASE_MANIFEST_BYTES).and_then(|bytes| {
            String::from_utf8(bytes).map_err(|error| {
                std::io::Error::new(std::io::ErrorKind::InvalidData, error.to_string())
            })
        }) {
            Ok(source) => source,
            Err(error) => {
                eprintln!("error: {error}");
                return ExitCode::FAILURE;
            }
        };
    let validation = if require_v0_3 {
        validate_current_release_manifest(&source)
    } else {
        validate_release_manifest(&source, require_v0_2)
    };
    match validation {
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
