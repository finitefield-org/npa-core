use std::env;
use std::path::Path;

use npa_api::parse_independent_checker_raw_result;

#[path = "support/closed_private_tree.rs"]
mod closed_private_tree;

const MAX_CHECKER_RESULT_BYTES: u64 = 16 * 1024 * 1024;

fn main() {
    if let Err(error) = run() {
        eprintln!("validate_checker_raw: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let paths = env::args_os().skip(1).collect::<Vec<_>>();
    if paths.is_empty() {
        return Err("usage: validate_checker_raw RESULT.json ...".to_owned());
    }
    for path in paths {
        let input = Path::new(&path);
        let absolute;
        let path = if input.is_absolute() {
            input
        } else {
            absolute = std::env::current_dir()
                .map_err(|error| format!("current directory is unavailable: {error}"))?
                .join(input);
            absolute.as_path()
        };
        let bytes = closed_private_tree::read_absolute_regular_file(
            path,
            MAX_CHECKER_RESULT_BYTES,
            "independent checker raw result",
        )?;
        let source = std::str::from_utf8(&bytes)
            .map_err(|error| format!("{} is not UTF-8: {error}", path.to_string_lossy()))?;
        parse_independent_checker_raw_result(source)
            .map_err(|error| format!("{}: {error:?}", path.to_string_lossy()))?;
    }
    Ok(())
}
