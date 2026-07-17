use std::env;
use std::fs;

use npa_api::parse_independent_checker_raw_result;

fn main() {
    let paths = env::args_os().skip(1).collect::<Vec<_>>();
    assert!(
        !paths.is_empty(),
        "usage: validate_checker_raw RESULT.json ..."
    );
    for path in paths {
        let bytes = fs::read(&path).unwrap();
        let source = std::str::from_utf8(&bytes).unwrap();
        parse_independent_checker_raw_result(source)
            .unwrap_or_else(|error| panic!("{}: {error:?}", path.to_string_lossy()));
    }
}
