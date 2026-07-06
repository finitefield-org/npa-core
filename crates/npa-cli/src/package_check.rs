//! Implementation of `npa package check`.

use crate::args::PackageCommonOptions;
use crate::diagnostic::CommandResult;
use crate::package::load_package_root;

/// Run manifest-only package metadata validation.
///
/// This command intentionally reads only `npa-package.toml`. It delegates
/// schema, profile, path, hash, import graph, and axiom-policy validation to
/// `npa-package`; artifact freshness checks belong to later CLR-04 commands.
pub fn run_package_check(options: PackageCommonOptions) -> CommandResult {
    match load_package_root(&options.root, "package check") {
        Ok(loaded) => CommandResult::passed("package check", loaded.root_display),
        Err(result) => result,
    }
}
