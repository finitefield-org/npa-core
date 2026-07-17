//! Package-confined atomic writer for generated artifacts.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use npa_package::PackagePath;

use crate::fs::join_package_path;

/// Atomically write one artifact beneath the package's real `generated` directory.
///
/// The helper rejects symlinked or non-directory parents, symlinked or
/// non-regular targets, and pre-existing sibling temporary paths. Identical
/// existing bytes are left untouched.
pub fn write_package_generated_artifact_atomic(
    root: &Path,
    package_path: &PackagePath,
    bytes: &[u8],
) -> io::Result<()> {
    let target = join_package_path(root, package_path, "generated_artifact.path")
        .map_err(|_| invalid_generated_artifact())?;
    let parent = target.parent().ok_or_else(invalid_generated_artifact)?;
    ensure_real_generated_parent(root, parent)?;
    ensure_regular_target_or_missing(&target)?;

    match read_regular_file_no_follow(&target) {
        Ok(existing) if existing == bytes => return Ok(()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    let temporary = sibling_temporary_path(&target)?;
    let mut temporary_created = false;
    let result = (|| {
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temporary)?;
        temporary_created = true;
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);

        ensure_real_generated_parent(root, parent)?;
        ensure_regular_target_or_missing(&target)?;
        fs::rename(&temporary, &target)?;
        File::open(parent)?.sync_all()?;
        Ok(())
    })();
    if result.is_err() && temporary_created {
        let _ = fs::remove_file(&temporary);
    }
    result
}

pub(crate) fn read_regular_file_no_follow(path: &Path) -> io::Result<Vec<u8>> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_NOFOLLOW);
    let mut file = options.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(invalid_generated_artifact());
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn ensure_real_generated_parent(root: &Path, expected_parent: &Path) -> io::Result<()> {
    let generated = root.join("generated");
    if generated != expected_parent {
        return Err(invalid_generated_artifact());
    }
    match fs::symlink_metadata(&generated) {
        Ok(metadata) => ensure_real_directory(&metadata),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            fs::create_dir(&generated)?;
            ensure_real_directory(&fs::symlink_metadata(&generated)?)
        }
        Err(error) => Err(error),
    }
}

fn ensure_real_directory(metadata: &fs::Metadata) -> io::Result<()> {
    let file_type = metadata.file_type();
    if file_type.is_dir() && !file_type.is_symlink() {
        Ok(())
    } else {
        Err(invalid_generated_artifact())
    }
}

fn ensure_regular_target_or_missing(target: &Path) -> io::Result<()> {
    match fs::symlink_metadata(target) {
        Ok(metadata) => {
            let file_type = metadata.file_type();
            if file_type.is_file() && !file_type.is_symlink() {
                Ok(())
            } else {
                Err(invalid_generated_artifact())
            }
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn sibling_temporary_path(target: &Path) -> io::Result<PathBuf> {
    let file_name = target
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(invalid_generated_artifact)?;
    Ok(target.with_file_name(format!(".{file_name}.tmp.{}", std::process::id())))
}

fn invalid_generated_artifact() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "generated artifact path is not a real package-confined regular file",
    )
}
