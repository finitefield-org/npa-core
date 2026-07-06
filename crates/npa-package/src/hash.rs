//! Package hash type adapters.

use crate::error::{PackageManifestError, PackageManifestResult};
use sha2::{Digest, Sha256};

/// SHA-256 digest type shared with canonical certificate artifacts.
pub type PackageHashBytes = npa_cert::Hash;

/// Parsed SHA-256 package hash digest.
///
/// Manifest text uses `sha256:<64 lowercase hex>` strings, but validated package
/// data stores the parsed digest bytes so later package logic does not trust or
/// compare display strings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageHash(pub PackageHashBytes);

impl PackageHash {
    /// Build a package hash from already parsed SHA-256 digest bytes.
    pub const fn new(digest: PackageHashBytes) -> Self {
        Self(digest)
    }

    /// Return the underlying SHA-256 digest bytes.
    pub const fn as_bytes(&self) -> &PackageHashBytes {
        &self.0
    }

    /// Consume this package hash and return its digest bytes.
    pub const fn into_bytes(self) -> PackageHashBytes {
        self.0
    }
}

impl From<PackageHashBytes> for PackageHash {
    fn from(digest: PackageHashBytes) -> Self {
        Self::new(digest)
    }
}

/// Compute the exact SHA-256 package file hash for an artifact byte sequence.
pub fn package_file_hash(bytes: &[u8]) -> PackageHash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0_u8; 32];
    hash.copy_from_slice(&digest);
    PackageHash::new(hash)
}

/// Parse a manifest hash string as `sha256:<64 lowercase hex>`.
///
/// This parser matches the package manifest wire grammar locally and does not
/// depend on API endpoint helpers, checker execution, files, or the network.
pub fn parse_package_hash(
    value: &str,
    path: impl Into<String>,
) -> PackageManifestResult<PackageHash> {
    let path = path.into();
    let Some(hex) = value.strip_prefix("sha256:") else {
        return Err(PackageManifestError::invalid_hash_format(path, value));
    };
    if hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(PackageManifestError::invalid_hash_format(path, value));
    }

    let mut digest = [0_u8; 32];
    for (index, chunk) in hex.as_bytes().chunks_exact(2).enumerate() {
        digest[index] = hex_nibble(chunk[0]) << 4 | hex_nibble(chunk[1]);
    }
    Ok(PackageHash::new(digest))
}

/// Format a parsed package hash as `sha256:<64 lowercase hex>`.
pub fn format_package_hash(hash: &PackageHash) -> String {
    let mut out = String::with_capacity("sha256:".len() + 64);
    out.push_str("sha256:");
    for byte in hash.as_bytes() {
        out.push(hex_digit(byte >> 4));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => unreachable!("hash parser validates lowercase hex before decoding"),
    }
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex digit out of range"),
    }
}
