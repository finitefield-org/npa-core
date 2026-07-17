//! Canonical recoverable transaction journal for mathlib promotion writes.
//!
//! The journal is untrusted workflow metadata. It binds old and new file
//! identities so the CLI can recover deterministically after interruption; it
//! is never proof evidence.

use std::collections::BTreeSet;

use crate::{
    artifacts::{
        expect_object, hash_json, json_array, json_bool, json_object_in_order, json_string,
        json_u64, parse_artifact_json, reject_unknown_fields, required_array, required_bool,
        required_hash, required_path, required_string, required_u64, required_value,
        validate_artifact_path,
    },
    error::{PackageArtifactError, PackageArtifactResult},
    hash::{package_file_hash, PackageHash},
    json::JsonValue,
    path::PackagePath,
    schema::MATHLIB_PROMOTION_TRANSACTION_SCHEMA,
};

const JOURNAL_FIELDS: &[&str] = &[
    "schema",
    "promotion_id",
    "phase",
    "target_canonical_path_hash",
    "transaction_state",
    "rows",
    "journal_hash",
    "proof_evidence",
];
const ROW_FIELDS: &[&str] = &[
    "replacement_order",
    "logical_path",
    "logical_path_hash",
    "old",
    "new_file_hash",
    "replacement_state",
];
const OLD_ABSENT_FIELDS: &[&str] = &["kind"];
const OLD_PRESENT_FIELDS: &[&str] = &["kind", "file_hash"];
const TRANSACTION_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-TRANSACTION-v1\0";
const PATH_DOMAIN: &[u8] = b"NPA-MATHLIB-PROMOTION-PATH-v1\0";

/// Temporary-copy or tracked-target transaction phase.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PromotionTransactionPhase {
    /// Disposable target-copy materialization.
    Temporary,
    /// Live tracked-target materialization.
    Tracked,
}

impl PromotionTransactionPhase {
    /// Stable wire spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Temporary => "temporary",
            Self::Tracked => "tracked",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "temporary" => Ok(Self::Temporary),
            "tracked" => Ok(Self::Tracked),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "phase",
                "temporary or tracked",
                value,
            )),
        }
    }
}

/// Overall transaction state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PromotionTransactionState {
    /// Replacements or post-write validation are still in progress.
    Applying,
    /// Every replacement was post-write validated and fsynced.
    Validated,
}

impl PromotionTransactionState {
    /// Stable wire spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Applying => "applying",
            Self::Validated => "validated",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "applying" => Ok(Self::Applying),
            "validated" => Ok(Self::Validated),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "transaction_state",
                "applying or validated",
                value,
            )),
        }
    }
}

/// Per-file replacement state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PromotionReplacementState {
    /// Target replacement has not been journaled as complete.
    Pending,
    /// Target replacement has been journaled as complete.
    Replaced,
}

impl PromotionReplacementState {
    /// Stable wire spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Replaced => "replaced",
        }
    }

    fn parse(value: &str, path: &str) -> PackageArtifactResult<Self> {
        match value {
            "pending" => Ok(Self::Pending),
            "replaced" => Ok(Self::Replaced),
            _ => Err(PackageArtifactError::invalid_enum_value(
                path,
                "replacement_state",
                "pending or replaced",
                value,
            )),
        }
    }
}

/// Exact old state for one path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PromotionOldFile {
    /// The target path did not exist before the transaction.
    Absent,
    /// The target path existed with the exact file hash.
    Present(PackageHash),
}

/// One ordered target replacement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTransactionRow {
    /// Zero-based deterministic replacement order.
    pub replacement_order: u64,
    /// Target-package-relative logical path.
    pub logical_path: PackagePath,
    /// Domain-separated logical path hash used for staged filenames.
    pub logical_path_hash: PackageHash,
    /// Exact old state.
    pub old: PromotionOldFile,
    /// Exact new bytes hash.
    pub new_file_hash: PackageHash,
    /// Current journaled replacement state.
    pub replacement_state: PromotionReplacementState,
}

/// Canonical recoverable promotion transaction journal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PromotionTransactionJournal {
    /// Schema identifier.
    pub schema: String,
    /// Stable promotion route identifier.
    pub promotion_id: PackageHash,
    /// Materialization phase.
    pub phase: PromotionTransactionPhase,
    /// Hash of the canonical absolute target path.
    pub target_canonical_path_hash: PackageHash,
    /// Overall transaction state.
    pub transaction_state: PromotionTransactionState,
    /// Ordered replacement rows.
    pub rows: Vec<PromotionTransactionRow>,
    /// Domain-separated self-hash.
    pub journal_hash: PackageHash,
    /// Always false.
    pub proof_evidence: bool,
}

impl PromotionTransactionJournal {
    /// Serialize strict canonical JSON with one final newline.
    pub fn canonical_json(&self) -> PackageArtifactResult<String> {
        validate_promotion_transaction(self)?;
        Ok(format!("{}\n", journal_json(self)))
    }

    /// Recompute and store the journal self-hash after a state transition.
    pub fn refresh_hash(&mut self) -> PackageArtifactResult<()> {
        self.journal_hash = promotion_transaction_hash(self)?;
        Ok(())
    }
}

/// Compute the staged filename hash for a normalized logical path.
pub fn promotion_transaction_path_hash(path: &PackagePath) -> PackageArtifactResult<PackageHash> {
    validate_artifact_path(path, "logical_path")?;
    let mut bytes = Vec::with_capacity(PATH_DOMAIN.len() + path.as_str().len());
    bytes.extend_from_slice(PATH_DOMAIN);
    bytes.extend_from_slice(path.as_str().as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Compute the domain-separated journal self-hash.
pub fn promotion_transaction_hash(
    journal: &PromotionTransactionJournal,
) -> PackageArtifactResult<PackageHash> {
    let mut copy = journal.clone();
    copy.journal_hash = zero_hash();
    validate_promotion_transaction_shape(&copy, false)?;
    let json = journal_json(&copy);
    let mut bytes = Vec::with_capacity(TRANSACTION_DOMAIN.len() + json.len());
    bytes.extend_from_slice(TRANSACTION_DOMAIN);
    bytes.extend_from_slice(json.as_bytes());
    Ok(package_file_hash(&bytes))
}

/// Parse and validate canonical transaction journal JSON.
pub fn parse_promotion_transaction_json(
    source: &str,
) -> PackageArtifactResult<PromotionTransactionJournal> {
    let value = parse_artifact_json(source)?;
    let members = expect_object(&value, "$")?;
    reject_unknown_fields("$", members, JOURNAL_FIELDS)?;
    let journal = PromotionTransactionJournal {
        schema: required_string(members, "$", "schema")?,
        promotion_id: required_hash(members, "$", "promotion_id")?,
        phase: PromotionTransactionPhase::parse(&required_string(members, "$", "phase")?, "phase")?,
        target_canonical_path_hash: required_hash(members, "$", "target_canonical_path_hash")?,
        transaction_state: PromotionTransactionState::parse(
            &required_string(members, "$", "transaction_state")?,
            "transaction_state",
        )?,
        rows: required_array(members, "$", "rows")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_row(value, index))
            .collect::<PackageArtifactResult<Vec<_>>>()?,
        journal_hash: required_hash(members, "$", "journal_hash")?,
        proof_evidence: required_bool(members, "$", "proof_evidence")?,
    };
    validate_promotion_transaction(&journal)?;
    if source != journal.canonical_json()? {
        return Err(PackageArtifactError::non_canonical(
            "$",
            "promotion transaction JSON bytes",
        ));
    }
    Ok(journal)
}

/// Validate a transaction journal and its self-hash.
pub fn validate_promotion_transaction(
    journal: &PromotionTransactionJournal,
) -> PackageArtifactResult<()> {
    validate_promotion_transaction_shape(journal, true)
}

fn validate_promotion_transaction_shape(
    journal: &PromotionTransactionJournal,
    check_hash: bool,
) -> PackageArtifactResult<()> {
    if journal.schema != MATHLIB_PROMOTION_TRANSACTION_SCHEMA {
        return Err(PackageArtifactError::unsupported_schema(
            "schema",
            "schema",
            MATHLIB_PROMOTION_TRANSACTION_SCHEMA,
            &journal.schema,
        ));
    }
    if journal.proof_evidence || journal.rows.is_empty() {
        return Err(PackageArtifactError::invalid_enum_value(
            "$",
            "transaction",
            "nonempty rows and false proof_evidence",
            "mismatch",
        ));
    }
    let mut paths = BTreeSet::new();
    let mut hashes = BTreeSet::new();
    for (index, row) in journal.rows.iter().enumerate() {
        if row.replacement_order != index as u64 {
            return Err(PackageArtifactError::non_canonical(
                format!("rows[{index}].replacement_order"),
                "contiguous replacement order",
            ));
        }
        validate_artifact_path(&row.logical_path, format!("rows[{index}].logical_path"))?;
        let expected = promotion_transaction_path_hash(&row.logical_path)?;
        if row.logical_path_hash != expected {
            return Err(PackageArtifactError::invalid_enum_value(
                format!("rows[{index}].logical_path_hash"),
                "logical_path_hash",
                "domain-separated logical path hash",
                "mismatch",
            ));
        }
        if !paths.insert(row.logical_path.clone()) || !hashes.insert(row.logical_path_hash) {
            return Err(PackageArtifactError::non_canonical(
                format!("rows[{index}]"),
                "unique transaction paths",
            ));
        }
    }
    if journal.transaction_state == PromotionTransactionState::Validated
        && journal
            .rows
            .iter()
            .any(|row| row.replacement_state != PromotionReplacementState::Replaced)
    {
        return Err(PackageArtifactError::invalid_enum_value(
            "transaction_state",
            "transaction_state",
            "validated only after every row is replaced",
            "validated",
        ));
    }
    if check_hash && journal.journal_hash != promotion_transaction_hash(journal)? {
        return Err(PackageArtifactError::invalid_enum_value(
            "journal_hash",
            "journal_hash",
            "matching promotion transaction self-hash",
            "mismatch",
        ));
    }
    Ok(())
}

fn parse_row(value: &JsonValue, index: usize) -> PackageArtifactResult<PromotionTransactionRow> {
    let path = format!("rows[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ROW_FIELDS)?;
    Ok(PromotionTransactionRow {
        replacement_order: required_u64(members, &path, "replacement_order")?,
        logical_path: required_path(members, &path, "logical_path")?,
        logical_path_hash: required_hash(members, &path, "logical_path_hash")?,
        old: parse_old(
            required_value(members, &path, "old")?,
            &format!("{path}.old"),
        )?,
        new_file_hash: required_hash(members, &path, "new_file_hash")?,
        replacement_state: PromotionReplacementState::parse(
            &required_string(members, &path, "replacement_state")?,
            &format!("{path}.replacement_state"),
        )?,
    })
}

fn parse_old(value: &JsonValue, path: &str) -> PackageArtifactResult<PromotionOldFile> {
    let members = expect_object(value, path)?;
    let kind = required_string(members, path, "kind")?;
    match kind.as_str() {
        "absent" => {
            reject_unknown_fields(path, members, OLD_ABSENT_FIELDS)?;
            Ok(PromotionOldFile::Absent)
        }
        "present" => {
            reject_unknown_fields(path, members, OLD_PRESENT_FIELDS)?;
            Ok(PromotionOldFile::Present(required_hash(
                members,
                path,
                "file_hash",
            )?))
        }
        _ => Err(PackageArtifactError::invalid_enum_value(
            path,
            "kind",
            "absent or present",
            kind,
        )),
    }
}

fn journal_json(journal: &PromotionTransactionJournal) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&journal.schema)),
        ("promotion_id", hash_json(journal.promotion_id)),
        ("phase", json_string(journal.phase.as_str())),
        (
            "target_canonical_path_hash",
            hash_json(journal.target_canonical_path_hash),
        ),
        (
            "transaction_state",
            json_string(journal.transaction_state.as_str()),
        ),
        (
            "rows",
            json_array(journal.rows.iter().map(row_json).collect()),
        ),
        ("journal_hash", hash_json(journal.journal_hash)),
        ("proof_evidence", json_bool(journal.proof_evidence)),
    ])
}

fn row_json(row: &PromotionTransactionRow) -> String {
    json_object_in_order(vec![
        ("replacement_order", json_u64(row.replacement_order)),
        ("logical_path", json_string(row.logical_path.as_str())),
        ("logical_path_hash", hash_json(row.logical_path_hash)),
        ("old", old_json(&row.old)),
        ("new_file_hash", hash_json(row.new_file_hash)),
        (
            "replacement_state",
            json_string(row.replacement_state.as_str()),
        ),
    ])
}

fn old_json(old: &PromotionOldFile) -> String {
    match old {
        PromotionOldFile::Absent => json_object_in_order(vec![("kind", json_string("absent"))]),
        PromotionOldFile::Present(hash) => json_object_in_order(vec![
            ("kind", json_string("present")),
            ("file_hash", hash_json(*hash)),
        ]),
    }
}

const fn zero_hash() -> PackageHash {
    PackageHash::new([0; 32])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(byte: u8) -> PackageHash {
        PackageHash::new([byte; 32])
    }

    #[test]
    fn transaction_round_trip_and_state_invariant() {
        let path = PackagePath::new("Mathlib/Example/source.npa");
        let mut journal = PromotionTransactionJournal {
            schema: MATHLIB_PROMOTION_TRANSACTION_SCHEMA.to_owned(),
            promotion_id: hash(1),
            phase: PromotionTransactionPhase::Tracked,
            target_canonical_path_hash: hash(2),
            transaction_state: PromotionTransactionState::Applying,
            rows: vec![PromotionTransactionRow {
                replacement_order: 0,
                logical_path_hash: promotion_transaction_path_hash(&path).unwrap(),
                logical_path: path,
                old: PromotionOldFile::Absent,
                new_file_hash: hash(3),
                replacement_state: PromotionReplacementState::Pending,
            }],
            journal_hash: zero_hash(),
            proof_evidence: false,
        };
        journal.refresh_hash().unwrap();
        assert_eq!(
            crate::format_package_hash(&journal.journal_hash),
            "sha256:60bfd8983fd2d46eef253d1b7973ef746f713e4eb034ddacc4a26c16fa02cfb5"
        );
        let json = journal.canonical_json().unwrap();
        assert_eq!(parse_promotion_transaction_json(&json).unwrap(), journal);

        journal.transaction_state = PromotionTransactionState::Validated;
        assert!(journal.refresh_hash().is_err());
    }
}
