use std::collections::BTreeSet;

use crate::json::{
    JsonDocument, JsonParseError, JsonParseErrorKind, JsonParseLimits, JsonSpan, JsonValue,
    JsonValueKind,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineApiErrorKind {
    UnknownSession,
    UnknownSnapshot,
    StateFingerprintMismatch,
    SessionRootHashMismatch,
    InvalidVerifiedImport,
    InvalidCheckedCurrentDecl,
    InvalidMachineApiOptions,
    InvalidMachineProofState,
    InvalidSessionRequest,
    InvalidSnapshotRequest,
    InvalidTacticRunRequest,
    InvalidTheoremIndex,
    InvalidTheoremQuery,
    TheoremIndexFingerprintMismatch,
    InvalidPromptPayloadRequest,
    InvalidBatchPolicy,
    InvalidSchedulerLimits,
    InvalidReplayPlan,
    InvalidVerifyRequest,
    ReplayHashMismatch,
    DisallowedAxiom,
    GoalNotOpen,
    InvalidCandidate,
    InvalidBudget,
    UnsupportedTactic,
    MachineTermParseError,
    MachineTermElaborationError,
    UnknownName,
    ImplicitArgumentRequired,
    TypeMismatch,
    ExpectedPiType,
    RewriteRuleInvalid,
    SimpNoProgress,
    InductionTargetNotNat,
    BudgetExceeded,
    TooManyGoals,
    TooLargeTerm,
    VerifyFailed,
}

impl MachineApiErrorKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnknownSession => "unknown_session",
            Self::UnknownSnapshot => "unknown_snapshot",
            Self::StateFingerprintMismatch => "state_fingerprint_mismatch",
            Self::SessionRootHashMismatch => "session_root_hash_mismatch",
            Self::InvalidVerifiedImport => "invalid_verified_import",
            Self::InvalidCheckedCurrentDecl => "invalid_checked_current_decl",
            Self::InvalidMachineApiOptions => "invalid_machine_api_options",
            Self::InvalidMachineProofState => "invalid_machine_proof_state",
            Self::InvalidSessionRequest => "invalid_session_request",
            Self::InvalidSnapshotRequest => "invalid_snapshot_request",
            Self::InvalidTacticRunRequest => "invalid_tactic_run_request",
            Self::InvalidTheoremIndex => "invalid_theorem_index",
            Self::InvalidTheoremQuery => "invalid_theorem_query",
            Self::TheoremIndexFingerprintMismatch => "theorem_index_fingerprint_mismatch",
            Self::InvalidPromptPayloadRequest => "invalid_prompt_payload_request",
            Self::InvalidBatchPolicy => "invalid_batch_policy",
            Self::InvalidSchedulerLimits => "invalid_scheduler_limits",
            Self::InvalidReplayPlan => "invalid_replay_plan",
            Self::InvalidVerifyRequest => "invalid_verify_request",
            Self::ReplayHashMismatch => "replay_hash_mismatch",
            Self::DisallowedAxiom => "disallowed_axiom",
            Self::GoalNotOpen => "goal_not_open",
            Self::InvalidCandidate => "invalid_candidate",
            Self::InvalidBudget => "invalid_budget",
            Self::UnsupportedTactic => "unsupported_tactic",
            Self::MachineTermParseError => "machine_term_parse_error",
            Self::MachineTermElaborationError => "machine_term_elaboration_error",
            Self::UnknownName => "unknown_name",
            Self::ImplicitArgumentRequired => "implicit_argument_required",
            Self::TypeMismatch => "type_mismatch",
            Self::ExpectedPiType => "expected_pi_type",
            Self::RewriteRuleInvalid => "rewrite_rule_invalid",
            Self::SimpNoProgress => "simp_no_progress",
            Self::InductionTargetNotNat => "induction_target_not_nat",
            Self::BudgetExceeded => "budget_exceeded",
            Self::TooManyGoals => "too_many_goals",
            Self::TooLargeTerm => "too_large_term",
            Self::VerifyFailed => "verify_failed",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineApiRequestError {
    pub kind: MachineApiErrorKind,
    pub path: JsonPath,
    pub reason: MachineApiRequestErrorReason,
}

impl MachineApiRequestError {
    pub(crate) fn new(
        kind: MachineApiErrorKind,
        path: JsonPath,
        reason: MachineApiRequestErrorReason,
    ) -> Self {
        Self { kind, path, reason }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineApiRequestErrorReason {
    JsonParse {
        offset: usize,
        kind: JsonParseErrorKind,
    },
    ExpectedObject {
        actual: JsonValueKind,
    },
    DuplicateKey {
        key: String,
    },
    UnknownField {
        field: String,
    },
    MissingField {
        field: &'static str,
    },
    NullField {
        field: &'static str,
    },
    TypeMismatch {
        field: &'static str,
        expected: JsonFieldType,
        actual: JsonValueKind,
    },
    InvalidUnsignedInteger {
        field: &'static str,
        raw: String,
        error: StrictUnsignedIntegerError,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonPath {
    pub elements: Vec<JsonPathElement>,
}

impl JsonPath {
    pub const fn root() -> Self {
        Self {
            elements: Vec::new(),
        }
    }

    pub fn field(&self, field: impl Into<String>) -> Self {
        let mut elements = self.elements.clone();
        elements.push(JsonPathElement::Field(field.into()));
        Self { elements }
    }

    pub fn index(&self, index: usize) -> Self {
        let mut elements = self.elements.clone();
        elements.push(JsonPathElement::Index(index));
        Self { elements }
    }
}

impl Default for JsonPath {
    fn default() -> Self {
        Self::root()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonPathElement {
    Field(String),
    Index(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonFieldType {
    Object,
    Array,
    String,
    Boolean,
    UnsignedInteger { max: u64 },
    DelayedJson,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldSpec {
    pub name: &'static str,
    pub required: bool,
    pub field_type: JsonFieldType,
    pub allow_null: bool,
}

impl FieldSpec {
    pub const fn required(name: &'static str, field_type: JsonFieldType) -> Self {
        Self {
            name,
            required: true,
            field_type,
            allow_null: false,
        }
    }

    pub const fn optional(name: &'static str, field_type: JsonFieldType) -> Self {
        Self {
            name,
            required: false,
            field_type,
            allow_null: false,
        }
    }

    pub const fn allow_null(mut self) -> Self {
        self.allow_null = true;
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectSchema<'a> {
    pub error_kind: MachineApiErrorKind,
    pub fields: &'a [FieldSpec],
}

impl<'a> ObjectSchema<'a> {
    pub const fn new(error_kind: MachineApiErrorKind, fields: &'a [FieldSpec]) -> Self {
        Self { error_kind, fields }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DelayedJsonPayload<'src> {
    pub raw: &'src str,
    pub span: JsonSpan,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ValidatedObject<'value, 'src> {
    members: &'value [crate::json::JsonMember<'src>],
}

impl<'value, 'src> ValidatedObject<'value, 'src> {
    pub fn field(&self, field_name: &str) -> Option<&'value JsonValue<'src>> {
        self.members
            .iter()
            .find(|member| member.key() == field_name)
            .map(|member| member.value())
    }

    pub const fn members(&self) -> &'value [crate::json::JsonMember<'src>] {
        self.members
    }
}

pub fn parse_request_body<'src>(
    source: &'src str,
    error_kind: MachineApiErrorKind,
) -> Result<JsonDocument<'src>, MachineApiRequestError> {
    parse_request_body_with_limits(source, error_kind, JsonParseLimits::default())
}

pub fn parse_request_body_with_limits<'src>(
    source: &'src str,
    error_kind: MachineApiErrorKind,
    limits: JsonParseLimits,
) -> Result<JsonDocument<'src>, MachineApiRequestError> {
    JsonDocument::parse_with_limits(source, limits).map_err(|err| parse_error(error_kind, err))
}

pub fn validate_json_object<'value, 'src>(
    value: &'value JsonValue<'src>,
    schema: ObjectSchema<'_>,
    path: &JsonPath,
) -> Result<ValidatedObject<'value, 'src>, MachineApiRequestError> {
    let Some(members) = value.object_members() else {
        return Err(MachineApiRequestError::new(
            schema.error_kind,
            path.clone(),
            MachineApiRequestErrorReason::ExpectedObject {
                actual: value.kind(),
            },
        ));
    };

    let mut seen = BTreeSet::new();
    for member in members {
        if !seen.insert(member.key().to_owned()) {
            return Err(MachineApiRequestError::new(
                schema.error_kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::DuplicateKey {
                    key: member.key().to_owned(),
                },
            ));
        }
    }

    for member in members {
        if !schema.fields.iter().any(|field| field.name == member.key()) {
            return Err(MachineApiRequestError::new(
                schema.error_kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        }
    }

    for field in schema.fields {
        if field.required && !members.iter().any(|member| member.key() == field.name) {
            return Err(MachineApiRequestError::new(
                schema.error_kind,
                path.field(field.name),
                MachineApiRequestErrorReason::MissingField { field: field.name },
            ));
        }
    }

    for member in members {
        let Some(field) = schema
            .fields
            .iter()
            .find(|field| field.name == member.key())
        else {
            return Err(MachineApiRequestError::new(
                schema.error_kind,
                path.field(member.key()),
                MachineApiRequestErrorReason::UnknownField {
                    field: member.key().to_owned(),
                },
            ));
        };
        validate_field(
            field,
            member.value(),
            schema.error_kind,
            &path.field(member.key()),
        )?;
    }

    Ok(ValidatedObject { members })
}

pub fn delayed_json_payload<'src>(value: &JsonValue<'src>) -> DelayedJsonPayload<'src> {
    DelayedJsonPayload {
        raw: value.raw_slice(),
        span: value.span(),
    }
}

pub fn parse_strict_u64_token(raw: &str, max: u64) -> Result<u64, StrictUnsignedIntegerError> {
    let bytes = raw.as_bytes();
    if bytes.is_empty() {
        return Err(StrictUnsignedIntegerError::InvalidGrammar);
    }

    if bytes == b"0" {
        return Ok(0);
    }

    if !matches!(bytes.first(), Some(b'1'..=b'9')) {
        return Err(StrictUnsignedIntegerError::InvalidGrammar);
    }

    let mut value = 0u64;
    for byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(StrictUnsignedIntegerError::InvalidGrammar);
        }
        value = value
            .checked_mul(10)
            .and_then(|prefix| prefix.checked_add(u64::from(byte - b'0')))
            .ok_or(StrictUnsignedIntegerError::Overflow)?;
    }

    if value > max {
        return Err(StrictUnsignedIntegerError::ExceedsMaximum { max });
    }

    Ok(value)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StrictUnsignedIntegerError {
    InvalidGrammar,
    Overflow,
    ExceedsMaximum { max: u64 },
}

fn validate_field(
    field: &FieldSpec,
    value: &JsonValue<'_>,
    error_kind: MachineApiErrorKind,
    path: &JsonPath,
) -> Result<(), MachineApiRequestError> {
    if value.kind() == JsonValueKind::Null {
        if field.allow_null {
            return Ok(());
        }
        return Err(MachineApiRequestError::new(
            error_kind,
            path.clone(),
            MachineApiRequestErrorReason::NullField { field: field.name },
        ));
    }

    match field.field_type {
        JsonFieldType::Object if value.kind() == JsonValueKind::Object => Ok(()),
        JsonFieldType::Array if value.kind() == JsonValueKind::Array => Ok(()),
        JsonFieldType::String if value.kind() == JsonValueKind::String => Ok(()),
        JsonFieldType::Boolean if value.kind() == JsonValueKind::Bool => Ok(()),
        JsonFieldType::DelayedJson => Ok(()),
        JsonFieldType::UnsignedInteger { max } => {
            let Some(raw) = value.number_raw() else {
                return Err(type_mismatch(field, value, error_kind, path));
            };
            parse_strict_u64_token(raw, max)
                .map(|_| ())
                .map_err(|error| {
                    MachineApiRequestError::new(
                        error_kind,
                        path.clone(),
                        MachineApiRequestErrorReason::InvalidUnsignedInteger {
                            field: field.name,
                            raw: raw.to_owned(),
                            error,
                        },
                    )
                })
        }
        _ => Err(type_mismatch(field, value, error_kind, path)),
    }
}

fn type_mismatch(
    field: &FieldSpec,
    value: &JsonValue<'_>,
    error_kind: MachineApiErrorKind,
    path: &JsonPath,
) -> MachineApiRequestError {
    MachineApiRequestError::new(
        error_kind,
        path.clone(),
        MachineApiRequestErrorReason::TypeMismatch {
            field: field.name,
            expected: field.field_type,
            actual: value.kind(),
        },
    )
}

fn parse_error(error_kind: MachineApiErrorKind, err: JsonParseError) -> MachineApiRequestError {
    MachineApiRequestError::new(
        error_kind,
        JsonPath::root(),
        MachineApiRequestErrorReason::JsonParse {
            offset: err.offset,
            kind: err.kind,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const SIMPLE_FIELDS: &[FieldSpec] = &[
        FieldSpec::required("name", JsonFieldType::String),
        FieldSpec::optional("enabled", JsonFieldType::Boolean),
    ];
    const SIMPLE_SCHEMA: ObjectSchema<'_> =
        ObjectSchema::new(MachineApiErrorKind::InvalidSessionRequest, SIMPLE_FIELDS);

    #[test]
    fn duplicate_keys_are_rejected_by_decoded_key() {
        let doc = parse_request_body(
            r#"{"name":"one","\u006eame":"two"}"#,
            MachineApiErrorKind::InvalidSessionRequest,
        )
        .unwrap();

        let err = validate_json_object(doc.root(), SIMPLE_SCHEMA, &JsonPath::root()).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidSessionRequest);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::DuplicateKey {
                key: "name".to_owned()
            }
        );
    }

    #[test]
    fn object_shape_errors_use_endpoint_error_kind() {
        let cases = [
            (
                r#"{"name":"ok","extra":true}"#,
                MachineApiRequestErrorReason::UnknownField {
                    field: "extra".to_owned(),
                },
            ),
            (
                r#"{}"#,
                MachineApiRequestErrorReason::MissingField { field: "name" },
            ),
            (
                r#"{"name":null}"#,
                MachineApiRequestErrorReason::NullField { field: "name" },
            ),
            (
                r#"{"name":1}"#,
                MachineApiRequestErrorReason::TypeMismatch {
                    field: "name",
                    expected: JsonFieldType::String,
                    actual: JsonValueKind::Number,
                },
            ),
        ];

        for (body, reason) in cases {
            let doc = parse_request_body(body, MachineApiErrorKind::InvalidSessionRequest).unwrap();
            let err =
                validate_json_object(doc.root(), SIMPLE_SCHEMA, &JsonPath::root()).unwrap_err();
            assert_eq!(err.kind, MachineApiErrorKind::InvalidSessionRequest);
            assert_eq!(err.reason, reason);
        }
    }

    #[test]
    fn object_shape_error_priority_is_schema_wide_not_request_order() {
        const FIELDS: &[FieldSpec] = &[
            FieldSpec::required("name", JsonFieldType::String),
            FieldSpec::required("id", JsonFieldType::String),
        ];
        let schema = ObjectSchema::new(MachineApiErrorKind::InvalidSessionRequest, FIELDS);

        let doc = parse_request_body(
            r#"{"name":1,"extra":true}"#,
            MachineApiErrorKind::InvalidSessionRequest,
        )
        .unwrap();
        let err = validate_json_object(doc.root(), schema, &JsonPath::root()).unwrap_err();
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::UnknownField {
                field: "extra".to_owned()
            }
        );

        let doc = parse_request_body(
            r#"{"name":null}"#,
            MachineApiErrorKind::InvalidSessionRequest,
        )
        .unwrap();
        let err = validate_json_object(doc.root(), schema, &JsonPath::root()).unwrap_err();
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::MissingField { field: "id" }
        );
    }

    #[test]
    fn delayed_payload_keeps_raw_slice_until_its_validation_stage() {
        const TOP_FIELDS: &[FieldSpec] = &[
            FieldSpec::required("session_id", JsonFieldType::String),
            FieldSpec::required("candidate", JsonFieldType::DelayedJson),
        ];
        const CANDIDATE_FIELDS: &[FieldSpec] =
            &[FieldSpec::required("kind", JsonFieldType::String)];

        let body = r#"{"session_id":"s","candidate":{"kind":"apply","kind":"exact"}}"#;
        let doc = parse_request_body(body, MachineApiErrorKind::InvalidTacticRunRequest).unwrap();
        let top = validate_json_object(
            doc.root(),
            ObjectSchema::new(MachineApiErrorKind::InvalidTacticRunRequest, TOP_FIELDS),
            &JsonPath::root(),
        )
        .unwrap();

        let candidate = top.field("candidate").unwrap();
        let delayed = delayed_json_payload(candidate);
        assert_eq!(delayed.raw, r#"{"kind":"apply","kind":"exact"}"#);

        let err = validate_json_object(
            candidate,
            ObjectSchema::new(MachineApiErrorKind::InvalidCandidate, CANDIDATE_FIELDS),
            &JsonPath::root().field("candidate"),
        )
        .unwrap_err();
        assert_eq!(err.kind, MachineApiErrorKind::InvalidCandidate);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::DuplicateKey {
                key: "kind".to_owned()
            }
        );
    }

    #[test]
    fn strict_unsigned_integer_tokens_do_not_coerce_json_numbers() {
        assert_eq!(parse_strict_u64_token("0", u64::MAX), Ok(0));
        assert_eq!(parse_strict_u64_token("42", u64::MAX), Ok(42));
        assert_eq!(
            parse_strict_u64_token("01", u64::MAX),
            Err(StrictUnsignedIntegerError::InvalidGrammar)
        );
        assert_eq!(
            parse_strict_u64_token("-1", u64::MAX),
            Err(StrictUnsignedIntegerError::InvalidGrammar)
        );
        assert_eq!(
            parse_strict_u64_token("1.0", u64::MAX),
            Err(StrictUnsignedIntegerError::InvalidGrammar)
        );
        assert_eq!(
            parse_strict_u64_token("1e3", u64::MAX),
            Err(StrictUnsignedIntegerError::InvalidGrammar)
        );
        assert_eq!(
            parse_strict_u64_token("+1", u64::MAX),
            Err(StrictUnsignedIntegerError::InvalidGrammar)
        );
        assert_eq!(
            parse_strict_u64_token("11", 10),
            Err(StrictUnsignedIntegerError::ExceedsMaximum { max: 10 })
        );
    }

    #[test]
    fn unsigned_integer_field_rejects_float_and_negative_number_tokens() {
        const FIELDS: &[FieldSpec] = &[FieldSpec::required(
            "limit",
            JsonFieldType::UnsignedInteger { max: 100 },
        )];
        let schema = ObjectSchema::new(MachineApiErrorKind::InvalidMachineApiOptions, FIELDS);

        for body in [r#"{"limit":1.0}"#, r#"{"limit":1e1}"#, r#"{"limit":-1}"#] {
            let doc =
                parse_request_body(body, MachineApiErrorKind::InvalidMachineApiOptions).unwrap();
            let err = validate_json_object(doc.root(), schema, &JsonPath::root()).unwrap_err();
            assert_eq!(err.kind, MachineApiErrorKind::InvalidMachineApiOptions);
            assert!(matches!(
                err.reason,
                MachineApiRequestErrorReason::InvalidUnsignedInteger { .. }
            ));
        }
    }

    #[test]
    fn parse_errors_are_endpoint_specific() {
        let err = parse_request_body("{", MachineApiErrorKind::InvalidReplayPlan).unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidReplayPlan);
        assert!(matches!(
            err.reason,
            MachineApiRequestErrorReason::JsonParse { .. }
        ));
    }

    #[test]
    fn parser_depth_limit_returns_structured_parse_error() {
        let err = parse_request_body_with_limits(
            r#"{"outer":{"inner":0}}"#,
            MachineApiErrorKind::InvalidReplayPlan,
            JsonParseLimits { max_depth: 1 },
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidReplayPlan);
        assert_eq!(
            err.reason,
            MachineApiRequestErrorReason::JsonParse {
                offset: 18,
                kind: JsonParseErrorKind::NestingDepthExceeded { max_depth: 1 }
            }
        );
    }

    #[test]
    fn parser_clamps_excessive_public_depth_limit_to_internal_cap() {
        let mut body = "[".repeat(JsonParseLimits::MAX_DEPTH + 1);
        body.push('0');
        body.push_str(&"]".repeat(JsonParseLimits::MAX_DEPTH + 1));

        let err = parse_request_body_with_limits(
            &body,
            MachineApiErrorKind::InvalidReplayPlan,
            JsonParseLimits {
                max_depth: usize::MAX,
            },
        )
        .unwrap_err();

        assert_eq!(err.kind, MachineApiErrorKind::InvalidReplayPlan);
        assert!(matches!(
            err.reason,
            MachineApiRequestErrorReason::JsonParse {
                kind: JsonParseErrorKind::NestingDepthExceeded {
                    max_depth: JsonParseLimits::MAX_DEPTH
                },
                ..
            }
        ));
    }
}
