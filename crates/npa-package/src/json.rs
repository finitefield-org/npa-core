#![allow(missing_docs)]

use std::fmt;

const MAX_JSON_NESTING_DEPTH: usize = 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct JsonResourceLimits {
    pub(crate) nesting_depth: usize,
    pub(crate) string_bytes: usize,
    pub(crate) number_bytes: usize,
    pub(crate) array_elements: usize,
    pub(crate) object_members: usize,
    pub(crate) array_member_elements: &'static [(&'static str, usize)],
}

const DEFAULT_JSON_RESOURCE_LIMITS: JsonResourceLimits = JsonResourceLimits {
    nesting_depth: MAX_JSON_NESTING_DEPTH,
    string_bytes: usize::MAX,
    number_bytes: usize::MAX,
    array_elements: usize::MAX,
    object_members: usize::MAX,
    array_member_elements: &[],
};

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum JsonValue {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<JsonValue>),
    Object(Vec<JsonMember>),
}

impl JsonValue {
    pub(crate) fn kind(&self) -> JsonValueKind {
        match self {
            Self::Null => JsonValueKind::Null,
            Self::Bool(_) => JsonValueKind::Bool,
            Self::Number(_) => JsonValueKind::Number,
            Self::String(_) => JsonValueKind::String,
            Self::Array(_) => JsonValueKind::Array,
            Self::Object(_) => JsonValueKind::Object,
        }
    }

    pub(crate) fn string_value(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    pub(crate) fn bool_value(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    pub(crate) fn number_value(&self) -> Option<&str> {
        match self {
            Self::Number(value) => Some(value),
            _ => None,
        }
    }

    pub(crate) fn array_elements(&self) -> Option<&[JsonValue]> {
        match self {
            Self::Array(values) => Some(values),
            _ => None,
        }
    }

    pub(crate) fn object_members(&self) -> Option<&[JsonMember]> {
        match self {
            Self::Object(members) => Some(members),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct JsonMember {
    key: String,
    value: JsonValue,
}

impl JsonMember {
    pub(crate) fn key(&self) -> &str {
        &self.key
    }

    pub(crate) fn value(&self) -> &JsonValue {
        &self.value
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum JsonValueKind {
    Null,
    Bool,
    Number,
    String,
    Array,
    Object,
}

impl JsonValueKind {
    pub(crate) const fn as_str(self) -> &'static str {
        match self {
            Self::Null => "null",
            Self::Bool => "bool",
            Self::Number => "number",
            Self::String => "string",
            Self::Array => "array",
            Self::Object => "object",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JsonParseError {
    pub(crate) offset: usize,
    pub(crate) kind: JsonParseErrorKind,
}

impl fmt::Display for JsonParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} at byte {}", self.kind, self.offset)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum JsonParseErrorKind {
    ExpectedValue,
    UnexpectedEof,
    UnexpectedByte { expected: &'static str, actual: u8 },
    TrailingCharacters,
    InvalidNumber,
    InvalidEscape,
    InvalidUnicodeEscape,
    ControlCharacterInString,
    NestingDepthExceeded { max_depth: usize },
    StringBytesExceeded { max_bytes: usize },
    NumberBytesExceeded { max_bytes: usize },
    ArrayElementsExceeded { max_elements: usize },
    ObjectMembersExceeded { max_members: usize },
}

pub(crate) fn parse_json(source: &str) -> Result<JsonValue, JsonParseError> {
    parse_json_with_limits(source, DEFAULT_JSON_RESOURCE_LIMITS)
}

pub(crate) fn parse_json_with_limits(
    source: &str,
    limits: JsonResourceLimits,
) -> Result<JsonValue, JsonParseError> {
    let mut parser = Parser::new(source, limits);
    let value = parser.parse_value(0)?;
    parser.skip_ws();
    if parser.is_done() {
        Ok(value)
    } else {
        Err(parser.error(JsonParseErrorKind::TrailingCharacters))
    }
}

struct Parser<'src> {
    source: &'src str,
    bytes: &'src [u8],
    offset: usize,
    limits: JsonResourceLimits,
}

impl<'src> Parser<'src> {
    fn new(source: &'src str, limits: JsonResourceLimits) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            offset: 0,
            limits,
        }
    }

    fn parse_value(&mut self, depth: usize) -> Result<JsonValue, JsonParseError> {
        self.parse_value_with_array_limit(depth, None)
    }

    fn parse_value_with_array_limit(
        &mut self,
        depth: usize,
        array_elements: Option<usize>,
    ) -> Result<JsonValue, JsonParseError> {
        if depth > self.limits.nesting_depth {
            return Err(self.error(JsonParseErrorKind::NestingDepthExceeded {
                max_depth: self.limits.nesting_depth,
            }));
        }
        self.skip_ws();
        let Some(byte) = self.peek() else {
            return Err(self.error(JsonParseErrorKind::ExpectedValue));
        };

        match byte {
            b'n' => self.parse_literal(b"null", JsonValue::Null),
            b't' => self.parse_literal(b"true", JsonValue::Bool(true)),
            b'f' => self.parse_literal(b"false", JsonValue::Bool(false)),
            b'"' => self.parse_string().map(JsonValue::String),
            b'[' => self.parse_array(
                depth,
                array_elements
                    .unwrap_or(self.limits.array_elements)
                    .min(self.limits.array_elements),
            ),
            b'{' => self.parse_object(depth),
            b'-' | b'0'..=b'9' => self.parse_number().map(JsonValue::Number),
            _ => Err(self.error(JsonParseErrorKind::ExpectedValue)),
        }
    }

    fn parse_literal(
        &mut self,
        literal: &'static [u8],
        value: JsonValue,
    ) -> Result<JsonValue, JsonParseError> {
        for expected in literal {
            self.consume_expected_byte(*expected, "literal")?;
        }
        Ok(value)
    }

    fn parse_string(&mut self) -> Result<String, JsonParseError> {
        self.consume_expected_byte(b'"', "string")?;
        let mut out = String::new();

        loop {
            let Some(byte) = self.peek() else {
                return Err(self.error(JsonParseErrorKind::UnexpectedEof));
            };
            match byte {
                b'"' => {
                    self.offset += 1;
                    return Ok(out);
                }
                b'\\' => {
                    self.offset += 1;
                    self.parse_string_escape(&mut out)?;
                }
                0x00..=0x1f => {
                    return Err(self.error(JsonParseErrorKind::ControlCharacterInString));
                }
                _ => {
                    let ch = self.source[self.offset..]
                        .chars()
                        .next()
                        .ok_or_else(|| self.error(JsonParseErrorKind::UnexpectedEof))?;
                    self.offset += ch.len_utf8();
                    self.push_string_char(&mut out, ch)?;
                }
            }
        }
    }

    fn parse_string_escape(&mut self, out: &mut String) -> Result<(), JsonParseError> {
        let Some(byte) = self.take_byte() else {
            return Err(self.error(JsonParseErrorKind::UnexpectedEof));
        };
        match byte {
            b'"' => self.push_string_char(out, '"')?,
            b'\\' => self.push_string_char(out, '\\')?,
            b'/' => self.push_string_char(out, '/')?,
            b'b' => self.push_string_char(out, '\u{0008}')?,
            b'f' => self.push_string_char(out, '\u{000c}')?,
            b'n' => self.push_string_char(out, '\n')?,
            b'r' => self.push_string_char(out, '\r')?,
            b't' => self.push_string_char(out, '\t')?,
            b'u' => {
                let ch = self.parse_unicode_escape()?;
                self.push_string_char(out, ch)?;
            }
            _ => return Err(self.error(JsonParseErrorKind::InvalidEscape)),
        }
        Ok(())
    }

    fn parse_unicode_escape(&mut self) -> Result<char, JsonParseError> {
        let unit = self.parse_hex_u16()?;
        let scalar = if (0xd800..=0xdbff).contains(&unit) {
            self.consume_expected_byte(b'\\', "unicode low surrogate")?;
            self.consume_expected_byte(b'u', "unicode low surrogate")?;
            let low = self.parse_hex_u16()?;
            if !(0xdc00..=0xdfff).contains(&low) {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            }
            let high_ten = u32::from(unit - 0xd800);
            let low_ten = u32::from(low - 0xdc00);
            0x10000 + ((high_ten << 10) | low_ten)
        } else {
            u32::from(unit)
        };

        let Some(ch) = char::from_u32(scalar) else {
            return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
        };
        Ok(ch)
    }

    fn push_string_char(&self, out: &mut String, ch: char) -> Result<(), JsonParseError> {
        if out.len().saturating_add(ch.len_utf8()) > self.limits.string_bytes {
            return Err(self.error(JsonParseErrorKind::StringBytesExceeded {
                max_bytes: self.limits.string_bytes,
            }));
        }
        out.push(ch);
        Ok(())
    }

    fn parse_hex_u16(&mut self) -> Result<u16, JsonParseError> {
        let mut value = 0_u16;
        for _ in 0..4 {
            let Some(byte) = self.take_byte() else {
                return Err(self.error(JsonParseErrorKind::UnexpectedEof));
            };
            let Some(nibble) = hex_nibble(byte) else {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            };
            value = (value << 4) | u16::from(nibble);
        }
        Ok(value)
    }

    fn parse_array(
        &mut self,
        depth: usize,
        max_elements: usize,
    ) -> Result<JsonValue, JsonParseError> {
        self.consume_expected_byte(b'[', "array")?;
        let mut values = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b']') {
            self.offset += 1;
            return Ok(JsonValue::Array(values));
        }

        loop {
            if values.len() == max_elements {
                return Err(self.error(JsonParseErrorKind::ArrayElementsExceeded { max_elements }));
            }
            values.push(self.parse_value(depth + 1)?);
            self.skip_ws();
            match self.take_byte() {
                Some(b',') => {}
                Some(b']') => return Ok(JsonValue::Array(values)),
                Some(actual) => {
                    return Err(self.error_at(
                        self.offset.saturating_sub(1),
                        JsonParseErrorKind::UnexpectedByte {
                            expected: "',' or ']'",
                            actual,
                        },
                    ));
                }
                None => return Err(self.error(JsonParseErrorKind::UnexpectedEof)),
            }
        }
    }

    fn parse_object(&mut self, depth: usize) -> Result<JsonValue, JsonParseError> {
        self.consume_expected_byte(b'{', "object")?;
        let mut members = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b'}') {
            self.offset += 1;
            return Ok(JsonValue::Object(members));
        }

        loop {
            self.skip_ws();
            if members.len() == self.limits.object_members {
                return Err(self.error(JsonParseErrorKind::ObjectMembersExceeded {
                    max_members: self.limits.object_members,
                }));
            }
            if self.peek() != Some(b'"') {
                return Err(self.error(JsonParseErrorKind::UnexpectedByte {
                    expected: "object key string",
                    actual: self.peek().unwrap_or_default(),
                }));
            }
            let key = self.parse_string()?;
            self.skip_ws();
            self.consume_expected_byte(b':', "object colon")?;
            let array_elements = self
                .limits
                .array_member_elements
                .iter()
                .find_map(|(field, maximum)| (key == *field).then_some(*maximum));
            let value = self.parse_value_with_array_limit(depth + 1, array_elements)?;
            members.push(JsonMember { key, value });
            self.skip_ws();
            match self.take_byte() {
                Some(b',') => {}
                Some(b'}') => return Ok(JsonValue::Object(members)),
                Some(actual) => {
                    return Err(self.error_at(
                        self.offset.saturating_sub(1),
                        JsonParseErrorKind::UnexpectedByte {
                            expected: "',' or '}'",
                            actual,
                        },
                    ));
                }
                None => return Err(self.error(JsonParseErrorKind::UnexpectedEof)),
            }
        }
    }

    fn parse_number(&mut self) -> Result<String, JsonParseError> {
        let start = self.offset;
        if self.peek() == Some(b'-') {
            self.offset += 1;
        }

        match self.peek() {
            Some(b'0') => self.offset += 1,
            Some(b'1'..=b'9') => {
                self.offset += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.offset += 1;
                }
            }
            _ => return Err(self.error(JsonParseErrorKind::InvalidNumber)),
        }

        if self.peek() == Some(b'.') {
            self.offset += 1;
            let digit_start = self.offset;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
            if self.offset == digit_start {
                return Err(self.error(JsonParseErrorKind::InvalidNumber));
            }
        }

        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.offset += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.offset += 1;
            }
            let digit_start = self.offset;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
            if self.offset == digit_start {
                return Err(self.error(JsonParseErrorKind::InvalidNumber));
            }
        }

        let number_bytes = self.offset - start;
        if number_bytes > self.limits.number_bytes {
            return Err(self.error(JsonParseErrorKind::NumberBytesExceeded {
                max_bytes: self.limits.number_bytes,
            }));
        }
        Ok(self.source[start..self.offset].to_owned())
    }

    fn consume_expected_byte(
        &mut self,
        expected: u8,
        expected_name: &'static str,
    ) -> Result<(), JsonParseError> {
        match self.take_byte() {
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(self.error_at(
                self.offset.saturating_sub(1),
                JsonParseErrorKind::UnexpectedByte {
                    expected: expected_name,
                    actual,
                },
            )),
            None => Err(self.error(JsonParseErrorKind::UnexpectedEof)),
        }
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.offset += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.offset).copied()
    }

    fn take_byte(&mut self) -> Option<u8> {
        let byte = self.peek()?;
        self.offset += 1;
        Some(byte)
    }

    fn is_done(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn error(&self, kind: JsonParseErrorKind) -> JsonParseError {
        self.error_at(self.offset, kind)
    }

    fn error_at(&self, offset: usize, kind: JsonParseErrorKind) -> JsonParseError {
        JsonParseError { offset, kind }
    }
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_nesting_limit_accepts_boundary_and_rejects_next_level() {
        let mut boundary = "[".repeat(MAX_JSON_NESTING_DEPTH);
        boundary.push('0');
        boundary.push_str(&"]".repeat(MAX_JSON_NESTING_DEPTH));
        assert!(parse_json(&boundary).is_ok());

        let mut over_limit = "[".repeat(MAX_JSON_NESTING_DEPTH + 1);
        over_limit.push('0');
        over_limit.push_str(&"]".repeat(MAX_JSON_NESTING_DEPTH + 1));
        let error = parse_json(&over_limit).expect_err("excessive nesting must fail closed");
        assert_eq!(
            error.kind,
            JsonParseErrorKind::NestingDepthExceeded {
                max_depth: MAX_JSON_NESTING_DEPTH,
            }
        );
    }

    #[test]
    fn json_resource_limits_reject_before_the_next_container_or_string_item() {
        let limits = JsonResourceLimits {
            nesting_depth: 2,
            string_bytes: 4,
            number_bytes: 4,
            array_elements: 2,
            object_members: 2,
            array_member_elements: &[("x", 1)],
        };

        assert!(parse_json_with_limits(r#"{"a":"four","b":[]}"#, limits).is_ok());
        assert_eq!(
            parse_json_with_limits(r#""12345""#, limits)
                .unwrap_err()
                .kind,
            JsonParseErrorKind::StringBytesExceeded { max_bytes: 4 }
        );
        assert_eq!(
            parse_json_with_limits("12345", limits).unwrap_err().kind,
            JsonParseErrorKind::NumberBytesExceeded { max_bytes: 4 }
        );
        assert_eq!(
            parse_json_with_limits("[0,1,2]", limits).unwrap_err().kind,
            JsonParseErrorKind::ArrayElementsExceeded { max_elements: 2 }
        );
        assert!(parse_json_with_limits(r#"{"x":[0]}"#, limits).is_ok());
        assert_eq!(
            parse_json_with_limits(r#"{"x":[0,1]}"#, limits)
                .unwrap_err()
                .kind,
            JsonParseErrorKind::ArrayElementsExceeded { max_elements: 1 }
        );
        assert_eq!(
            parse_json_with_limits(r#"{"a":0,"b":1,"c":2}"#, limits)
                .unwrap_err()
                .kind,
            JsonParseErrorKind::ObjectMembersExceeded { max_members: 2 }
        );
        assert_eq!(
            parse_json_with_limits("[[[0]]]", limits).unwrap_err().kind,
            JsonParseErrorKind::NestingDepthExceeded { max_depth: 2 }
        );
    }
}
