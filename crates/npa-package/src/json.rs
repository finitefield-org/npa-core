#![allow(missing_docs)]

use std::fmt;

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
}

pub(crate) fn parse_json(source: &str) -> Result<JsonValue, JsonParseError> {
    let mut parser = Parser::new(source);
    let value = parser.parse_value()?;
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
}

impl<'src> Parser<'src> {
    fn new(source: &'src str) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            offset: 0,
        }
    }

    fn parse_value(&mut self) -> Result<JsonValue, JsonParseError> {
        self.skip_ws();
        let Some(byte) = self.peek() else {
            return Err(self.error(JsonParseErrorKind::ExpectedValue));
        };

        match byte {
            b'n' => self.parse_literal(b"null", JsonValue::Null),
            b't' => self.parse_literal(b"true", JsonValue::Bool(true)),
            b'f' => self.parse_literal(b"false", JsonValue::Bool(false)),
            b'"' => self.parse_string().map(JsonValue::String),
            b'[' => self.parse_array(),
            b'{' => self.parse_object(),
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
                    out.push(ch);
                }
            }
        }
    }

    fn parse_string_escape(&mut self, out: &mut String) -> Result<(), JsonParseError> {
        let Some(byte) = self.take_byte() else {
            return Err(self.error(JsonParseErrorKind::UnexpectedEof));
        };
        match byte {
            b'"' => out.push('"'),
            b'\\' => out.push('\\'),
            b'/' => out.push('/'),
            b'b' => out.push('\u{0008}'),
            b'f' => out.push('\u{000c}'),
            b'n' => out.push('\n'),
            b'r' => out.push('\r'),
            b't' => out.push('\t'),
            b'u' => self.parse_unicode_escape(out)?,
            _ => return Err(self.error(JsonParseErrorKind::InvalidEscape)),
        }
        Ok(())
    }

    fn parse_unicode_escape(&mut self, out: &mut String) -> Result<(), JsonParseError> {
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

    fn parse_array(&mut self) -> Result<JsonValue, JsonParseError> {
        self.consume_expected_byte(b'[', "array")?;
        let mut values = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b']') {
            self.offset += 1;
            return Ok(JsonValue::Array(values));
        }

        loop {
            values.push(self.parse_value()?);
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

    fn parse_object(&mut self) -> Result<JsonValue, JsonParseError> {
        self.consume_expected_byte(b'{', "object")?;
        let mut members = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b'}') {
            self.offset += 1;
            return Ok(JsonValue::Object(members));
        }

        loop {
            self.skip_ws();
            if self.peek() != Some(b'"') {
                return Err(self.error(JsonParseErrorKind::UnexpectedByte {
                    expected: "object key string",
                    actual: self.peek().unwrap_or_default(),
                }));
            }
            let key = self.parse_string()?;
            self.skip_ws();
            self.consume_expected_byte(b':', "object colon")?;
            let value = self.parse_value()?;
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
