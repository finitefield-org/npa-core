#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JsonSpan {
    pub start: usize,
    pub end: usize,
}

impl JsonSpan {
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct JsonDocument<'src> {
    source: &'src str,
    root: JsonValue<'src>,
}

impl<'src> JsonDocument<'src> {
    pub fn parse(source: &'src str) -> Result<Self, JsonParseError> {
        Self::parse_with_limits(source, JsonParseLimits::default())
    }

    pub fn parse_with_limits(
        source: &'src str,
        limits: JsonParseLimits,
    ) -> Result<Self, JsonParseError> {
        let mut parser = Parser::new(source, limits.capped());
        let root = parser.parse_document()?;
        Ok(Self { source, root })
    }

    pub const fn source(&self) -> &'src str {
        self.source
    }

    pub const fn root(&self) -> &JsonValue<'src> {
        &self.root
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JsonParseLimits {
    pub max_depth: usize,
}

impl JsonParseLimits {
    pub const MAX_DEPTH: usize = 512;

    const fn capped(self) -> Self {
        Self {
            max_depth: if self.max_depth > Self::MAX_DEPTH {
                Self::MAX_DEPTH
            } else {
                self.max_depth
            },
        }
    }
}

impl Default for JsonParseLimits {
    fn default() -> Self {
        Self {
            max_depth: Self::MAX_DEPTH,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct JsonValue<'src> {
    raw: &'src str,
    span: JsonSpan,
    data: JsonValueData<'src>,
}

#[derive(Clone, Debug, PartialEq)]
enum JsonValueData<'src> {
    Null,
    Bool(bool),
    Number,
    String(String),
    Array(Vec<JsonValue<'src>>),
    Object(Vec<JsonMember<'src>>),
}

impl<'src> JsonValue<'src> {
    pub const fn span(&self) -> JsonSpan {
        self.span
    }

    pub const fn raw_slice(&self) -> &'src str {
        self.raw
    }

    pub fn kind(&self) -> JsonValueKind {
        match &self.data {
            JsonValueData::Null => JsonValueKind::Null,
            JsonValueData::Bool(_) => JsonValueKind::Bool,
            JsonValueData::Number => JsonValueKind::Number,
            JsonValueData::String(_) => JsonValueKind::String,
            JsonValueData::Array(_) => JsonValueKind::Array,
            JsonValueData::Object(_) => JsonValueKind::Object,
        }
    }

    pub fn bool_value(&self) -> Option<bool> {
        match self.data {
            JsonValueData::Bool(value) => Some(value),
            _ => None,
        }
    }

    pub fn number_raw(&self) -> Option<&'src str> {
        match self.data {
            JsonValueData::Number => Some(self.raw),
            _ => None,
        }
    }

    pub fn string_value(&self) -> Option<&str> {
        match &self.data {
            JsonValueData::String(value) => Some(value),
            _ => None,
        }
    }

    pub fn array_elements(&self) -> Option<&[JsonValue<'src>]> {
        match &self.data {
            JsonValueData::Array(elements) => Some(elements),
            _ => None,
        }
    }

    pub fn object_members(&self) -> Option<&[JsonMember<'src>]> {
        match &self.data {
            JsonValueData::Object(members) => Some(members),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonValueKind {
    Null,
    Bool,
    Number,
    String,
    Array,
    Object,
}

#[derive(Clone, Debug, PartialEq)]
pub struct JsonMember<'src> {
    key: String,
    key_span: JsonSpan,
    value: JsonValue<'src>,
}

impl<'src> JsonMember<'src> {
    pub fn key(&self) -> &str {
        &self.key
    }

    pub const fn key_span(&self) -> JsonSpan {
        self.key_span
    }

    pub const fn value(&self) -> &JsonValue<'src> {
        &self.value
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonParseError {
    pub offset: usize,
    pub kind: JsonParseErrorKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonParseErrorKind {
    ExpectedValue,
    UnexpectedEof,
    UnexpectedByte { expected: &'static str, actual: u8 },
    TrailingCharacters,
    InvalidNumber,
    InvalidEscape,
    InvalidUnicodeEscape,
    ControlCharacterInString,
    NestingDepthExceeded { max_depth: usize },
}

struct Parser<'src> {
    source: &'src str,
    bytes: &'src [u8],
    offset: usize,
    limits: JsonParseLimits,
}

impl<'src> Parser<'src> {
    fn new(source: &'src str, limits: JsonParseLimits) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            offset: 0,
            limits,
        }
    }

    fn parse_document(&mut self) -> Result<JsonValue<'src>, JsonParseError> {
        let value = self.parse_value(0)?;
        self.skip_ws();
        if self.offset == self.bytes.len() {
            Ok(value)
        } else {
            Err(self.error(JsonParseErrorKind::TrailingCharacters))
        }
    }

    fn parse_value(&mut self, depth: usize) -> Result<JsonValue<'src>, JsonParseError> {
        if depth > self.limits.max_depth {
            return Err(self.error(JsonParseErrorKind::NestingDepthExceeded {
                max_depth: self.limits.max_depth,
            }));
        }

        self.skip_ws();
        let Some(byte) = self.peek() else {
            return Err(self.error(JsonParseErrorKind::ExpectedValue));
        };
        match byte {
            b'n' => self.parse_null(),
            b't' => self.parse_bool(true),
            b'f' => self.parse_bool(false),
            b'"' => self.parse_string_value(),
            b'[' => self.parse_array(depth),
            b'{' => self.parse_object(depth),
            b'-' | b'0'..=b'9' => self.parse_number(),
            _ => Err(self.error(JsonParseErrorKind::ExpectedValue)),
        }
    }

    fn parse_null(&mut self) -> Result<JsonValue<'src>, JsonParseError> {
        let start = self.offset;
        self.consume_literal(b"null")?;
        Ok(JsonValue {
            raw: &self.source[start..self.offset],
            span: JsonSpan::new(start, self.offset),
            data: JsonValueData::Null,
        })
    }

    fn parse_bool(&mut self, value: bool) -> Result<JsonValue<'src>, JsonParseError> {
        let start = self.offset;
        if value {
            self.consume_literal(b"true")?;
        } else {
            self.consume_literal(b"false")?;
        }
        Ok(JsonValue {
            raw: &self.source[start..self.offset],
            span: JsonSpan::new(start, self.offset),
            data: JsonValueData::Bool(value),
        })
    }

    fn parse_string_value(&mut self) -> Result<JsonValue<'src>, JsonParseError> {
        let (value, span) = self.parse_string_token()?;
        Ok(JsonValue {
            raw: &self.source[span.start..span.end],
            span,
            data: JsonValueData::String(value),
        })
    }

    fn parse_array(&mut self, depth: usize) -> Result<JsonValue<'src>, JsonParseError> {
        let start = self.offset;
        self.expect_byte(b'[', "'['")?;
        self.skip_ws();

        let mut elements = Vec::new();
        if self.try_consume(b']') {
            return Ok(JsonValue {
                raw: &self.source[start..self.offset],
                span: JsonSpan::new(start, self.offset),
                data: JsonValueData::Array(elements),
            });
        }

        loop {
            elements.push(self.parse_value(depth + 1)?);
            self.skip_ws();
            if self.try_consume(b']') {
                break;
            }
            self.expect_byte(b',', "',' or ']'")?;
        }

        Ok(JsonValue {
            raw: &self.source[start..self.offset],
            span: JsonSpan::new(start, self.offset),
            data: JsonValueData::Array(elements),
        })
    }

    fn parse_object(&mut self, depth: usize) -> Result<JsonValue<'src>, JsonParseError> {
        let start = self.offset;
        self.expect_byte(b'{', "'{'")?;
        self.skip_ws();

        let mut members = Vec::new();
        if self.try_consume(b'}') {
            return Ok(JsonValue {
                raw: &self.source[start..self.offset],
                span: JsonSpan::new(start, self.offset),
                data: JsonValueData::Object(members),
            });
        }

        loop {
            self.skip_ws();
            let (key, key_span) = self.parse_string_token()?;
            self.skip_ws();
            self.expect_byte(b':', "':'")?;
            let value = self.parse_value(depth + 1)?;
            members.push(JsonMember {
                key,
                key_span,
                value,
            });
            self.skip_ws();
            if self.try_consume(b'}') {
                break;
            }
            self.expect_byte(b',', "',' or '}'")?;
        }

        Ok(JsonValue {
            raw: &self.source[start..self.offset],
            span: JsonSpan::new(start, self.offset),
            data: JsonValueData::Object(members),
        })
    }

    fn parse_number(&mut self) -> Result<JsonValue<'src>, JsonParseError> {
        let start = self.offset;

        self.try_consume(b'-');
        self.consume_integer_part()?;

        if self.try_consume(b'.') {
            self.consume_digits()?;
        }

        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.offset += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.offset += 1;
            }
            self.consume_digits()?;
        }

        Ok(JsonValue {
            raw: &self.source[start..self.offset],
            span: JsonSpan::new(start, self.offset),
            data: JsonValueData::Number,
        })
    }

    fn consume_integer_part(&mut self) -> Result<(), JsonParseError> {
        match self.peek() {
            Some(b'0') => {
                self.offset += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return Err(self.error(JsonParseErrorKind::InvalidNumber));
                }
                Ok(())
            }
            Some(b'1'..=b'9') => {
                self.offset += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.offset += 1;
                }
                Ok(())
            }
            Some(_) => Err(self.error(JsonParseErrorKind::InvalidNumber)),
            None => Err(self.error(JsonParseErrorKind::UnexpectedEof)),
        }
    }

    fn consume_digits(&mut self) -> Result<(), JsonParseError> {
        let start = self.offset;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.offset += 1;
        }
        if self.offset == start {
            Err(self.error(JsonParseErrorKind::InvalidNumber))
        } else {
            Ok(())
        }
    }

    fn parse_string_token(&mut self) -> Result<(String, JsonSpan), JsonParseError> {
        let start = self.offset;
        self.expect_byte(b'"', "'\"'")?;

        let mut value = String::new();
        loop {
            let Some(byte) = self.peek() else {
                return Err(self.error(JsonParseErrorKind::UnexpectedEof));
            };

            match byte {
                b'"' => {
                    self.offset += 1;
                    return Ok((value, JsonSpan::new(start, self.offset)));
                }
                b'\\' => {
                    self.offset += 1;
                    self.parse_escape(&mut value)?;
                }
                0x00..=0x1f => {
                    return Err(self.error(JsonParseErrorKind::ControlCharacterInString));
                }
                _ => {
                    let Some(ch) = self.source[self.offset..].chars().next() else {
                        return Err(self.error(JsonParseErrorKind::UnexpectedEof));
                    };
                    self.offset += ch.len_utf8();
                    value.push(ch);
                }
            }
        }
    }

    fn parse_escape(&mut self, out: &mut String) -> Result<(), JsonParseError> {
        let Some(byte) = self.peek() else {
            return Err(self.error(JsonParseErrorKind::UnexpectedEof));
        };
        self.offset += 1;
        match byte {
            b'"' => out.push('"'),
            b'\\' => out.push('\\'),
            b'/' => out.push('/'),
            b'b' => out.push('\u{0008}'),
            b'f' => out.push('\u{000c}'),
            b'n' => out.push('\n'),
            b'r' => out.push('\r'),
            b't' => out.push('\t'),
            b'u' => {
                let unit = self.parse_hex_u16()?;
                self.push_unicode_escape(unit, out)?;
            }
            _ => return Err(self.error(JsonParseErrorKind::InvalidEscape)),
        }
        Ok(())
    }

    fn push_unicode_escape(&mut self, unit: u16, out: &mut String) -> Result<(), JsonParseError> {
        if (0xd800..=0xdbff).contains(&unit) {
            if self.peek() != Some(b'\\') || self.bytes.get(self.offset + 1) != Some(&b'u') {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            }
            self.offset += 2;
            let low = self.parse_hex_u16()?;
            if !(0xdc00..=0xdfff).contains(&low) {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            }
            let high_ten = u32::from(unit - 0xd800);
            let low_ten = u32::from(low - 0xdc00);
            let scalar = 0x1_0000 + ((high_ten << 10) | low_ten);
            let Some(ch) = char::from_u32(scalar) else {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            };
            out.push(ch);
            return Ok(());
        }

        if (0xdc00..=0xdfff).contains(&unit) {
            return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
        }

        let Some(ch) = char::from_u32(u32::from(unit)) else {
            return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
        };
        out.push(ch);
        Ok(())
    }

    fn parse_hex_u16(&mut self) -> Result<u16, JsonParseError> {
        let mut value = 0u16;
        for _ in 0..4 {
            let Some(byte) = self.peek() else {
                return Err(self.error(JsonParseErrorKind::UnexpectedEof));
            };
            let Some(digit) = hex_value(byte) else {
                return Err(self.error(JsonParseErrorKind::InvalidUnicodeEscape));
            };
            self.offset += 1;
            value = (value << 4) | u16::from(digit);
        }
        Ok(value)
    }

    fn consume_literal(&mut self, literal: &[u8]) -> Result<(), JsonParseError> {
        for expected in literal {
            match self.peek() {
                Some(actual) if actual == *expected => self.offset += 1,
                Some(actual) => {
                    return Err(self.error(JsonParseErrorKind::UnexpectedByte {
                        expected: "literal",
                        actual,
                    }));
                }
                None => return Err(self.error(JsonParseErrorKind::UnexpectedEof)),
            }
        }
        Ok(())
    }

    fn expect_byte(
        &mut self,
        expected: u8,
        expected_name: &'static str,
    ) -> Result<(), JsonParseError> {
        match self.peek() {
            Some(actual) if actual == expected => {
                self.offset += 1;
                Ok(())
            }
            Some(actual) => Err(self.error(JsonParseErrorKind::UnexpectedByte {
                expected: expected_name,
                actual,
            })),
            None => Err(self.error(JsonParseErrorKind::UnexpectedEof)),
        }
    }

    fn try_consume(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.offset += 1;
            true
        } else {
            false
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

    fn error(&self, kind: JsonParseErrorKind) -> JsonParseError {
        JsonParseError {
            offset: self.offset,
            kind,
        }
    }
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}
