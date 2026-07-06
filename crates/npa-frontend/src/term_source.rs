use crate::{
    parse_machine_term, FileId, MachineLevel, MachineTerm, MachineTermAst,
    MachineTermSourceCanonical, Result, Span,
};
use sha2::{Digest, Sha256};

const TERM_SOURCE_TAG: &str = "npa.frontend.machine-term-source.v1";
const MAX_CANONICAL_STRING_LEN: usize = 1 << 20;
const MAX_CANONICAL_LIST_LEN: usize = 100_000;
const MAX_CANONICAL_NODES: usize = 100_000;
const MAX_CANONICAL_DEPTH: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineSurfaceToken {
    pub kind: MachineSurfaceTokenKind,
    pub spelling: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineSurfaceTokenKind {
    IdentLike,
    Reserved,
    Dot,
    Punctuation,
    Natural,
    StringLiteral,
    Whitespace,
    Comment,
    ExternalCommand,
}

pub fn canonicalize_machine_term_source(source: &str) -> Result<MachineTermSourceCanonical> {
    let term = parse_machine_term(FileId(0), source)?;
    validate_term_for_canonical_encoding(&term)?;
    let mut canonical_bytes = Vec::new();
    encode_string_to(&mut canonical_bytes, TERM_SOURCE_TAG);
    encode_term_to(&mut canonical_bytes, &term);
    let canonical_hash = hash_bytes(&canonical_bytes);

    Ok(MachineTermSourceCanonical {
        source: source.to_owned(),
        canonical_bytes,
        canonical_hash,
    })
}

fn validate_term_for_canonical_encoding(term: &MachineTerm) -> Result<()> {
    let mut remaining_nodes = MAX_CANONICAL_NODES;
    validate_term_for_canonical_encoding_at_depth(term, 0, &mut remaining_nodes)
}

fn validate_term_for_canonical_encoding_at_depth(
    term: &MachineTerm,
    depth: usize,
    remaining_nodes: &mut usize,
) -> Result<()> {
    ensure_canonical_depth(depth)?;
    consume_canonical_node(remaining_nodes)?;
    match term {
        MachineTerm::Ident {
            name,
            universe_args,
            ..
        } => {
            validate_name_for_canonical_encoding(&name.parts)?;
            if let Some(levels) = universe_args {
                ensure_non_empty_canonical_list(
                    !levels.is_empty(),
                    "explicit universe argument list",
                )?;
                ensure_canonical_list_len(levels.len(), "explicit universe argument list")?;
                for level in levels {
                    validate_level_for_canonical_encoding_at_depth(
                        level,
                        child_depth(depth)?,
                        remaining_nodes,
                    )?;
                }
            }
        }
        MachineTerm::Local { .. } | MachineTerm::Prop { .. } => {}
        MachineTerm::Type { level, .. } | MachineTerm::Sort { level, .. } => {
            validate_level_for_canonical_encoding_at_depth(
                level,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
        MachineTerm::App { func, arg, .. } => {
            validate_term_for_canonical_encoding_at_depth(
                func,
                child_depth(depth)?,
                remaining_nodes,
            )?;
            validate_term_for_canonical_encoding_at_depth(
                arg,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
        MachineTerm::Lam { binders, body, .. } | MachineTerm::Pi { binders, body, .. } => {
            ensure_non_empty_canonical_list(!binders.is_empty(), "binder list")?;
            ensure_canonical_list_len(binders.len(), "binder list")?;
            for binder in binders {
                validate_identifier_for_canonical_encoding(&binder.name, "binder name")?;
                validate_term_for_canonical_encoding_at_depth(
                    &binder.ty,
                    child_depth(depth)?,
                    remaining_nodes,
                )?;
            }
            validate_term_for_canonical_encoding_at_depth(
                body,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
        MachineTerm::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            validate_identifier_for_canonical_encoding(name, "let name")?;
            validate_term_for_canonical_encoding_at_depth(
                ty,
                child_depth(depth)?,
                remaining_nodes,
            )?;
            validate_term_for_canonical_encoding_at_depth(
                value,
                child_depth(depth)?,
                remaining_nodes,
            )?;
            validate_term_for_canonical_encoding_at_depth(
                body,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
        MachineTerm::Annot { expr, ty, .. } => {
            validate_term_for_canonical_encoding_at_depth(
                expr,
                child_depth(depth)?,
                remaining_nodes,
            )?;
            validate_term_for_canonical_encoding_at_depth(
                ty,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
    }
    Ok(())
}

fn validate_level_for_canonical_encoding_at_depth(
    level: &MachineLevel,
    depth: usize,
    remaining_nodes: &mut usize,
) -> Result<()> {
    ensure_canonical_depth(depth)?;
    consume_canonical_node(remaining_nodes)?;
    match level {
        MachineLevel::Nat { .. } => {}
        MachineLevel::Param { name, .. } => {
            validate_identifier_for_canonical_encoding(name, "universe level parameter")?;
        }
        MachineLevel::Succ { level, .. } => validate_level_for_canonical_encoding_at_depth(
            level,
            child_depth(depth)?,
            remaining_nodes,
        )?,
        MachineLevel::Max { lhs, rhs, .. } | MachineLevel::IMax { lhs, rhs, .. } => {
            validate_level_for_canonical_encoding_at_depth(
                lhs,
                child_depth(depth)?,
                remaining_nodes,
            )?;
            validate_level_for_canonical_encoding_at_depth(
                rhs,
                child_depth(depth)?,
                remaining_nodes,
            )?;
        }
    }
    Ok(())
}

fn validate_name_for_canonical_encoding(parts: &[String]) -> Result<()> {
    ensure_non_empty_canonical_list(!parts.is_empty(), "name")?;
    ensure_canonical_list_len(parts.len(), "name component list")?;
    validate_identifier_for_canonical_encoding(&parts[0], "name head component")?;
    for part in &parts[1..] {
        validate_dotted_name_component_for_canonical_encoding(part)?;
    }
    Ok(())
}

fn validate_dotted_name_component_for_canonical_encoding(value: &str) -> Result<()> {
    ensure_canonical_string_len(value)?;
    if !is_machine_identifier(value) {
        return Err(canonical_validation_error(
            "invalid canonical dotted name component",
        ));
    }
    Ok(())
}

fn validate_identifier_for_canonical_encoding(value: &str, what: &'static str) -> Result<()> {
    ensure_canonical_string_len(value)?;
    if !is_machine_identifier(value) || is_reserved_spelling(value) {
        return Err(canonical_validation_error(format!(
            "invalid canonical {what}"
        )));
    }
    Ok(())
}

fn ensure_non_empty_canonical_list(non_empty: bool, what: &'static str) -> Result<()> {
    if !non_empty {
        return Err(canonical_validation_error(format!(
            "empty canonical {what}"
        )));
    }
    Ok(())
}

fn ensure_canonical_list_len(len: usize, what: &'static str) -> Result<()> {
    if len > MAX_CANONICAL_LIST_LEN {
        return Err(canonical_validation_error(format!(
            "canonical {what} is too large"
        )));
    }
    Ok(())
}

fn ensure_canonical_string_len(value: &str) -> Result<()> {
    if value.len() > MAX_CANONICAL_STRING_LEN {
        return Err(canonical_validation_error("canonical string is too large"));
    }
    Ok(())
}

fn consume_canonical_node(remaining_nodes: &mut usize) -> Result<()> {
    *remaining_nodes = remaining_nodes
        .checked_sub(1)
        .ok_or_else(|| canonical_validation_error("canonical term is too large"))?;
    Ok(())
}

fn canonical_validation_error(message: impl Into<String>) -> crate::MachineDiagnostic {
    crate::MachineDiagnostic::parse(Span::empty(FileId(0)), message)
}

fn ensure_canonical_depth(depth: usize) -> Result<()> {
    if depth > MAX_CANONICAL_DEPTH {
        return Err(crate::MachineDiagnostic::parse(
            Span::empty(FileId(0)),
            "canonical term nesting is too deep",
        ));
    }
    Ok(())
}

fn child_depth(depth: usize) -> Result<usize> {
    depth.checked_add(1).ok_or_else(|| {
        crate::MachineDiagnostic::parse(
            Span::empty(FileId(0)),
            "canonical term nesting is too deep",
        )
    })
}

pub fn lex_machine_surface_tokens(source: &str) -> Result<Vec<MachineSurfaceToken>> {
    let file_id = FileId(0);
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();

    while let Some((offset, ch)) = chars.next() {
        let start = offset;
        let (kind, end) = match ch {
            ch if ch.is_whitespace() => (
                MachineSurfaceTokenKind::Whitespace,
                consume_while_end(offset, ch, &mut chars, |candidate| {
                    candidate.is_whitespace()
                }),
            ),
            '-' if matches!(chars.peek(), Some((_, '-'))) => {
                let (_, second) = chars.next().expect("peeked comment marker");
                let mut end = offset + ch.len_utf8() + second.len_utf8();
                while let Some((next_offset, next)) = chars.peek().copied() {
                    if next == '\n' {
                        break;
                    }
                    chars.next();
                    end = next_offset + next.len_utf8();
                }
                (MachineSurfaceTokenKind::Comment, end)
            }
            '"' => (
                MachineSurfaceTokenKind::StringLiteral,
                consume_string_literal_end(source, offset, &mut chars)?,
            ),
            '.' => (MachineSurfaceTokenKind::Dot, offset + ch.len_utf8()),
            '0'..='9' => (
                MachineSurfaceTokenKind::Natural,
                consume_natural_end(file_id, source, offset, ch, &mut chars)?,
            ),
            ident if is_machine_identifier_start(ident) => {
                let end =
                    consume_while_end(offset, ident, &mut chars, is_machine_identifier_continue);
                let spelling = &source[start..end];
                let kind = if is_reserved_spelling(spelling) {
                    MachineSurfaceTokenKind::Reserved
                } else {
                    MachineSurfaceTokenKind::IdentLike
                };
                (kind, end)
            }
            ':' => {
                let end = consume_punctuation_pair(offset, ch, &mut chars, '=');
                (MachineSurfaceTokenKind::Punctuation, end)
            }
            '=' => {
                if !matches!(chars.peek(), Some((_, '>'))) {
                    return Err(crate::MachineDiagnostic::unsupported_syntax(
                        Span::new(file_id, start as u32, (start + ch.len_utf8()) as u32),
                        "character is not part of Machine Surface syntax",
                    ));
                }
                let end = consume_punctuation_pair(offset, ch, &mut chars, '>');
                (MachineSurfaceTokenKind::Punctuation, end)
            }
            '?' => (
                MachineSurfaceTokenKind::Punctuation,
                consume_optional_named_hole_end(offset, &mut chars),
            ),
            '{' | '}' | '(' | ')' | ',' | '@' | '_' => {
                (MachineSurfaceTokenKind::Punctuation, offset + ch.len_utf8())
            }
            _ => {
                return Err(crate::MachineDiagnostic::unsupported_syntax(
                    Span::new(file_id, start as u32, (start + ch.len_utf8()) as u32),
                    "character is not part of Machine Surface syntax",
                ));
            }
        };

        tokens.push(MachineSurfaceToken {
            kind,
            spelling: source[start..end].to_owned(),
            span: Span::new(file_id, start as u32, end as u32),
        });
    }

    Ok(tokens)
}

fn consume_while_end(
    first_offset: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    mut predicate: impl FnMut(char) -> bool,
) -> usize {
    let mut end = first_offset + first.len_utf8();
    while let Some((offset, ch)) = chars.peek().copied() {
        if !predicate(ch) {
            break;
        }
        chars.next();
        end = offset + ch.len_utf8();
    }
    end
}

fn consume_string_literal_end(
    source: &str,
    start: usize,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<usize> {
    let mut escaped = false;
    for (offset, ch) in chars.by_ref() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == '"' {
            return Ok(offset + ch.len_utf8());
        }
    }

    Err(crate::MachineDiagnostic::parse(
        Span::new(FileId(0), start as u32, source.len() as u32),
        "unterminated string literal",
    ))
}

fn consume_natural_end(
    file_id: FileId,
    source: &str,
    start: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<usize> {
    let end = consume_while_end(start, first, chars, |candidate| candidate.is_ascii_digit());
    let span = Span::new(file_id, start as u32, end as u32);
    source[start..end].parse::<u64>().map_err(|_| {
        crate::MachineDiagnostic::parse(span, "universe level numeral is too large")
    })?;
    Ok(end)
}

fn consume_punctuation_pair(
    first_offset: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    second: char,
) -> usize {
    let Some((offset, ch)) = chars.peek().copied() else {
        return first_offset + first.len_utf8();
    };
    if ch != second {
        return first_offset + first.len_utf8();
    }
    chars.next();
    offset + ch.len_utf8()
}

fn consume_optional_named_hole_end(
    start: usize,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    let Some((first_offset, first)) = chars.peek().copied() else {
        return start + 1;
    };
    if !is_machine_identifier_start(first) {
        return start + 1;
    }
    chars.next();
    consume_while_end(first_offset, first, chars, is_machine_identifier_continue)
}

pub fn decode_machine_term_source_canonical(canonical_bytes: &[u8]) -> Result<MachineTermAst> {
    let mut decoder = Decoder::new(canonical_bytes);
    let tag = decoder.string()?;
    if tag != TERM_SOURCE_TAG {
        return Err(crate::MachineDiagnostic::parse(
            Span::empty(FileId(0)),
            "unexpected Machine Surface term-source canonical tag",
        ));
    }
    let term = decoder.term()?;
    decoder.finish()?;
    Ok(MachineTermAst { term })
}

fn hash_bytes(bytes: &[u8]) -> npa_cert::Hash {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

fn is_machine_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    is_machine_identifier_start(first) && chars.all(is_machine_identifier_continue)
}

fn is_machine_identifier_start(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}

fn is_machine_identifier_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '\''
}

fn is_reserved_spelling(value: &str) -> bool {
    is_level_operator(value)
        || matches!(
            value,
            "import"
                | "def"
                | "theorem"
                | "fun"
                | "forall"
                | "let"
                | "in"
                | "Prop"
                | "Type"
                | "Sort"
                | "open"
                | "namespace"
                | "match"
                | "with"
                | "notation"
                | "infix"
                | "infixl"
                | "infixr"
                | "axiom"
                | "inductive"
        )
}

fn is_level_operator(value: &str) -> bool {
    matches!(value, "succ" | "max" | "imax")
}

fn encode_term_to(out: &mut Vec<u8>, term: &MachineTerm) {
    match term {
        MachineTerm::Ident {
            name,
            universe_args,
            explicit_mode,
            ..
        } => {
            out.push(0x00);
            encode_name_to(out, &name.parts);
            out.push(u8::from(*explicit_mode));
            encode_option_levels_to(out, universe_args.as_deref());
        }
        MachineTerm::Local { .. } => {
            unreachable!("canonical Machine Surface source is encoded before local resolution")
        }
        MachineTerm::Prop { .. } => {
            out.push(0x09);
        }
        MachineTerm::Type { level, .. } => {
            out.push(0x08);
            encode_machine_level_to(out, level);
        }
        MachineTerm::Sort { level, .. } => {
            out.push(0x02);
            encode_machine_level_to(out, level);
        }
        MachineTerm::App { func, arg, .. } => {
            out.push(0x03);
            encode_term_to(out, func);
            encode_term_to(out, arg);
        }
        MachineTerm::Lam { binders, body, .. } => {
            out.push(0x04);
            encode_binders_to(out, binders);
            encode_term_to(out, body);
        }
        MachineTerm::Pi { binders, body, .. } => {
            out.push(0x05);
            encode_binders_to(out, binders);
            encode_term_to(out, body);
        }
        MachineTerm::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            out.push(0x06);
            encode_string_to(out, name);
            encode_term_to(out, ty);
            encode_term_to(out, value);
            encode_term_to(out, body);
        }
        MachineTerm::Annot { expr, ty, .. } => {
            out.push(0x07);
            encode_term_to(out, expr);
            encode_term_to(out, ty);
        }
    }
}

fn encode_binders_to(out: &mut Vec<u8>, binders: &[crate::MachineBinder]) {
    encode_uvar_to(out, binders.len() as u64);
    for binder in binders {
        encode_string_to(out, &binder.name);
        encode_term_to(out, &binder.ty);
    }
}

fn encode_option_levels_to(out: &mut Vec<u8>, levels: Option<&[MachineLevel]>) {
    match levels {
        Some(levels) => {
            out.push(0x01);
            encode_uvar_to(out, levels.len() as u64);
            for level in levels {
                encode_machine_level_to(out, level);
            }
        }
        None => out.push(0x00),
    }
}

fn encode_machine_level_to(out: &mut Vec<u8>, level: &MachineLevel) {
    match level {
        MachineLevel::Nat { value, .. } => {
            out.push(0x00);
            encode_uvar_to(out, *value);
        }
        MachineLevel::Param { name, .. } => {
            out.push(0x01);
            encode_string_to(out, name);
        }
        MachineLevel::Succ { level, .. } => {
            out.push(0x02);
            encode_machine_level_to(out, level);
        }
        MachineLevel::Max { lhs, rhs, .. } => {
            out.push(0x03);
            encode_machine_level_to(out, lhs);
            encode_machine_level_to(out, rhs);
        }
        MachineLevel::IMax { lhs, rhs, .. } => {
            out.push(0x04);
            encode_machine_level_to(out, lhs);
            encode_machine_level_to(out, rhs);
        }
    }
}

fn encode_name_to(out: &mut Vec<u8>, parts: &[String]) {
    encode_uvar_to(out, parts.len() as u64);
    for part in parts {
        encode_string_to(out, part);
    }
}

fn encode_string_to(out: &mut Vec<u8>, value: &str) {
    encode_uvar_to(out, value.len() as u64);
    out.extend(value.as_bytes());
}

fn encode_uvar_to(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
    remaining_nodes: usize,
}

impl<'a> Decoder<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            offset: 0,
            remaining_nodes: MAX_CANONICAL_NODES,
        }
    }

    fn finish(&self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(crate::MachineDiagnostic::parse(
                Span::empty(FileId(0)),
                "trailing bytes in Machine Surface term-source canonical bytes",
            ))
        }
    }

    fn term(&mut self) -> Result<MachineTerm> {
        self.term_at_depth(0)
    }

    fn term_at_depth(&mut self, depth: usize) -> Result<MachineTerm> {
        self.ensure_depth(depth)?;
        self.consume_node()?;
        let tag = self.byte()?;
        let span = Span::empty(FileId(0));
        match tag {
            0x00 => {
                let name = crate::MachineName::new(self.name()?, span);
                let explicit_mode = match self.byte()? {
                    0x00 => false,
                    0x01 => true,
                    _ => return Err(self.decode_error("invalid explicit-mode byte")),
                };
                let universe_args = self.option_levels(self.child_depth(depth)?)?;
                Ok(MachineTerm::Ident {
                    name,
                    universe_args,
                    explicit_mode,
                    span,
                })
            }
            0x01 => {
                Err(self.decode_error("local term tag is not canonical Machine Surface source"))
            }
            0x02 => Ok(MachineTerm::Sort {
                level: self.machine_level_at_depth(self.child_depth(depth)?)?,
                span,
            }),
            0x03 => Ok(MachineTerm::App {
                func: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                arg: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x04 => Ok(MachineTerm::Lam {
                binders: self.binders(self.child_depth(depth)?)?,
                body: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x05 => Ok(MachineTerm::Pi {
                binders: self.binders(self.child_depth(depth)?)?,
                body: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x06 => Ok(MachineTerm::Let {
                name: self.identifier("let name")?,
                ty: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                value: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                body: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x07 => Ok(MachineTerm::Annot {
                expr: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                ty: Box::new(self.term_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x08 => Ok(MachineTerm::Type {
                level: self.machine_level_at_depth(self.child_depth(depth)?)?,
                span,
            }),
            0x09 => Ok(MachineTerm::Prop { span }),
            _ => Err(self.decode_error("unknown Machine Surface term canonical tag")),
        }
    }

    fn binders(&mut self, depth: usize) -> Result<Vec<crate::MachineBinder>> {
        let len = self.usize()?;
        if len == 0 {
            return Err(self.decode_error("empty canonical binder list"));
        }
        self.ensure_list_len(len, "binder list")?;
        let mut binders = Vec::with_capacity(len);
        let span = Span::empty(FileId(0));
        for _ in 0..len {
            binders.push(crate::MachineBinder {
                name: self.identifier("binder name")?,
                ty: self.term_at_depth(depth)?,
                span,
            });
        }
        Ok(binders)
    }

    fn option_levels(&mut self, depth: usize) -> Result<Option<Vec<MachineLevel>>> {
        match self.byte()? {
            0x00 => Ok(None),
            0x01 => {
                let len = self.usize()?;
                if len == 0 {
                    return Err(self.decode_error("empty explicit universe argument list"));
                }
                self.ensure_list_len(len, "explicit universe argument list")?;
                let mut levels = Vec::with_capacity(len);
                for _ in 0..len {
                    levels.push(self.machine_level_at_depth(depth)?);
                }
                Ok(Some(levels))
            }
            _ => Err(self.decode_error("invalid optional level-list tag")),
        }
    }

    fn machine_level_at_depth(&mut self, depth: usize) -> Result<MachineLevel> {
        self.ensure_depth(depth)?;
        self.consume_node()?;
        let tag = self.byte()?;
        let span = Span::empty(FileId(0));
        match tag {
            0x00 => Ok(MachineLevel::Nat {
                value: self.uvar()?,
                span,
            }),
            0x01 => Ok(MachineLevel::Param {
                name: self.level_param_identifier()?,
                span,
            }),
            0x02 => Ok(MachineLevel::Succ {
                level: Box::new(self.machine_level_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x03 => Ok(MachineLevel::Max {
                lhs: Box::new(self.machine_level_at_depth(self.child_depth(depth)?)?),
                rhs: Box::new(self.machine_level_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            0x04 => Ok(MachineLevel::IMax {
                lhs: Box::new(self.machine_level_at_depth(self.child_depth(depth)?)?),
                rhs: Box::new(self.machine_level_at_depth(self.child_depth(depth)?)?),
                span,
            }),
            _ => Err(self.decode_error("unknown Machine Surface level canonical tag")),
        }
    }

    fn name(&mut self) -> Result<Vec<String>> {
        let len = self.usize()?;
        if len == 0 {
            return Err(self.decode_error("empty canonical name"));
        }
        self.ensure_list_len(len, "name component list")?;
        let mut parts = Vec::with_capacity(len);
        parts.push(self.identifier("name head component")?);
        for _ in 1..len {
            parts.push(self.dotted_name_component()?);
        }
        Ok(parts)
    }

    fn dotted_name_component(&mut self) -> Result<String> {
        let value = self.string()?;
        if !is_machine_identifier(&value) {
            return Err(self.decode_error("invalid canonical dotted name component"));
        }
        Ok(value)
    }

    fn identifier(&mut self, what: &'static str) -> Result<String> {
        let value = self.string()?;
        if !is_machine_identifier(&value) || is_reserved_spelling(&value) {
            return Err(self.decode_error(format!("invalid canonical {what}")));
        }
        Ok(value)
    }

    fn level_param_identifier(&mut self) -> Result<String> {
        let value = self.identifier("universe level parameter")?;
        if is_level_operator(&value) {
            return Err(self.decode_error("invalid canonical universe level parameter"));
        }
        Ok(value)
    }

    fn string(&mut self) -> Result<String> {
        let len = self.usize()?;
        if len > MAX_CANONICAL_STRING_LEN {
            return Err(self.decode_error("canonical string is too large"));
        }
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| self.decode_error("invalid UTF-8 string"))
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(self.uvar()?).map_err(|_| self.decode_error("length is too large"))
    }

    fn uvar(&mut self) -> Result<u64> {
        let start = self.offset;
        let mut value = 0u64;
        let mut shift = 0;
        loop {
            let byte = self.byte()?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                let mut canonical = Vec::new();
                encode_uvar_to(&mut canonical, value);
                if canonical != self.bytes[start..self.offset] {
                    return Err(self.decode_error("non-canonical unsigned integer"));
                }
                return Ok(value);
            }
            shift += 7;
            if shift >= 64 {
                return Err(self.decode_error("unsigned integer is too large"));
            }
        }
    }

    fn byte(&mut self) -> Result<u8> {
        let Some(byte) = self.bytes.get(self.offset).copied() else {
            return Err(self.decode_error("unexpected end of canonical bytes"));
        };
        self.offset += 1;
        Ok(byte)
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or_else(|| self.decode_error("length overflow"))?;
        if end > self.bytes.len() {
            return Err(self.decode_error("unexpected end of canonical bytes"));
        }
        let bytes = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(bytes)
    }

    fn consume_node(&mut self) -> Result<()> {
        self.remaining_nodes = self
            .remaining_nodes
            .checked_sub(1)
            .ok_or_else(|| self.decode_error("canonical term is too large"))?;
        Ok(())
    }

    fn ensure_depth(&self, depth: usize) -> Result<()> {
        if depth > MAX_CANONICAL_DEPTH {
            return Err(self.decode_error("canonical term nesting is too deep"));
        }
        Ok(())
    }

    fn child_depth(&self, depth: usize) -> Result<usize> {
        depth
            .checked_add(1)
            .ok_or_else(|| self.decode_error("canonical term nesting is too deep"))
    }

    fn ensure_list_len(&self, len: usize, what: &'static str) -> Result<()> {
        if len > MAX_CANONICAL_LIST_LEN {
            return Err(self.decode_error(format!("canonical {what} is too large")));
        }
        Ok(())
    }

    fn decode_error(&self, message: impl Into<String>) -> crate::MachineDiagnostic {
        crate::MachineDiagnostic::parse(Span::empty(FileId(0)), message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn canonical_bytes_with_term(body: impl FnOnce(&mut Vec<u8>)) -> Vec<u8> {
        let mut bytes = Vec::new();
        encode_string_to(&mut bytes, TERM_SOURCE_TAG);
        body(&mut bytes);
        bytes
    }

    fn encode_simple_ident(bytes: &mut Vec<u8>, name: &str) {
        bytes.push(0x00);
        encode_name_to(bytes, &[name.to_owned()]);
        bytes.push(0x00);
        bytes.push(0x00);
    }

    #[test]
    fn canonical_term_source_ignores_whitespace_and_spans() {
        let first = canonicalize_machine_term_source("@Eq.refl.{1} Nat n")
            .expect("term should canonicalize");
        let second = canonicalize_machine_term_source("  @Eq.refl.{1}\n Nat   n  ")
            .expect("term should canonicalize");

        assert_eq!(first.canonical_bytes, second.canonical_bytes);
        assert_eq!(first.canonical_hash, second.canonical_hash);
    }

    #[test]
    fn canonical_term_source_round_trips_through_ast() {
        let canonical = canonicalize_machine_term_source("@Eq.refl.{1} Nat n")
            .expect("term should canonicalize");
        let ast = decode_machine_term_source_canonical(&canonical.canonical_bytes)
            .expect("canonical bytes should decode");

        let mut bytes = Vec::new();
        encode_string_to(&mut bytes, TERM_SOURCE_TAG);
        encode_term_to(&mut bytes, &ast.term);
        assert_eq!(bytes, canonical.canonical_bytes);
    }

    #[test]
    fn canonical_term_source_fixture_for_ai_fast_path_is_stable() {
        let canonical = canonicalize_machine_term_source("@Eq.refl.{1} Nat n")
            .expect("term should canonicalize");
        let expected_bytes = vec![
            0x23, 0x6e, 0x70, 0x61, 0x2e, 0x66, 0x72, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x64, 0x2e,
            0x6d, 0x61, 0x63, 0x68, 0x69, 0x6e, 0x65, 0x2d, 0x74, 0x65, 0x72, 0x6d, 0x2d, 0x73,
            0x6f, 0x75, 0x72, 0x63, 0x65, 0x2e, 0x76, 0x31, 0x03, 0x03, 0x00, 0x02, 0x02, 0x45,
            0x71, 0x04, 0x72, 0x65, 0x66, 0x6c, 0x01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x01, 0x03,
            0x4e, 0x61, 0x74, 0x00, 0x00, 0x00, 0x01, 0x01, 0x6e, 0x00, 0x00,
        ];
        let expected_hash = [
            0x60, 0x8f, 0x3f, 0x0b, 0xa3, 0x6d, 0xbb, 0xaa, 0xd6, 0x8b, 0x50, 0x0a, 0xd8, 0x9e,
            0x90, 0x43, 0x18, 0x1a, 0xeb, 0x6c, 0x3d, 0xcf, 0xd9, 0x3e, 0xcc, 0xdb, 0x36, 0x8f,
            0x7d, 0x29, 0x89, 0xcf,
        ];

        assert_eq!(canonical.canonical_bytes, expected_bytes);
        assert_eq!(canonical.canonical_hash, expected_hash);
    }

    #[test]
    fn canonical_term_source_fixture_is_not_widened_by_human_features() {
        for source in [
            "def Test.x : Prop := Prop",
            "notation \"x\" => Nat.zero",
            "n + Nat.zero",
            "rw [h]",
            "simp-lite",
            "_",
            "?m",
        ] {
            assert!(
                canonicalize_machine_term_source(source).is_err(),
                "Human-only syntax must not become Machine canonical source: {source}"
            );
        }

        let canonical = canonicalize_machine_term_source("@Eq.refl.{1} Nat n")
            .expect("Machine Surface fixture should remain accepted");
        assert_eq!(
            canonical.canonical_hash,
            [
                0x60, 0x8f, 0x3f, 0x0b, 0xa3, 0x6d, 0xbb, 0xaa, 0xd6, 0x8b, 0x50, 0x0a, 0xd8, 0x9e,
                0x90, 0x43, 0x18, 0x1a, 0xeb, 0x6c, 0x3d, 0xcf, 0xd9, 0x3e, 0xcc, 0xdb, 0x36, 0x8f,
                0x7d, 0x29, 0x89, 0xcf,
            ]
        );
    }

    #[test]
    fn canonical_name_atom_layout_matches_spec_order() {
        let canonical =
            canonicalize_machine_term_source("@Eq.refl").expect("term should canonicalize");
        let expected = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_name_to(bytes, &["Eq".to_owned(), "refl".to_owned()]);
            bytes.push(0x01);
            bytes.push(0x00);
        });

        assert_eq!(canonical.canonical_bytes, expected);
    }

    #[test]
    fn canonical_term_source_keeps_prop_type_and_sort_distinct() {
        let prop = canonicalize_machine_term_source("Prop").expect("Prop should canonicalize");
        let sort_zero =
            canonicalize_machine_term_source("Sort 0").expect("Sort 0 should canonicalize");
        let ty = canonicalize_machine_term_source("Type").expect("Type should canonicalize");
        let sort_one =
            canonicalize_machine_term_source("Sort 1").expect("Sort 1 should canonicalize");

        assert_ne!(prop.canonical_bytes, sort_zero.canonical_bytes);
        assert_ne!(prop.canonical_hash, sort_zero.canonical_hash);
        assert_ne!(ty.canonical_bytes, sort_one.canonical_bytes);
        assert_ne!(ty.canonical_hash, sort_one.canonical_hash);
    }

    #[test]
    fn token_only_api_preserves_spelling_and_trivia() {
        let tokens = lex_machine_surface_tokens("Std.unsafe.Type -- doc\nnotation \"x\"")
            .expect("token-only lexing should preserve unsupported surface fragments");
        let got = tokens
            .iter()
            .map(|token| (token.kind.clone(), token.spelling.as_str()))
            .collect::<Vec<_>>();

        assert_eq!(
            got,
            vec![
                (MachineSurfaceTokenKind::IdentLike, "Std"),
                (MachineSurfaceTokenKind::Dot, "."),
                (MachineSurfaceTokenKind::IdentLike, "unsafe"),
                (MachineSurfaceTokenKind::Dot, "."),
                (MachineSurfaceTokenKind::Reserved, "Type"),
                (MachineSurfaceTokenKind::Whitespace, " "),
                (MachineSurfaceTokenKind::Comment, "-- doc"),
                (MachineSurfaceTokenKind::Whitespace, "\n"),
                (MachineSurfaceTokenKind::Reserved, "notation"),
                (MachineSurfaceTokenKind::Whitespace, " "),
                (MachineSurfaceTokenKind::StringLiteral, "\"x\""),
            ]
        );
        assert_eq!(tokens[4].span, Span::new(FileId(0), 11, 15));
    }

    #[test]
    fn token_only_api_rejects_oversized_natural_like_parser_lexer() {
        let err = lex_machine_surface_tokens("18446744073709551616")
            .expect_err("oversized natural should be a lexical diagnostic");

        assert_eq!(err.kind, crate::MachineDiagnosticKind::ParseError);
    }

    #[test]
    fn canonical_decoder_allows_reserved_spellings_after_dot() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_name_to(
                bytes,
                &["M".to_owned(), "Type".to_owned(), "match".to_owned()],
            );
            bytes.push(0x00);
            bytes.push(0x00);
        });
        let ast = decode_machine_term_source_canonical(&bytes)
            .expect("reserved spellings after dot can be canonical name components");

        let MachineTerm::Ident { name, .. } = ast.term else {
            panic!("expected ident term");
        };
        assert_eq!(name.as_dotted(), "M.Type.match");
    }

    #[test]
    fn decoder_rejects_empty_canonical_name() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_uvar_to(bytes, 0);
            bytes.push(0x00);
            bytes.push(0x00);
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("empty names cannot be produced by the parser");
    }

    #[test]
    fn decoder_rejects_oversized_canonical_lists_before_allocation() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_uvar_to(bytes, MAX_CANONICAL_LIST_LEN as u64 + 1);
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("oversized canonical lists should be rejected before allocation");
    }

    #[test]
    fn decoder_rejects_empty_or_keyword_identifiers() {
        let empty_name_component = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_uvar_to(bytes, 1);
            encode_string_to(bytes, "");
            bytes.push(0x00);
            bytes.push(0x00);
        });
        decode_machine_term_source_canonical(&empty_name_component)
            .expect_err("empty name components cannot be produced by the parser");

        let keyword_name_component = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_uvar_to(bytes, 1);
            encode_string_to(bytes, "let");
            bytes.push(0x00);
            bytes.push(0x00);
        });
        decode_machine_term_source_canonical(&keyword_name_component)
            .expect_err("keyword name components cannot be produced by the parser");
    }

    #[test]
    fn decoder_rejects_resolved_local_term_tag() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x01);
            encode_string_to(bytes, "n");
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("resolved locals cannot be produced by the parser");
    }

    #[test]
    fn decoder_rejects_empty_binder_lists() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x04);
            encode_uvar_to(bytes, 0);
            bytes.push(0x02);
            bytes.push(0x00);
            encode_uvar_to(bytes, 0);
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("empty lambda binder lists cannot be produced by the parser");
    }

    #[test]
    fn decoder_rejects_empty_explicit_universe_args() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x00);
            encode_name_to(bytes, &["Nat".to_owned()]);
            bytes.push(0x00);
            bytes.push(0x01);
            encode_uvar_to(bytes, 0);
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("empty explicit universe args cannot be produced by the parser");
    }

    #[test]
    fn decoder_rejects_level_operator_as_level_param() {
        let bytes = canonical_bytes_with_term(|bytes| {
            bytes.push(0x02);
            bytes.push(0x01);
            encode_string_to(bytes, "succ");
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("level operators cannot decode as level parameters");
    }

    #[test]
    fn decoder_rejects_excessive_canonical_depth() {
        let bytes = canonical_bytes_with_term(|bytes| {
            for _ in 0..=MAX_CANONICAL_DEPTH {
                bytes.push(0x03);
                encode_simple_ident(bytes, "f");
            }
            encode_simple_ident(bytes, "x");
        });

        decode_machine_term_source_canonical(&bytes)
            .expect_err("deep canonical terms should be rejected before overflowing the stack");
    }

    #[test]
    fn canonicalizer_rejects_terms_deeper_than_decoder_limit() {
        let source = std::iter::repeat_n("f", MAX_CANONICAL_DEPTH + 3)
            .collect::<Vec<_>>()
            .join(" ");

        canonicalize_machine_term_source(&source)
            .expect_err("canonicalizer and decoder must share the same depth limit");
    }

    #[test]
    fn canonicalizer_rejects_oversized_canonical_lists_before_encoding() {
        let span = Span::empty(FileId(0));
        let parts =
            std::iter::repeat_n("M".to_owned(), MAX_CANONICAL_LIST_LEN + 1).collect::<Vec<_>>();
        let term = MachineTerm::Ident {
            name: crate::MachineName::new(parts, span),
            universe_args: None,
            explicit_mode: false,
            span,
        };

        validate_term_for_canonical_encoding(&term)
            .expect_err("canonicalizer should reject bytes the decoder would reject");
    }

    #[test]
    fn canonicalizer_rejects_terms_with_more_nodes_than_decoder_limit() {
        let span = Span::empty(FileId(0));
        let binders = std::iter::repeat_with(|| crate::MachineBinder {
            name: "x".to_owned(),
            ty: MachineTerm::Prop { span },
            span,
        })
        .take(MAX_CANONICAL_NODES)
        .collect::<Vec<_>>();
        let term = MachineTerm::Lam {
            binders,
            body: Box::new(MachineTerm::Prop { span }),
            span,
        };

        validate_term_for_canonical_encoding(&term)
            .expect_err("canonicalizer should enforce the decoder node budget");
    }

    #[test]
    fn canonicalizer_rejects_strings_larger_than_decoder_limit() {
        let span = Span::empty(FileId(0));
        let term = MachineTerm::Ident {
            name: crate::MachineName::new(vec!["x".repeat(MAX_CANONICAL_STRING_LEN + 1)], span),
            universe_args: None,
            explicit_mode: false,
            span,
        };

        validate_term_for_canonical_encoding(&term)
            .expect_err("canonicalizer should enforce the decoder string limit");
    }
}
