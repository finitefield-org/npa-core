use std::collections::BTreeMap;

use crate::{
    FileId, HumanAxiomDecl, HumanBinder, HumanBinderInfo, HumanClassDecl, HumanClassFieldDecl,
    HumanConstructorDecl, HumanDecl, HumanDeclValue, HumanDiagnostic, HumanDiagnosticKind,
    HumanDiagnosticPhase, HumanEquationDecl, HumanEquationRow, HumanExpr, HumanImplicitMode,
    HumanImportedSourceInterface, HumanInductiveDecl, HumanInstanceDecl, HumanInstanceFieldDecl,
    HumanItem, HumanLevel, HumanModule, HumanName, HumanNotationAssociativity, HumanNotationDecl,
    HumanNotationHead, HumanNotationKind, HumanPattern, HumanProofBlock, HumanResult,
    HumanRewriteDirection, HumanRewriteRuleSyntax, HumanSourceNotationMetadata, HumanTacticScript,
    HumanTacticSyntax, HumanTerminationAnnotation, HumanUniverseParam, Span,
};

pub fn parse_human_module(file_id: FileId, source: &str) -> HumanResult<HumanModule> {
    parse_human_module_with_source_interfaces(file_id, source, &[])
}

pub fn parse_human_module_with_source_interfaces(
    file_id: FileId,
    source: &str,
    imported_source_interfaces: &[HumanImportedSourceInterface],
) -> HumanResult<HumanModule> {
    let tokens = lex_human(file_id, source)
        .map_err(|diagnostic| diagnostic.with_default_phase(HumanDiagnosticPhase::Parser))?;
    Parser::new(tokens, source, imported_source_interfaces)
        .parse_module(file_id, source.len() as u32)
        .map_err(|diagnostic| diagnostic.with_default_phase(HumanDiagnosticPhase::Parser))
}

pub fn parse_human_term(file_id: FileId, source: &str) -> HumanResult<HumanExpr> {
    let tokens = lex_human(file_id, source)
        .map_err(|diagnostic| diagnostic.with_default_phase(HumanDiagnosticPhase::Parser))?;
    let mut parser = Parser::new(tokens, source, &[]);
    let term = parser
        .parse_term()
        .map_err(|diagnostic| diagnostic.with_default_phase(HumanDiagnosticPhase::Parser))?;
    if !parser.at_eof() {
        return Err(HumanDiagnostic::parse(
            parser.peek_span(),
            "expected end of Human Surface term",
        )
        .with_phase(HumanDiagnosticPhase::Parser));
    }
    Ok(term)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Token {
    kind: TokenKind,
    span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Ident(String),
    Number(u64),
    StringLiteral(String),
    Operator(String),
    Import,
    Open,
    Namespace,
    End,
    Def,
    Theorem,
    Axiom,
    Inductive,
    Class,
    Instance,
    Where,
    TerminationBy,
    Notation,
    Prefix,
    Postfix,
    Infix,
    Infixl,
    Infixr,
    By,
    Intro,
    Exact,
    Apply,
    Rw,
    SimpLite,
    Smt,
    Induction,
    Fun,
    Forall,
    Let,
    In,
    Prop,
    Type,
    Sort,
    Succ,
    Max,
    IMax,
    Dot,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    LParen,
    RParen,
    Colon,
    ColonEq,
    Comma,
    FatArrow,
    ThinArrow,
    At,
    Bar,
    Hole,
    NamedHole(String),
    Eof,
}

fn lex_human(file_id: FileId, source: &str) -> HumanResult<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();

    while let Some((offset, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }

        let start = offset as u32;
        let token = match ch {
            '-' if matches!(chars.peek(), Some((_, '-'))) => {
                skip_line_comment(&mut chars);
                continue;
            }
            '-' if matches!(chars.peek(), Some((_, '>'))) => {
                let (next_offset, _) = chars.next().expect("peeked thin arrow");
                Token {
                    kind: TokenKind::ThinArrow,
                    span: Span::new(file_id, start, (next_offset + 1) as u32),
                }
            }
            '→' => Token {
                kind: TokenKind::ThinArrow,
                span: Span::new(file_id, start, start + ch.len_utf8() as u32),
            },
            '"' => lex_string(file_id, source, start, &mut chars)?,
            '.' => Token {
                kind: TokenKind::Dot,
                span: Span::new(file_id, start, start + 1),
            },
            '[' => Token {
                kind: TokenKind::LBracket,
                span: Span::new(file_id, start, start + 1),
            },
            ']' => Token {
                kind: TokenKind::RBracket,
                span: Span::new(file_id, start, start + 1),
            },
            '{' => Token {
                kind: TokenKind::LBrace,
                span: Span::new(file_id, start, start + 1),
            },
            '}' => Token {
                kind: TokenKind::RBrace,
                span: Span::new(file_id, start, start + 1),
            },
            '(' => Token {
                kind: TokenKind::LParen,
                span: Span::new(file_id, start, start + 1),
            },
            ')' => Token {
                kind: TokenKind::RParen,
                span: Span::new(file_id, start, start + 1),
            },
            ',' => Token {
                kind: TokenKind::Comma,
                span: Span::new(file_id, start, start + 1),
            },
            '@' => Token {
                kind: TokenKind::At,
                span: Span::new(file_id, start, start + 1),
            },
            '|' => Token {
                kind: TokenKind::Bar,
                span: Span::new(file_id, start, start + 1),
            },
            ':' => {
                if let Some((next_offset, '=')) = chars.peek().copied() {
                    chars.next();
                    Token {
                        kind: TokenKind::ColonEq,
                        span: Span::new(file_id, start, (next_offset + 1) as u32),
                    }
                } else {
                    Token {
                        kind: TokenKind::Colon,
                        span: Span::new(file_id, start, start + 1),
                    }
                }
            }
            '=' if matches!(chars.peek(), Some((_, '>'))) => {
                let (next_offset, _) = chars.next().expect("peeked fat arrow");
                Token {
                    kind: TokenKind::FatArrow,
                    span: Span::new(file_id, start, (next_offset + 1) as u32),
                }
            }
            '_' => Token {
                kind: TokenKind::Hole,
                span: Span::new(file_id, start, start + 1),
            },
            '?' => lex_named_hole(file_id, source, start, &mut chars),
            '0'..='9' => lex_number(file_id, source, start, offset, ch, &mut chars)?,
            ch if is_ident_start(ch) => lex_ident(file_id, source, start, offset, &mut chars),
            ch if is_operator_char(ch) => {
                lex_operator(file_id, source, start, offset, ch, &mut chars)
            }
            ch => {
                return Err(HumanDiagnostic::unsupported_syntax(
                    Span::new(file_id, start, start + ch.len_utf8() as u32),
                    "character is not part of Human Surface syntax",
                ));
            }
        };

        tokens.push(token);
    }

    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span::new(file_id, source.len() as u32, source.len() as u32),
    });

    Ok(tokens)
}

fn skip_line_comment(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) {
    chars.next().expect("peeked second comment marker");
    while let Some((_, next)) = chars.peek().copied() {
        if next == '\n' {
            break;
        }
        chars.next();
    }
}

fn lex_string(
    file_id: FileId,
    source: &str,
    start: u32,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> HumanResult<Token> {
    let mut escaped = false;
    let mut value = String::new();

    for (offset, ch) in chars.by_ref() {
        if escaped {
            value.push(ch);
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == '"' {
            return Ok(Token {
                kind: TokenKind::StringLiteral(value),
                span: Span::new(file_id, start, (offset + ch.len_utf8()) as u32),
            });
        }
        value.push(ch);
    }

    Err(HumanDiagnostic::parse(
        Span::new(file_id, start, source.len() as u32),
        "unterminated string literal",
    ))
}

fn lex_number(
    file_id: FileId,
    source: &str,
    start: u32,
    first_offset: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> HumanResult<Token> {
    let mut end = first_offset + first.len_utf8();

    while let Some((offset, ch)) = chars.peek().copied() {
        if !ch.is_ascii_digit() {
            break;
        }

        chars.next();
        end = offset + ch.len_utf8();
    }

    let span = Span::new(file_id, start, end as u32);
    let value = source[start as usize..end]
        .parse::<u64>()
        .map_err(|_| HumanDiagnostic::parse(span, "numeric literal is too large"))?;

    Ok(Token {
        kind: TokenKind::Number(value),
        span,
    })
}

fn lex_ident(
    file_id: FileId,
    source: &str,
    start: u32,
    first_offset: usize,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Token {
    let mut end = first_offset;

    while let Some((offset, ch)) = chars.peek().copied() {
        if !is_ident_continue(ch) {
            break;
        }

        chars.next();
        end = offset;
    }

    let mut end = end
        + source[end..]
            .chars()
            .next()
            .expect("identifier has a character")
            .len_utf8();
    if &source[start as usize..end] == "simp" {
        let suffix = "-lite";
        let suffix_end = end + suffix.len();
        let suffix_is_complete = source
            .get(end..)
            .is_some_and(|remaining| remaining.starts_with(suffix))
            && source
                .get(suffix_end..)
                .and_then(|remaining| remaining.chars().next())
                .is_none_or(|next| !is_ident_continue(next));
        if suffix_is_complete {
            while matches!(chars.peek(), Some((offset, _)) if *offset < suffix_end) {
                chars.next();
            }
            end = suffix_end;
        }
    }

    let text = &source[start as usize..end];
    let kind = match text {
        "import" => TokenKind::Import,
        "open" => TokenKind::Open,
        "namespace" => TokenKind::Namespace,
        "end" => TokenKind::End,
        "def" => TokenKind::Def,
        "theorem" => TokenKind::Theorem,
        "axiom" => TokenKind::Axiom,
        "inductive" => TokenKind::Inductive,
        "class" => TokenKind::Class,
        "instance" => TokenKind::Instance,
        "where" => TokenKind::Where,
        "termination_by" => TokenKind::TerminationBy,
        "notation" => TokenKind::Notation,
        "prefix" => TokenKind::Prefix,
        "postfix" => TokenKind::Postfix,
        "infix" => TokenKind::Infix,
        "infixl" => TokenKind::Infixl,
        "infixr" => TokenKind::Infixr,
        "by" => TokenKind::By,
        "intro" => TokenKind::Intro,
        "exact" => TokenKind::Exact,
        "apply" => TokenKind::Apply,
        "rw" => TokenKind::Rw,
        "simp-lite" => TokenKind::SimpLite,
        "smt" => TokenKind::Smt,
        "induction" => TokenKind::Induction,
        "fun" => TokenKind::Fun,
        "forall" => TokenKind::Forall,
        "let" => TokenKind::Let,
        "in" => TokenKind::In,
        "Prop" => TokenKind::Prop,
        "Type" => TokenKind::Type,
        "Sort" => TokenKind::Sort,
        "succ" => TokenKind::Succ,
        "max" => TokenKind::Max,
        "imax" => TokenKind::IMax,
        _ => TokenKind::Ident(text.to_owned()),
    };

    Token {
        kind,
        span: Span::new(file_id, start, end as u32),
    }
}

fn lex_named_hole(
    file_id: FileId,
    source: &str,
    start: u32,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Token {
    let Some((first_offset, first)) = chars.peek().copied() else {
        return Token {
            kind: TokenKind::Hole,
            span: Span::new(file_id, start, start + 1),
        };
    };

    if !is_ident_start(first) {
        return Token {
            kind: TokenKind::Hole,
            span: Span::new(file_id, start, start + 1),
        };
    }

    chars.next();
    let mut end = first_offset + first.len_utf8();

    while let Some((offset, ch)) = chars.peek().copied() {
        if !is_ident_continue(ch) {
            break;
        }

        chars.next();
        end = offset + ch.len_utf8();
    }

    Token {
        kind: TokenKind::NamedHole(source[(start as usize + 1)..end].to_owned()),
        span: Span::new(file_id, start, end as u32),
    }
}

fn lex_operator(
    file_id: FileId,
    source: &str,
    start: u32,
    first_offset: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Token {
    let mut end = first_offset + first.len_utf8();

    while let Some((offset, ch)) = chars.peek().copied() {
        if !is_operator_char(ch) {
            break;
        }

        chars.next();
        end = offset + ch.len_utf8();
    }

    Token {
        kind: TokenKind::Operator(source[start as usize..end].to_owned()),
        span: Span::new(file_id, start, end as u32),
    }
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '\''
}

fn is_operator_char(ch: char) -> bool {
    matches!(
        ch,
        '+' | '-' | '*' | '/' | '=' | '<' | '>' | '!' | '$' | '%' | '&' | '^' | '~' | '?' | ':'
    )
}

fn reserved_name_component_spelling(kind: &TokenKind) -> Option<&'static str> {
    Some(match kind {
        TokenKind::Import => "import",
        TokenKind::Open => "open",
        TokenKind::Namespace => "namespace",
        TokenKind::End => "end",
        TokenKind::Def => "def",
        TokenKind::Theorem => "theorem",
        TokenKind::Axiom => "axiom",
        TokenKind::Inductive => "inductive",
        TokenKind::Class => "class",
        TokenKind::Instance => "instance",
        TokenKind::Where => "where",
        TokenKind::TerminationBy => "termination_by",
        TokenKind::Notation => "notation",
        TokenKind::Prefix => "prefix",
        TokenKind::Postfix => "postfix",
        TokenKind::Infix => "infix",
        TokenKind::Infixl => "infixl",
        TokenKind::Infixr => "infixr",
        TokenKind::By => "by",
        TokenKind::Intro => "intro",
        TokenKind::Exact => "exact",
        TokenKind::Apply => "apply",
        TokenKind::Rw => "rw",
        TokenKind::SimpLite => "simp-lite",
        TokenKind::Smt => "smt",
        TokenKind::Induction => "induction",
        TokenKind::Fun => "fun",
        TokenKind::Forall => "forall",
        TokenKind::Let => "let",
        TokenKind::In => "in",
        TokenKind::Prop => "Prop",
        TokenKind::Type => "Type",
        TokenKind::Sort => "Sort",
        TokenKind::Succ => "succ",
        TokenKind::Max => "max",
        TokenKind::IMax => "imax",
        _ => return None,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParserNotationEntry {
    token: String,
    kind: HumanNotationKind,
    precedence: u16,
    associativity: HumanNotationAssociativity,
    namespace: Vec<String>,
    span: Span,
}

#[derive(Clone, Debug, Default)]
struct ParserNotationScope {
    entries: Vec<ParserNotationEntry>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParserNotationFixity {
    Prefix,
    Postfix,
    Infix,
}

fn notation_fixity(kind: HumanNotationKind) -> Option<ParserNotationFixity> {
    match kind {
        HumanNotationKind::Notation => None,
        HumanNotationKind::Prefix => Some(ParserNotationFixity::Prefix),
        HumanNotationKind::Postfix => Some(ParserNotationFixity::Postfix),
        HumanNotationKind::Infix | HumanNotationKind::Infixl | HumanNotationKind::Infixr => {
            Some(ParserNotationFixity::Infix)
        }
    }
}

fn notation_associativity(kind: HumanNotationKind) -> HumanNotationAssociativity {
    match kind {
        HumanNotationKind::Infixl => HumanNotationAssociativity::Left,
        HumanNotationKind::Infixr => HumanNotationAssociativity::Right,
        HumanNotationKind::Notation
        | HumanNotationKind::Prefix
        | HumanNotationKind::Postfix
        | HumanNotationKind::Infix => HumanNotationAssociativity::NonAssoc,
    }
}

fn name_looks_like_constructor_pattern(name: &HumanName) -> bool {
    name.parts.len() > 1
        || name
            .parts
            .last()
            .and_then(|part| part.chars().next())
            .is_some_and(|ch| ch.is_ascii_uppercase())
}

fn notation_head(entry: &ParserNotationEntry, span: Span) -> HumanNotationHead {
    HumanNotationHead {
        token: entry.token.clone(),
        kind: entry.kind,
        precedence: entry.precedence,
        associativity: entry.associativity,
        span,
    }
}

fn parser_notation_entry_from_metadata(
    metadata: &HumanSourceNotationMetadata,
) -> ParserNotationEntry {
    ParserNotationEntry {
        token: metadata.token.clone(),
        kind: metadata.kind,
        precedence: metadata.precedence,
        associativity: metadata.associativity,
        namespace: metadata.namespace.clone(),
        span: metadata.span,
    }
}

fn notation_entry_sort_key(entry: &ParserNotationEntry) -> (String, u8, u16, u8, Vec<String>) {
    (
        entry.token.clone(),
        notation_kind_sort_key(entry.kind),
        entry.precedence,
        notation_associativity_sort_key(entry.associativity),
        entry.namespace.clone(),
    )
}

fn notation_kind_sort_key(kind: HumanNotationKind) -> u8 {
    match kind {
        HumanNotationKind::Notation => 0,
        HumanNotationKind::Prefix => 1,
        HumanNotationKind::Postfix => 2,
        HumanNotationKind::Infix => 3,
        HumanNotationKind::Infixl => 4,
        HumanNotationKind::Infixr => 5,
    }
}

fn notation_associativity_sort_key(associativity: HumanNotationAssociativity) -> u8 {
    match associativity {
        HumanNotationAssociativity::NonAssoc => 0,
        HumanNotationAssociativity::Left => 1,
        HumanNotationAssociativity::Right => 2,
    }
}

fn validate_mvp_notation_token(token: &str, span: Span) -> HumanResult<()> {
    if token.is_empty() {
        return Err(HumanDiagnostic::parse(
            span,
            "notation token must not be empty",
        ));
    }
    if token.chars().any(char::is_whitespace) {
        return Err(HumanDiagnostic::parse(
            span,
            "multi-token notation is not part of the frontend MVP",
        ));
    }
    let is_nullary_numeric = matches!(token, "0" | "1");
    if reserved_notation_token(token)
        || (!is_nullary_numeric && !token.chars().all(is_operator_char))
    {
        return Err(HumanDiagnostic::parse(
            span,
            format!("notation token {token} is not a frontend MVP operator"),
        ));
    }
    Ok(())
}

fn is_nullary_numeric_notation_token(token: &str) -> bool {
    matches!(token, "0" | "1")
}

fn reserved_notation_token(token: &str) -> bool {
    matches!(
        token,
        "->" | "→"
            | ":"
            | ":="
            | "=>"
            | ","
            | "."
            | ".{"
            | "("
            | ")"
            | "["
            | "]"
            | "{"
            | "}"
            | "|"
            | "@"
            | "_"
            | "?"
    )
}

struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    source: &'a str,
    imported_source_interfaces: Vec<HumanImportedSourceInterface>,
    namespace_stack: Vec<HumanName>,
    notation_scopes: Vec<ParserNotationScope>,
    namespace_notations: BTreeMap<Vec<String>, Vec<ParserNotationEntry>>,
    field_boundary_depth: usize,
}

impl<'a> Parser<'a> {
    fn new(
        tokens: Vec<Token>,
        source: &'a str,
        imported_source_interfaces: &[HumanImportedSourceInterface],
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            source,
            imported_source_interfaces: imported_source_interfaces.to_vec(),
            namespace_stack: Vec::new(),
            notation_scopes: vec![ParserNotationScope::default()],
            namespace_notations: BTreeMap::new(),
            field_boundary_depth: 0,
        }
    }

    fn parse_module(&mut self, file_id: FileId, source_len: u32) -> HumanResult<HumanModule> {
        let mut items = Vec::new();
        let mut saw_non_import = false;

        while !self.at_eof() {
            let item = match self.peek_kind() {
                TokenKind::Import => {
                    if saw_non_import {
                        return Err(HumanDiagnostic::error(
                            HumanDiagnosticKind::ImportAfterItem,
                            self.peek_span(),
                            "import items must appear before other Human Surface items",
                        ));
                    }
                    let item = self.parse_import()?;
                    if let HumanItem::Import { module, span: _ } = &item {
                        self.activate_import_notations(module)?;
                    }
                    item
                }
                TokenKind::Open => {
                    saw_non_import = true;
                    let item = self.parse_open()?;
                    if let HumanItem::Open { namespace, .. } = &item {
                        self.activate_open_notations(namespace)?;
                    }
                    item
                }
                TokenKind::Namespace => {
                    saw_non_import = true;
                    let item = self.parse_namespace_start()?;
                    if let HumanItem::NamespaceStart { name, .. } = &item {
                        self.namespace_stack.push(name.clone());
                        self.notation_scopes.push(ParserNotationScope::default());
                    }
                    item
                }
                TokenKind::End => {
                    saw_non_import = true;
                    let item = self.parse_namespace_end()?;
                    self.namespace_stack.pop();
                    if self.notation_scopes.len() > 1 {
                        self.notation_scopes.pop();
                    }
                    item
                }
                TokenKind::Def => {
                    saw_non_import = true;
                    self.parse_def_item()?
                }
                TokenKind::Theorem => {
                    saw_non_import = true;
                    HumanItem::Theorem(self.parse_def_or_theorem_decl(false)?)
                }
                TokenKind::Axiom => {
                    saw_non_import = true;
                    HumanItem::Axiom(self.parse_axiom_decl()?)
                }
                TokenKind::Inductive => {
                    saw_non_import = true;
                    HumanItem::Inductive(self.parse_inductive_decl()?)
                }
                TokenKind::Class => {
                    saw_non_import = true;
                    HumanItem::Class(self.parse_class_decl()?)
                }
                TokenKind::Instance => {
                    saw_non_import = true;
                    HumanItem::Instance(self.parse_instance_decl()?)
                }
                TokenKind::Notation
                | TokenKind::Prefix
                | TokenKind::Postfix
                | TokenKind::Infix
                | TokenKind::Infixl
                | TokenKind::Infixr => {
                    saw_non_import = true;
                    let decl = self.parse_notation_decl()?;
                    self.register_notation_decl(&decl)?;
                    HumanItem::Notation(decl)
                }
                _ => {
                    return Err(HumanDiagnostic::parse(
                        self.peek_span(),
                        "expected Human Surface item",
                    ));
                }
            };

            items.push(item);
        }

        Ok(HumanModule {
            file_id,
            items,
            span: Span::new(file_id, 0, source_len),
        })
    }

    fn parse_import(&mut self) -> HumanResult<HumanItem> {
        let start = self.expect_import()?;
        let module = self.parse_name()?;
        let span = start.join(module.span);
        Ok(HumanItem::Import { module, span })
    }

    fn parse_open(&mut self) -> HumanResult<HumanItem> {
        let start = self.expect_open()?;
        let namespace = self.parse_name()?;
        let span = start.join(namespace.span);
        Ok(HumanItem::Open { namespace, span })
    }

    fn parse_namespace_start(&mut self) -> HumanResult<HumanItem> {
        let start = self.expect_namespace()?;
        let name = self.parse_name()?;
        let span = start.join(name.span);
        Ok(HumanItem::NamespaceStart { name, span })
    }

    fn parse_namespace_end(&mut self) -> HumanResult<HumanItem> {
        let start = self.expect_end()?;
        let name = if self.is_name_start() {
            Some(self.parse_name()?)
        } else {
            None
        };
        let span = name.as_ref().map_or(start, |name| start.join(name.span));
        Ok(HumanItem::NamespaceEnd { name, span })
    }

    fn parse_def_item(&mut self) -> HumanResult<HumanItem> {
        let start = self.expect_def()?;
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_colon()?;
        let result_type = self.parse_term()?;

        match self.peek_kind() {
            TokenKind::ColonEq => {
                self.expect_colon_eq()?;
                let value = self.parse_decl_value(false)?;
                let span = start.join(value.span());
                Ok(HumanItem::Def(HumanDecl {
                    name,
                    universe_params,
                    binders,
                    ty: result_type,
                    value,
                    span,
                }))
            }
            TokenKind::Where => {
                self.expect_where()?;
                let rows = self.parse_equation_rows()?;
                let termination = self.parse_optional_termination_annotation()?;
                let end = termination
                    .as_ref()
                    .map(|annotation| annotation.span)
                    .or_else(|| rows.last().map(HumanEquationRow::span))
                    .unwrap_or_else(|| result_type.span());
                Ok(HumanItem::EquationDef(HumanEquationDecl {
                    name,
                    universe_params,
                    binders,
                    result_type,
                    rows,
                    termination,
                    span: start.join(end),
                }))
            }
            _ => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected ':=' or 'where' after def type",
            )),
        }
    }

    fn parse_def_or_theorem_decl(&mut self, is_def: bool) -> HumanResult<HumanDecl> {
        let start = if is_def {
            self.expect_def()?
        } else {
            self.expect_theorem()?
        };
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_colon()?;
        let ty = self.parse_term()?;
        self.expect_colon_eq()?;
        let value = self.parse_decl_value(!is_def)?;
        let span = start.join(value.span());

        Ok(HumanDecl {
            name,
            universe_params,
            binders,
            ty,
            value,
            span,
        })
    }

    fn parse_equation_rows(&mut self) -> HumanResult<Vec<HumanEquationRow>> {
        let mut rows = Vec::new();

        while matches!(self.peek_kind(), TokenKind::Bar) {
            rows.push(self.parse_equation_row()?);
        }

        if rows.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected at least one equation row",
            ));
        }

        Ok(rows)
    }

    fn parse_equation_row(&mut self) -> HumanResult<HumanEquationRow> {
        let start = self.expect_bar()?;

        if self.at_explicit_default_case() {
            let (_, default_span) = self.expect_ident("expected default equation case")?;
            self.expect_fat_arrow()?;
            let value = self.parse_term()?;
            return Ok(HumanEquationRow::Default {
                default_span,
                span: start.join(value.span()),
                value,
            });
        }

        let mut patterns = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::FatArrow | TokenKind::Eof) {
            self.reject_equation_guard_or_view_pattern()?;
            patterns.push(self.parse_pattern()?);
        }

        if patterns.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected equation pattern or default case",
            ));
        }

        self.expect_fat_arrow()?;
        let value = self.parse_term()?;
        Ok(HumanEquationRow::Patterns {
            patterns,
            span: start.join(value.span()),
            value,
        })
    }

    fn parse_optional_termination_annotation(
        &mut self,
    ) -> HumanResult<Option<HumanTerminationAnnotation>> {
        if !matches!(self.peek_kind(), TokenKind::TerminationBy) {
            return Ok(None);
        }

        let start = self.advance().span;
        self.reject_unsupported_termination_measure()?;
        let measure = self.parse_term()?;
        Ok(Some(HumanTerminationAnnotation {
            span: start.join(measure.span()),
            measure,
        }))
    }

    fn reject_unsupported_termination_measure(&self) -> HumanResult<()> {
        if let TokenKind::Ident(name) = self.peek_kind() {
            if matches!(
                name.as_str(),
                "lex" | "lexicographic" | "multiset" | "well_founded"
            ) {
                return Err(HumanDiagnostic::error(
                    HumanDiagnosticKind::TerminationMeasureNotNat,
                    self.peek_span(),
                    format!(
                        "unsupported termination measure form {name}; only Nat-valued measures are supported"
                    ),
                ));
            }
        }
        Ok(())
    }

    fn at_explicit_default_case(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Ident(name) if name == "default")
            && matches!(self.peek_next_kind(), Some(TokenKind::FatArrow))
    }

    fn reject_equation_guard_or_view_pattern(&self) -> HumanResult<()> {
        match self.peek_kind() {
            TokenKind::Ident(name) if name == "if" || name == "when" => Err(
                HumanDiagnostic::unsupported_equation_guard(self.peek_span()),
            ),
            TokenKind::ThinArrow => {
                Err(HumanDiagnostic::unsupported_view_pattern(self.peek_span()))
            }
            _ => Ok(()),
        }
    }

    fn parse_pattern(&mut self) -> HumanResult<HumanPattern> {
        let mut pattern = self.parse_pattern_atom()?;
        if matches!(self.peek_kind(), TokenKind::At) {
            let HumanPattern::Variable { name, span: start } = pattern else {
                return Err(HumanDiagnostic::unsupported_syntax(
                    pattern.span(),
                    "as-pattern binder must be a variable",
                ));
            };
            self.expect_at()?;
            let inner = self.parse_pattern()?;
            let span = start.join(inner.span());
            pattern = HumanPattern::AsPattern {
                name,
                pattern: Box::new(inner),
                span,
            };
        }

        Ok(pattern)
    }

    fn parse_pattern_atom(&mut self) -> HumanResult<HumanPattern> {
        match self.peek_kind() {
            TokenKind::Ident(_) => self.parse_name_pattern(),
            TokenKind::Hole => {
                let span = self.advance().span;
                Ok(HumanPattern::Wildcard { span })
            }
            TokenKind::NamedHole(_) => Err(HumanDiagnostic::error(
                HumanDiagnosticKind::UnsolvedHole,
                self.peek_span(),
                "named holes are not supported in equation patterns",
            )),
            TokenKind::Number(value) => {
                let value = *value;
                let span = self.advance().span;
                Ok(HumanPattern::Literal { value, span })
            }
            TokenKind::Dot => {
                let span = self.advance().span;
                Ok(HumanPattern::Impossible { span })
            }
            TokenKind::LParen => {
                self.expect_lparen()?;
                let pattern = self.parse_pattern()?;
                self.expect_rparen()?;
                Ok(pattern)
            }
            _ => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected equation pattern",
            )),
        }
    }

    fn parse_name_pattern(&mut self) -> HumanResult<HumanPattern> {
        let name = self.parse_name()?;
        if !name_looks_like_constructor_pattern(&name) {
            return Ok(HumanPattern::Variable {
                span: name.span,
                name,
            });
        }

        let mut args = Vec::new();
        while self.is_pattern_atom_start() {
            self.reject_equation_guard_or_view_pattern()?;
            args.push(self.parse_pattern_atom()?);
        }

        let span = args
            .last()
            .map(|arg| name.span.join(arg.span()))
            .unwrap_or(name.span);
        Ok(HumanPattern::Constructor { name, args, span })
    }

    fn parse_decl_value(&mut self, allow_proof_block: bool) -> HumanResult<HumanDeclValue> {
        if allow_proof_block && matches!(self.peek_kind(), TokenKind::By) {
            Ok(HumanDeclValue::ProofBlock(self.parse_proof_block()?))
        } else {
            Ok(HumanDeclValue::Term(self.parse_term()?))
        }
    }

    fn parse_proof_block(&mut self) -> HumanResult<HumanProofBlock> {
        let start = self.expect_by()?;
        let mut tactics = Vec::new();

        while !self.at_eof() && !self.at_top_level_item_start() {
            tactics.push(self.parse_tactic()?);
        }

        if tactics.is_empty() {
            return Err(
                HumanDiagnostic::parse(start, "expected Human tactic after by")
                    .with_phase(HumanDiagnosticPhase::TacticParse),
            );
        }

        let script_span = start.join(
            tactics
                .last()
                .expect("checked non-empty tactic script")
                .span(),
        );
        Ok(HumanProofBlock {
            script: HumanTacticScript {
                tactics,
                span: script_span,
            },
            span: script_span,
        })
    }

    fn parse_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let parsed =
            match self.peek_kind() {
                TokenKind::Intro => self.parse_intro_tactic(),
                TokenKind::Exact => self.parse_exact_tactic(),
                TokenKind::Apply => self.parse_apply_tactic(),
                TokenKind::Rw => self.parse_rw_tactic(),
                TokenKind::SimpLite => self.parse_simp_lite_tactic(),
                TokenKind::Smt => self.parse_smt_tactic(),
                TokenKind::Induction => self.parse_induction_tactic(),
                TokenKind::Ident(name) if name == "finite_decide" => self
                    .parse_solver_tactic("finite_decide", |span| HumanTacticSyntax::FiniteDecide {
                        span,
                    }),
                TokenKind::Ident(name) if name == "omega" => {
                    self.parse_solver_tactic("omega", |span| HumanTacticSyntax::Omega { span })
                }
                TokenKind::Ident(name) if name == "ring_nf" => {
                    self.parse_solver_tactic("ring_nf", |span| HumanTacticSyntax::RingNf { span })
                }
                TokenKind::Ident(name) if name == "bitblast" => self
                    .parse_solver_tactic("bitblast", |span| HumanTacticSyntax::Bitblast { span }),
                TokenKind::Ident(name) if name == "case" => Err(
                    HumanDiagnostic::unsupported_tactic(self.peek_span(), "case"),
                ),
                TokenKind::Ident(name) => Err(HumanDiagnostic::unsupported_tactic(
                    self.peek_span(),
                    name.clone(),
                )),
                _ => Err(HumanDiagnostic::unsupported_tactic(
                    self.peek_span(),
                    "unexpected token in Human tactic script",
                )),
            };
        parsed
            .map_err(|diagnostic| diagnostic.with_default_phase(HumanDiagnosticPhase::TacticParse))
    }

    fn parse_intro_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_intro()?;
        let (name, name_span) = self.expect_ident("expected intro binder name")?;
        let name = HumanName::new(vec![name], name_span);
        let span = start.join(name.span);
        Ok(HumanTacticSyntax::Intro { name, span })
    }

    fn parse_exact_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_exact()?;
        let term = self.parse_term()?;
        let span = start.join(term.span());
        Ok(HumanTacticSyntax::Exact { term, span })
    }

    fn parse_apply_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_apply()?;
        let term = self.parse_term()?;
        let span = start.join(term.span());
        Ok(HumanTacticSyntax::Apply { term, span })
    }

    fn parse_rw_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_rw()?;
        self.expect_lbracket()?;
        if matches!(self.peek_kind(), TokenKind::RBracket) {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected rw rewrite rule",
            ));
        }

        let mut rules = Vec::new();
        loop {
            rules.push(self.parse_rw_rule()?);
            if matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                continue;
            }
            break;
        }

        let end = self.expect_rbracket()?;
        Ok(HumanTacticSyntax::Rewrite {
            rules,
            span: start.join(end),
        })
    }

    fn parse_rw_rule(&mut self) -> HumanResult<HumanRewriteRuleSyntax> {
        let (direction, direction_span) = match self.peek_kind() {
            TokenKind::Operator(token) if token == "<-" => {
                (HumanRewriteDirection::Backward, Some(self.advance().span))
            }
            _ => (HumanRewriteDirection::Forward, None),
        };
        let term = self.parse_term()?;
        let span = direction_span.map_or_else(|| term.span(), |span| span.join(term.span()));

        Ok(HumanRewriteRuleSyntax {
            direction,
            term,
            span,
        })
    }

    fn parse_simp_lite_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let span = self.expect_simp_lite()?;
        Ok(HumanTacticSyntax::SimpLite { span })
    }

    fn parse_smt_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_smt()?;
        if !matches!(self.peek_kind(), TokenKind::LBracket) {
            return Ok(HumanTacticSyntax::Smt {
                lemmas: Vec::new(),
                span: start,
            });
        }
        self.expect_lbracket()?;
        let mut lemmas = Vec::new();
        if !matches!(self.peek_kind(), TokenKind::RBracket) {
            loop {
                lemmas.push(self.parse_term()?);
                if matches!(self.peek_kind(), TokenKind::Comma) {
                    self.advance();
                    continue;
                }
                break;
            }
        }
        let end = self.expect_rbracket()?;
        Ok(HumanTacticSyntax::Smt {
            lemmas,
            span: start.join(end),
        })
    }

    fn parse_solver_tactic(
        &mut self,
        expected: &'static str,
        make: impl FnOnce(Span) -> HumanTacticSyntax,
    ) -> HumanResult<HumanTacticSyntax> {
        let (name, span) = self.expect_ident("expected solver tactic")?;
        if name != expected {
            return Err(HumanDiagnostic::parse(
                span,
                format!("expected solver tactic `{expected}`"),
            ));
        }
        Ok(make(span))
    }

    fn parse_induction_tactic(&mut self) -> HumanResult<HumanTacticSyntax> {
        let start = self.expect_induction()?;
        let (name, name_span) = self.expect_ident("expected induction target name")?;
        let name = HumanName::new(vec![name], name_span);
        let span = start.join(name.span);
        Ok(HumanTacticSyntax::Induction { name, span })
    }

    fn parse_axiom_decl(&mut self) -> HumanResult<HumanAxiomDecl> {
        let start = self.expect_axiom()?;
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_colon()?;
        let ty = self.parse_term()?;
        let span = start.join(ty.span());

        Ok(HumanAxiomDecl {
            name,
            universe_params,
            binders,
            ty,
            span,
        })
    }

    fn parse_inductive_decl(&mut self) -> HumanResult<HumanInductiveDecl> {
        let start = self.expect_inductive()?;
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_colon()?;
        let ty = self.parse_term()?;
        self.expect_where()?;
        let mut constructors = Vec::new();

        while matches!(self.peek_kind(), TokenKind::Bar) {
            constructors.push(self.parse_constructor_decl()?);
        }

        let span = constructors
            .last()
            .map(|constructor| start.join(constructor.span))
            .unwrap_or_else(|| start.join(ty.span()));
        Ok(HumanInductiveDecl {
            name,
            universe_params,
            binders,
            ty,
            constructors,
            span,
        })
    }

    fn parse_constructor_decl(&mut self) -> HumanResult<HumanConstructorDecl> {
        let start = self.expect_bar()?;
        let name = self.parse_declaration_name()?;
        self.expect_colon()?;
        let ty = self.parse_term()?;
        let span = start.join(ty.span());
        Ok(HumanConstructorDecl { name, ty, span })
    }

    fn parse_class_decl(&mut self) -> HumanResult<HumanClassDecl> {
        let start = self.expect_class()?;
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_where()?;
        let mut fields = Vec::new();

        while !self.at_eof() && !self.at_top_level_item_start() {
            fields.push(self.parse_class_field_decl()?);
        }

        if fields.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected at least one class field declaration",
            ));
        }

        let span = start.join(fields.last().expect("checked non-empty").span);
        Ok(HumanClassDecl {
            name,
            universe_params,
            binders,
            fields,
            span,
        })
    }

    fn parse_class_field_decl(&mut self) -> HumanResult<HumanClassFieldDecl> {
        if matches!(self.peek_kind(), TokenKind::Bar) {
            self.advance();
        }
        let name = self.parse_declaration_name()?;
        self.expect_colon()?;
        let ty = self.parse_field_term()?;
        let span = name.span.join(ty.span());
        Ok(HumanClassFieldDecl { name, ty, span })
    }

    fn parse_instance_decl(&mut self) -> HumanResult<HumanInstanceDecl> {
        let start = self.expect_instance()?;
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let binders = self.parse_decl_binders()?;
        self.expect_colon()?;
        let ty = self.parse_term()?;
        self.expect_where()?;
        let mut fields = Vec::new();

        while !self.at_eof() && !self.at_top_level_item_start() {
            fields.push(self.parse_instance_field_decl()?);
        }

        if fields.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected at least one instance field assignment",
            ));
        }

        let span = start.join(fields.last().expect("checked non-empty").span);
        Ok(HumanInstanceDecl {
            name,
            universe_params,
            binders,
            ty,
            fields,
            span,
        })
    }

    fn parse_instance_field_decl(&mut self) -> HumanResult<HumanInstanceFieldDecl> {
        if matches!(self.peek_kind(), TokenKind::Bar) {
            self.advance();
        }
        let name = self.parse_declaration_name()?;
        self.expect_colon_eq()?;
        let value = self.parse_field_term()?;
        let span = name.span.join(value.span());
        Ok(HumanInstanceFieldDecl { name, value, span })
    }

    fn parse_field_term(&mut self) -> HumanResult<HumanExpr> {
        self.field_boundary_depth += 1;
        let result = self.parse_term();
        self.field_boundary_depth -= 1;
        result
    }

    fn parse_notation_decl(&mut self) -> HumanResult<HumanNotationDecl> {
        let (kind, start, needs_precedence) = match self.peek_kind() {
            TokenKind::Notation => (HumanNotationKind::Notation, self.advance().span, false),
            TokenKind::Prefix => (HumanNotationKind::Prefix, self.advance().span, true),
            TokenKind::Postfix => (HumanNotationKind::Postfix, self.advance().span, true),
            TokenKind::Infix => (HumanNotationKind::Infix, self.advance().span, true),
            TokenKind::Infixl => (HumanNotationKind::Infixl, self.advance().span, true),
            TokenKind::Infixr => (HumanNotationKind::Infixr, self.advance().span, true),
            _ => {
                return Err(HumanDiagnostic::parse(
                    self.peek_span(),
                    "expected notation declaration",
                ));
            }
        };
        let precedence = if needs_precedence {
            self.expect_colon()?;
            self.expect_precedence()?
        } else {
            0
        };
        let (token, token_span) = self.expect_string_literal("expected notation string literal")?;
        self.expect_fat_arrow()?;
        let target = self.parse_name()?;
        let span = start.join(target.span);

        Ok(HumanNotationDecl {
            kind,
            precedence,
            token: token.trim().to_owned(),
            target,
            span: span.join(token_span),
        })
    }

    fn register_notation_decl(&mut self, decl: &HumanNotationDecl) -> HumanResult<()> {
        if decl.kind == HumanNotationKind::Notation
            && !is_nullary_numeric_notation_token(&decl.token)
        {
            return Ok(());
        }
        validate_mvp_notation_token(&decl.token, decl.span)?;
        let entry = ParserNotationEntry {
            token: decl.token.clone(),
            kind: decl.kind,
            precedence: decl.precedence,
            associativity: notation_associativity(decl.kind),
            namespace: self.current_namespace_parts(),
            span: decl.span,
        };
        if let Some(fixity) = notation_fixity(decl.kind) {
            self.ensure_notation_compatible(&entry, fixity)?;
        }
        self.current_notation_scope().entries.push(entry.clone());
        self.namespace_notations
            .entry(entry.namespace.clone())
            .or_default()
            .push(entry);
        Ok(())
    }

    fn activate_import_notations(&mut self, module: &HumanName) -> HumanResult<()> {
        let source_interface = self.imported_source_interface(module)?;
        let Some(source_interface) = source_interface else {
            return Ok(());
        };

        for metadata in &source_interface.notations {
            if metadata.kind == HumanNotationKind::Notation
                && !is_nullary_numeric_notation_token(&metadata.token)
            {
                continue;
            }
            validate_mvp_notation_token(&metadata.token, metadata.span)?;
            let entry = parser_notation_entry_from_metadata(metadata);
            self.namespace_notations
                .entry(entry.namespace.clone())
                .or_default()
                .push(entry.clone());
            if entry.namespace.is_empty() {
                if let Some(fixity) = notation_fixity(entry.kind) {
                    self.ensure_notation_compatible(&entry, fixity)?;
                }
                self.current_notation_scope().entries.push(entry);
            }
        }

        Ok(())
    }

    fn imported_source_interface(
        &self,
        module: &HumanName,
    ) -> HumanResult<Option<crate::HumanSourceInterface>> {
        let module_name = npa_cert::Name(module.parts.clone());
        let mut matches = self
            .imported_source_interfaces
            .iter()
            .filter(|import| import.module == module_name);
        let Some(first) = matches.next() else {
            return Ok(None);
        };

        if matches.any(|import| import.source_interface != first.source_interface) {
            return Err(HumanDiagnostic::error(
                HumanDiagnosticKind::ImportResolutionError,
                module.span,
                format!(
                    "import {} has multiple Human source interfaces",
                    module.as_dotted()
                ),
            ));
        }

        Ok(Some(first.source_interface.clone()))
    }

    fn ensure_notation_compatible(
        &self,
        entry: &ParserNotationEntry,
        fixity: ParserNotationFixity,
    ) -> HumanResult<()> {
        for existing in self.active_notation_entries(&entry.token, fixity) {
            if existing.precedence != entry.precedence
                || existing.associativity != entry.associativity
            {
                return Err(HumanDiagnostic::error(
                    HumanDiagnosticKind::NotationConflict,
                    entry.span,
                    format!("conflicting notation declaration for {}", entry.token),
                ));
            }
        }

        Ok(())
    }

    fn activate_open_notations(&mut self, namespace: &HumanName) -> HumanResult<()> {
        for candidate in self.open_notation_namespaces(namespace) {
            if let Some(entries) = self.namespace_notations.get(&candidate.0).cloned() {
                for entry in &entries {
                    if let Some(fixity) = notation_fixity(entry.kind) {
                        self.ensure_notation_compatible(entry, fixity)?;
                    }
                }
                self.current_notation_scope().entries.extend(entries);
                return Ok(());
            }
        }
        Ok(())
    }

    fn open_notation_namespaces(&self, namespace: &HumanName) -> Vec<npa_cert::Name> {
        let exact = npa_cert::Name(namespace.parts.clone());
        let mut current_relative = self.current_namespace_parts();
        current_relative.extend(namespace.parts.iter().cloned());
        if current_relative == exact.0 {
            vec![exact]
        } else {
            vec![exact, npa_cert::Name(current_relative)]
        }
    }

    fn active_notation_entry(
        &self,
        token: &str,
        fixity: ParserNotationFixity,
    ) -> Option<ParserNotationEntry> {
        self.active_notation_entries(token, fixity)
            .into_iter()
            .next()
    }

    fn active_notation_entries(
        &self,
        token: &str,
        fixity: ParserNotationFixity,
    ) -> Vec<ParserNotationEntry> {
        let mut entries: Vec<_> = self
            .notation_scopes
            .iter()
            .flat_map(|scope| scope.entries.iter())
            .filter(|entry| entry.token == token && notation_fixity(entry.kind) == Some(fixity))
            .cloned()
            .collect();
        entries.sort_by(|lhs, rhs| {
            notation_entry_sort_key(lhs)
                .cmp(&notation_entry_sort_key(rhs))
                .then_with(|| lhs.span.start.cmp(&rhs.span.start))
        });
        entries.dedup_by(|lhs, rhs| {
            lhs.token == rhs.token
                && lhs.kind == rhs.kind
                && lhs.precedence == rhs.precedence
                && lhs.associativity == rhs.associativity
                && lhs.namespace == rhs.namespace
        });
        entries
    }

    fn current_notation_scope(&mut self) -> &mut ParserNotationScope {
        if self.notation_scopes.is_empty() {
            self.notation_scopes.push(ParserNotationScope::default());
        }
        self.notation_scopes
            .last_mut()
            .expect("notation scope stack has a top-level frame")
    }

    fn current_namespace_parts(&self) -> Vec<String> {
        self.namespace_stack
            .iter()
            .flat_map(|name| name.parts.iter().cloned())
            .collect()
    }

    fn active_nullary_notation_entry(&self, token: &str) -> Option<ParserNotationEntry> {
        let mut entries: Vec<_> = self
            .notation_scopes
            .iter()
            .flat_map(|scope| scope.entries.iter())
            .filter(|entry| entry.token == token && entry.kind == HumanNotationKind::Notation)
            .cloned()
            .collect();
        entries.sort_by(|lhs, rhs| {
            notation_entry_sort_key(lhs)
                .cmp(&notation_entry_sort_key(rhs))
                .then_with(|| lhs.span.start.cmp(&rhs.span.start))
        });
        entries.dedup_by(|lhs, rhs| {
            lhs.token == rhs.token
                && lhs.kind == rhs.kind
                && lhs.precedence == rhs.precedence
                && lhs.associativity == rhs.associativity
                && lhs.namespace == rhs.namespace
        });
        entries.into_iter().next()
    }

    fn parse_decl_binders(&mut self) -> HumanResult<Vec<HumanBinder>> {
        let mut binders = Vec::new();
        while matches!(self.peek_kind(), TokenKind::LParen | TokenKind::LBrace) {
            binders.extend(self.parse_binder_group()?);
        }
        Ok(binders)
    }

    fn parse_binder_group(&mut self) -> HumanResult<Vec<HumanBinder>> {
        let (binder_info, start, end_kind) = match self.peek_kind() {
            TokenKind::LParen => (
                HumanBinderInfo::Explicit,
                self.expect_lparen()?,
                TokenKind::RParen,
            ),
            TokenKind::LBrace => (
                HumanBinderInfo::Implicit,
                self.expect_lbrace()?,
                TokenKind::RBrace,
            ),
            _ => {
                return Err(HumanDiagnostic::parse(
                    self.peek_span(),
                    "expected binder group",
                ));
            }
        };
        let mut names = Vec::new();
        while self.is_name_start() && !matches!(self.peek_kind(), TokenKind::Colon) {
            names.push(self.parse_name()?);
        }
        if names.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected binder name",
            ));
        }
        self.expect_colon()?;
        let ty = self.parse_term()?;
        let end = match end_kind {
            TokenKind::RParen => self.expect_rparen()?,
            TokenKind::RBrace => self.expect_rbrace()?,
            _ => unreachable!("binder groups only use parens or braces"),
        };
        let span = start.join(end);

        Ok(names
            .into_iter()
            .map(|name| HumanBinder::named(name, Some(ty.clone()), binder_info, span))
            .collect())
    }

    fn parse_term(&mut self) -> HumanResult<HumanExpr> {
        match self.peek_kind() {
            TokenKind::Fun => self.parse_lam(),
            TokenKind::Forall => self.parse_pi(),
            TokenKind::Let => self.parse_let(),
            _ => self.parse_arrow(),
        }
    }

    fn parse_lam(&mut self) -> HumanResult<HumanExpr> {
        let start = self.expect_fun()?;
        let mut binders = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::FatArrow | TokenKind::Eof) {
            if matches!(self.peek_kind(), TokenKind::LParen | TokenKind::LBrace) {
                binders.extend(self.parse_binder_group()?);
            } else if matches!(self.peek_kind(), TokenKind::Hole) {
                let span = self.advance().span;
                binders.push(HumanBinder::anonymous(None, span));
            } else if self.is_name_start() {
                let name = self.parse_name()?;
                let span = name.span;
                binders.push(HumanBinder::named(
                    name,
                    None,
                    HumanBinderInfo::Explicit,
                    span,
                ));
            } else {
                break;
            }
        }
        if binders.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected lambda binder",
            ));
        }
        self.expect_fat_arrow()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(HumanExpr::Lam {
            binders,
            body: Box::new(body),
            span,
        })
    }

    fn parse_pi(&mut self) -> HumanResult<HumanExpr> {
        let start = self.expect_forall()?;
        let mut binders = Vec::new();
        while matches!(self.peek_kind(), TokenKind::LParen | TokenKind::LBrace) {
            binders.extend(self.parse_binder_group()?);
        }
        if binders.is_empty() {
            return Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected Pi binder",
            ));
        }
        self.expect_comma()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(HumanExpr::Pi {
            binders,
            body: Box::new(body),
            span,
        })
    }

    fn parse_let(&mut self) -> HumanResult<HumanExpr> {
        let start = self.expect_let()?;
        let name = self.parse_name()?;
        let ty = if matches!(self.peek_kind(), TokenKind::Colon) {
            self.expect_colon()?;
            Some(Box::new(self.parse_term()?))
        } else {
            None
        };
        self.expect_colon_eq()?;
        let value = self.parse_term()?;
        self.expect_in()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(HumanExpr::Let {
            name,
            ty,
            value: Box::new(value),
            body: Box::new(body),
            span,
        })
    }

    fn parse_arrow(&mut self) -> HumanResult<HumanExpr> {
        let domain = self.parse_annotation()?;
        if !matches!(self.peek_kind(), TokenKind::ThinArrow) {
            return Ok(domain);
        }

        self.expect_thin_arrow()?;
        let codomain = self.parse_arrow()?;
        let span = domain.span().join(codomain.span());
        let binder = HumanBinder::anonymous(Some(domain), span);
        Ok(HumanExpr::Pi {
            binders: vec![binder],
            body: Box::new(codomain),
            span,
        })
    }

    fn parse_annotation(&mut self) -> HumanResult<HumanExpr> {
        let expr = self.parse_infix()?;

        if !matches!(self.peek_kind(), TokenKind::Colon) {
            return Ok(expr);
        }

        self.expect_colon()?;
        let ty = self.parse_term()?;
        let span = expr.span().join(ty.span());

        Ok(HumanExpr::Annot {
            expr: Box::new(expr),
            ty: Box::new(ty),
            span,
        })
    }

    fn parse_infix(&mut self) -> HumanResult<HumanExpr> {
        self.parse_notation_expr(0)
    }

    fn parse_notation_expr(&mut self, min_precedence: u16) -> HumanResult<HumanExpr> {
        let mut expr = if let TokenKind::Operator(token) = self.peek_kind().clone() {
            if let Some(entry) = self.active_notation_entry(&token, ParserNotationFixity::Prefix) {
                let op_span = self.advance().span;
                let rhs = self.parse_notation_expr(entry.precedence)?;
                let span = op_span.join(rhs.span());
                HumanExpr::NotationApp {
                    head: notation_head(&entry, op_span),
                    args: vec![rhs],
                    span,
                }
            } else {
                self.parse_app()?
            }
        } else {
            self.parse_app()?
        };
        let mut consumed_nonassoc_precedence = None;

        while let TokenKind::Operator(token) = self.peek_kind().clone() {
            if let Some(entry) = self.active_notation_entry(&token, ParserNotationFixity::Postfix) {
                if entry.precedence < min_precedence {
                    break;
                }
                let op_span = self.advance().span;
                let span = expr.span().join(op_span);
                expr = HumanExpr::NotationApp {
                    head: notation_head(&entry, op_span),
                    args: vec![expr],
                    span,
                };
                consumed_nonassoc_precedence = None;
                continue;
            }

            let Some(entry) = self.active_notation_entry(&token, ParserNotationFixity::Infix)
            else {
                return Err(HumanDiagnostic::parse(
                    self.peek_span(),
                    format!("unknown infix notation {token}"),
                ));
            };
            if entry.precedence < min_precedence {
                break;
            }
            if entry.associativity == HumanNotationAssociativity::NonAssoc
                && consumed_nonassoc_precedence == Some(entry.precedence)
            {
                return Err(HumanDiagnostic::parse(
                    self.peek_span(),
                    format!(
                        "non-associative infix notation {} cannot be chained",
                        entry.token
                    ),
                ));
            }
            let op_span = self.advance().span;
            let rhs_min_precedence = match entry.associativity {
                HumanNotationAssociativity::Right => entry.precedence,
                HumanNotationAssociativity::Left | HumanNotationAssociativity::NonAssoc => {
                    entry.precedence.saturating_add(1)
                }
            };
            let rhs = self.parse_notation_expr(rhs_min_precedence)?;
            let span = expr.span().join(rhs.span());
            expr = HumanExpr::NotationApp {
                head: notation_head(&entry, op_span),
                args: vec![expr, rhs],
                span,
            };
            consumed_nonassoc_precedence = (entry.associativity
                == HumanNotationAssociativity::NonAssoc)
                .then_some(entry.precedence);
        }

        Ok(expr)
    }

    fn parse_app(&mut self) -> HumanResult<HumanExpr> {
        let mut expr = self.parse_atom()?;

        while self.is_atom_start() {
            let arg = self.parse_atom()?;
            let span = expr.span().join(arg.span());
            expr = HumanExpr::App {
                func: Box::new(expr),
                arg: Box::new(arg),
                span,
            };
        }

        Ok(expr)
    }

    fn parse_atom(&mut self) -> HumanResult<HumanExpr> {
        match self.peek_kind() {
            TokenKind::Ident(_) => self.parse_ref(HumanImplicitMode::Insert),
            TokenKind::At => self.parse_explicit_ref(),
            TokenKind::Prop => self.parse_prop(),
            TokenKind::Type => self.parse_type(),
            TokenKind::Sort => self.parse_sort(),
            TokenKind::LParen => {
                self.expect_lparen()?;
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Ok(term)
            }
            TokenKind::Hole => {
                let span = self.advance().span;
                Ok(HumanExpr::Hole { name: None, span })
            }
            TokenKind::NamedHole(name) => {
                let name = name.clone();
                let span = self.advance().span;
                Ok(HumanExpr::Hole {
                    name: Some(HumanName::new(vec![name], span)),
                    span,
                })
            }
            TokenKind::Number(value) if matches!(value, 0 | 1) => {
                let token = value.to_string();
                let Some(entry) = self.active_nullary_notation_entry(&token) else {
                    return Err(HumanDiagnostic::parse(
                        self.peek_span(),
                        "numeric term literals are not Human Surface syntax",
                    ));
                };
                let span = self.advance().span;
                Ok(HumanExpr::NotationApp {
                    head: notation_head(&entry, span),
                    args: Vec::new(),
                    span,
                })
            }
            TokenKind::Number(_) => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "numeric term literals are not Human Surface syntax",
            )),
            _ => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected Human Surface term",
            )),
        }
    }

    fn parse_ref(&mut self, implicit_mode: HumanImplicitMode) -> HumanResult<HumanExpr> {
        let name = self.parse_name()?;
        let universe_args = self.parse_optional_universe_args()?;
        let span = match &universe_args {
            Some((_, args_span)) => name.span.join(*args_span),
            None => name.span,
        };

        Ok(HumanExpr::Ident {
            name,
            universe_args: universe_args.map(|(args, _)| args),
            implicit_mode,
            span,
        })
    }

    fn parse_explicit_ref(&mut self) -> HumanResult<HumanExpr> {
        let at = self.expect_at()?;
        let expr = self.parse_ref(HumanImplicitMode::Explicit)?;
        let span = at.join(expr.span());
        let HumanExpr::Ident {
            name,
            universe_args,
            implicit_mode,
            ..
        } = expr
        else {
            unreachable!("parse_ref returns an identifier");
        };

        Ok(HumanExpr::Ident {
            name,
            universe_args,
            implicit_mode,
            span,
        })
    }

    fn parse_prop(&mut self) -> HumanResult<HumanExpr> {
        let span = self.expect_prop()?;
        Ok(HumanExpr::Sort {
            level: HumanLevel::Nat { value: 0, span },
            span,
        })
    }

    fn parse_type(&mut self) -> HumanResult<HumanExpr> {
        let start = self.expect_type()?;
        let level = if self.is_type_level_start() {
            let level = self.parse_level()?;
            let span = start.join(level.span());
            HumanLevel::Succ {
                level: Box::new(level),
                span,
            }
        } else {
            HumanLevel::Nat {
                value: 1,
                span: start,
            }
        };
        let span = start.join(level.span());
        Ok(HumanExpr::Sort { level, span })
    }

    fn parse_sort(&mut self) -> HumanResult<HumanExpr> {
        let start = self.expect_sort()?;
        let level = self.parse_level()?;
        let span = start.join(level.span());
        Ok(HumanExpr::Sort { level, span })
    }

    fn parse_level(&mut self) -> HumanResult<HumanLevel> {
        match self.peek_kind() {
            TokenKind::Number(value) => {
                let value = *value;
                let span = self.advance().span;
                Ok(HumanLevel::Nat { value, span })
            }
            TokenKind::Succ => {
                let start = self.advance().span;
                let level = self.parse_level()?;
                let span = start.join(level.span());
                Ok(HumanLevel::Succ {
                    level: Box::new(level),
                    span,
                })
            }
            TokenKind::Max => {
                let start = self.advance().span;
                let lhs = self.parse_level()?;
                let rhs = self.parse_level()?;
                let span = start.join(rhs.span());
                Ok(HumanLevel::Max {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span,
                })
            }
            TokenKind::IMax => {
                let start = self.advance().span;
                let lhs = self.parse_level()?;
                let rhs = self.parse_level()?;
                let span = start.join(rhs.span());
                Ok(HumanLevel::IMax {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span,
                })
            }
            TokenKind::Ident(name) => {
                let name = name.clone();
                let span = self.advance().span;
                Ok(HumanLevel::Param { name, span })
            }
            _ => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected universe level",
            )),
        }
    }

    fn parse_name(&mut self) -> HumanResult<HumanName> {
        let (first, first_span) = self.expect_name_component("expected name")?;
        self.parse_name_tail(first, first_span)
    }

    fn parse_declaration_name(&mut self) -> HumanResult<HumanName> {
        let (first, first_span) = self.expect_dotted_name_component("expected declaration name")?;
        self.parse_name_tail(first, first_span)
    }

    fn parse_name_tail(&mut self, first: String, first_span: Span) -> HumanResult<HumanName> {
        let mut parts = vec![first];
        let mut span = first_span;

        while matches!(self.peek_kind(), TokenKind::Dot) {
            if matches!(self.peek_next_kind(), Some(TokenKind::LBrace)) {
                break;
            }

            self.expect_dot()?;
            let (part, part_span) =
                self.expect_dotted_name_component("expected identifier after '.'")?;
            parts.push(part);
            span = span.join(part_span);
        }

        Ok(HumanName::new(parts, span))
    }

    fn parse_optional_universe_params(&mut self) -> HumanResult<Vec<HumanUniverseParam>> {
        if !self.at_universe_brace() {
            return Ok(Vec::new());
        }

        self.expect_dot()?;
        self.expect_lbrace()?;
        let mut params = Vec::new();

        loop {
            let (name, span) = self.expect_ident("expected universe parameter name")?;
            params.push(HumanUniverseParam { name, span });

            if matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                continue;
            }

            break;
        }

        self.expect_rbrace()?;
        Ok(params)
    }

    fn parse_optional_universe_args(&mut self) -> HumanResult<Option<(Vec<HumanLevel>, Span)>> {
        if !self.at_universe_brace() {
            return Ok(None);
        }

        let start = self.expect_dot()?;
        self.expect_lbrace()?;
        let mut levels = Vec::new();

        loop {
            levels.push(self.parse_level()?);

            if matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                continue;
            }

            break;
        }

        let end = self.expect_rbrace()?;
        Ok(Some((levels, start.join(end))))
    }

    fn at_universe_brace(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Dot)
            && matches!(self.peek_next_kind(), Some(TokenKind::LBrace))
    }

    fn at_top_level_item_start(&self) -> bool {
        matches!(
            self.peek_kind(),
            TokenKind::Import
                | TokenKind::Open
                | TokenKind::Namespace
                | TokenKind::End
                | TokenKind::Def
                | TokenKind::Theorem
                | TokenKind::Axiom
                | TokenKind::Inductive
                | TokenKind::Class
                | TokenKind::Instance
                | TokenKind::Notation
                | TokenKind::Prefix
                | TokenKind::Postfix
                | TokenKind::Infix
                | TokenKind::Infixl
                | TokenKind::Infixr
        )
    }

    fn is_atom_start(&self) -> bool {
        if self.at_field_boundary() {
            return false;
        }
        matches!(
            self.peek_kind(),
            TokenKind::Ident(_)
                | TokenKind::At
                | TokenKind::Prop
                | TokenKind::Type
                | TokenKind::Sort
                | TokenKind::LParen
                | TokenKind::Hole
                | TokenKind::NamedHole(_)
                | TokenKind::Number(_)
        )
    }

    fn is_pattern_atom_start(&self) -> bool {
        matches!(
            self.peek_kind(),
            TokenKind::Ident(_)
                | TokenKind::Hole
                | TokenKind::NamedHole(_)
                | TokenKind::Number(_)
                | TokenKind::Dot
                | TokenKind::LParen
        )
    }

    fn at_field_boundary(&self) -> bool {
        if self.field_boundary_depth == 0 || self.pos == 0 {
            return false;
        }
        if !matches!(
            self.peek_kind(),
            TokenKind::Ident(_) | TokenKind::Bar | TokenKind::Class | TokenKind::Instance
        ) {
            return false;
        }
        if matches!(self.peek_kind(), TokenKind::Ident(_))
            && !matches!(
                self.peek_next_kind(),
                Some(TokenKind::Colon) | Some(TokenKind::ColonEq)
            )
        {
            return false;
        }
        self.has_newline_before_current()
    }

    fn has_newline_before_current(&self) -> bool {
        let Some(previous) = self.tokens.get(self.pos.saturating_sub(1)) else {
            return false;
        };
        let Some(current) = self.tokens.get(self.pos) else {
            return false;
        };
        let start = previous.span.end.0 as usize;
        let end = current.span.start.0 as usize;
        self.source
            .get(start..end)
            .is_some_and(|whitespace| whitespace.contains('\n') || whitespace.contains('\r'))
    }

    fn is_type_level_start(&self) -> bool {
        match self.peek_kind() {
            TokenKind::Number(_) => true,
            TokenKind::Succ | TokenKind::Max | TokenKind::IMax => true,
            TokenKind::Ident(_) => !matches!(
                self.peek_next_kind(),
                Some(TokenKind::Dot)
                    | Some(TokenKind::LBrace)
                    | Some(TokenKind::RParen)
                    | Some(TokenKind::RBrace)
                    | Some(TokenKind::Comma)
                    | Some(TokenKind::Colon)
                    | Some(TokenKind::ColonEq)
                    | Some(TokenKind::FatArrow)
                    | Some(TokenKind::ThinArrow)
                    | Some(TokenKind::Operator(_))
            ),
            _ => false,
        }
    }

    fn is_name_start(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Ident(_))
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Eof)
    }

    fn peek_kind(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn peek_next_kind(&self) -> Option<&TokenKind> {
        self.tokens.get(self.pos + 1).map(|token| &token.kind)
    }

    fn peek_span(&self) -> Span {
        self.tokens[self.pos].span
    }

    fn advance(&mut self) -> Token {
        let token = self.tokens[self.pos].clone();
        self.pos += 1;
        token
    }

    fn expect_name_component(&mut self, message: &str) -> HumanResult<(String, Span)> {
        match self.peek_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                let span = self.advance().span;
                Ok((name, span))
            }
            _ => Err(HumanDiagnostic::parse(self.peek_span(), message)),
        }
    }

    fn expect_dotted_name_component(&mut self, message: &str) -> HumanResult<(String, Span)> {
        let Some(spelling) = reserved_name_component_spelling(self.peek_kind()) else {
            return self.expect_name_component(message);
        };
        let span = self.advance().span;
        Ok((spelling.to_owned(), span))
    }

    fn expect_ident(&mut self, message: &str) -> HumanResult<(String, Span)> {
        self.expect_name_component(message)
    }

    fn expect_string_literal(&mut self, message: &str) -> HumanResult<(String, Span)> {
        match self.peek_kind() {
            TokenKind::StringLiteral(value) => {
                let value = value.clone();
                let span = self.advance().span;
                Ok((value, span))
            }
            _ => Err(HumanDiagnostic::parse(self.peek_span(), message)),
        }
    }

    fn expect_precedence(&mut self) -> HumanResult<u16> {
        match self.peek_kind() {
            TokenKind::Number(value) if *value <= u16::MAX as u64 => {
                let value = *value as u16;
                self.advance();
                Ok(value)
            }
            TokenKind::Number(_) => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "notation precedence is too large",
            )),
            _ => Err(HumanDiagnostic::parse(
                self.peek_span(),
                "expected notation precedence",
            )),
        }
    }

    fn expect_import(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Import), "expected import")
    }

    fn expect_open(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Open), "expected open")
    }

    fn expect_namespace(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::Namespace),
            "expected namespace",
        )
    }

    fn expect_end(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::End), "expected end")
    }

    fn expect_def(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Def), "expected def")
    }

    fn expect_theorem(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::Theorem),
            "expected theorem",
        )
    }

    fn expect_axiom(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Axiom), "expected axiom")
    }

    fn expect_inductive(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::Inductive),
            "expected inductive",
        )
    }

    fn expect_class(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Class), "expected class")
    }

    fn expect_instance(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::Instance),
            "expected instance",
        )
    }

    fn expect_by(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::By), "expected by")
    }

    fn expect_intro(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Intro), "expected intro")
    }

    fn expect_exact(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Exact), "expected exact")
    }

    fn expect_apply(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Apply), "expected apply")
    }

    fn expect_rw(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Rw), "expected rw")
    }

    fn expect_simp_lite(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::SimpLite),
            "expected simp-lite",
        )
    }

    fn expect_smt(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Smt), "expected smt")
    }

    fn expect_induction(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::Induction),
            "expected induction",
        )
    }

    fn expect_fun(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Fun), "expected fun")
    }

    fn expect_forall(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Forall), "expected forall")
    }

    fn expect_let(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Let), "expected let")
    }

    fn expect_where(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Where), "expected where")
    }

    fn expect_dot(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Dot), "expected '.'")
    }

    fn expect_lbracket(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::LBracket), "expected '['")
    }

    fn expect_rbracket(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::RBracket), "expected ']'")
    }

    fn expect_lbrace(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::LBrace), "expected '{'")
    }

    fn expect_rbrace(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::RBrace), "expected '}'")
    }

    fn expect_lparen(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::LParen), "expected '('")
    }

    fn expect_rparen(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::RParen), "expected ')'")
    }

    fn expect_colon(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Colon), "expected ':'")
    }

    fn expect_colon_eq(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::ColonEq), "expected ':='")
    }

    fn expect_comma(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Comma), "expected ','")
    }

    fn expect_fat_arrow(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::FatArrow), "expected '=>'")
    }

    fn expect_thin_arrow(&mut self) -> HumanResult<Span> {
        self.expect_simple(
            |kind| matches!(kind, TokenKind::ThinArrow),
            "expected '->' or '→'",
        )
    }

    fn expect_at(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::At), "expected '@'")
    }

    fn expect_bar(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Bar), "expected '|'")
    }

    fn expect_prop(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Prop), "expected Prop")
    }

    fn expect_type(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Type), "expected Type")
    }

    fn expect_sort(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::Sort), "expected Sort")
    }

    fn expect_in(&mut self) -> HumanResult<Span> {
        self.expect_simple(|kind| matches!(kind, TokenKind::In), "expected in")
    }

    fn expect_simple(
        &mut self,
        matches_expected: impl FnOnce(&TokenKind) -> bool,
        message: &str,
    ) -> HumanResult<Span> {
        if matches_expected(self.peek_kind()) {
            Ok(self.advance().span)
        } else {
            Err(HumanDiagnostic::parse(self.peek_span(), message))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HumanBinderKind, HumanTacticKind};

    fn parse_module(source: &str) -> HumanModule {
        parse_human_module(FileId(0), source).expect("Human source should parse")
    }

    fn parse_term(source: &str) -> HumanExpr {
        parse_human_term(FileId(0), source).expect("Human term should parse")
    }

    fn parse_err(source: &str) -> HumanDiagnosticKind {
        parse_human_module(FileId(0), source)
            .expect_err("Human source should be rejected")
            .kind
    }

    fn parse_diagnostic(source: &str) -> HumanDiagnostic {
        parse_human_module(FileId(0), source).expect_err("Human source should be rejected")
    }

    #[test]
    fn parses_empty_human_module() {
        let module = parse_human_module(FileId(2), " \n\t ").expect("empty module should parse");

        assert_eq!(module.file_id, FileId(2));
        assert!(module.items.is_empty());
        assert_eq!(module.span, Span::new(FileId(2), 0, 4));
    }

    #[test]
    fn parses_import_open_namespace_and_end_items() {
        let module = parse_module(
            "import Std.Nat.Basic
open Std.Nat
namespace Demo
end Demo",
        );

        assert_eq!(module.items.len(), 4);
        assert!(matches!(module.items[0], HumanItem::Import { .. }));
        assert!(matches!(module.items[1], HumanItem::Open { .. }));
        assert!(matches!(module.items[2], HumanItem::NamespaceStart { .. }));
        assert!(matches!(module.items[3], HumanItem::NamespaceEnd { .. }));
    }

    #[test]
    fn rejects_import_after_non_import_item() {
        assert_eq!(
            parse_err("def x : Prop := Prop\nimport Std.Nat.Basic"),
            HumanDiagnosticKind::ImportAfterItem
        );
    }

    #[test]
    fn parses_explicit_and_implicit_def_declarations() {
        let module = parse_module("def id.{u} {A : Sort u} (x : A) : A := x");
        let HumanItem::Def(decl) = &module.items[0] else {
            panic!("expected def");
        };

        assert_eq!(decl.name.as_dotted(), "id");
        assert_eq!(decl.universe_params[0].name, "u");
        assert_eq!(decl.binders.len(), 2);
        assert_eq!(decl.binders[0].binder_info, HumanBinderInfo::Implicit);
        assert_eq!(decl.binders[1].binder_info, HumanBinderInfo::Explicit);
    }

    #[test]
    fn parses_mvp_equation_definition_rows_default_and_termination() {
        let module = parse_module(
            "\
def pred (n : Nat) : Nat where
| Nat.zero => Nat.zero
| Nat.succ k => k
| default => Nat.zero
termination_by n",
        );
        let HumanItem::EquationDef(decl) = &module.items[0] else {
            panic!("expected equation def");
        };

        assert_eq!(decl.name.as_dotted(), "pred");
        assert_eq!(decl.binders.len(), 1);
        assert_eq!(decl.rows.len(), 3);
        let HumanEquationRow::Patterns { patterns, .. } = &decl.rows[1] else {
            panic!("expected pattern row");
        };
        let HumanPattern::Constructor { name, args, .. } = &patterns[0] else {
            panic!("expected constructor pattern");
        };
        assert_eq!(name.as_dotted(), "Nat.succ");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], HumanPattern::Variable { .. }));
        assert!(matches!(decl.rows[2], HumanEquationRow::Default { .. }));
        assert!(decl.termination.is_some());
    }

    #[test]
    fn equation_parser_rejects_guards_views_bad_measures_and_pattern_holes() {
        let cases = [
            (
                "guard",
                "\
def bad (n : Nat) : Nat where
| Nat.succ k if p => k",
                HumanDiagnosticKind::UnsupportedEquationGuard,
            ),
            (
                "view",
                "\
def bad (n : Nat) : Nat where
| k -> Nat.zero => k",
                HumanDiagnosticKind::UnsupportedViewPattern,
            ),
            (
                "measure",
                "\
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
termination_by lex n",
                HumanDiagnosticKind::TerminationMeasureNotNat,
            ),
            (
                "multiset measure",
                "\
def bad (n : Nat) : Nat where
| Nat.zero => Nat.zero
termination_by multiset n",
                HumanDiagnosticKind::TerminationMeasureNotNat,
            ),
            (
                "pattern hole",
                "\
def bad (n : Nat) : Nat where
| ?m => Nat.zero",
                HumanDiagnosticKind::UnsolvedHole,
            ),
        ];

        for (label, source, expected) in cases {
            let diagnostic = parse_diagnostic(source);
            assert_eq!(diagnostic.kind, expected, "{label}");
            assert_eq!(
                diagnostic
                    .payload
                    .as_ref()
                    .and_then(|payload| payload.phase),
                Some(HumanDiagnosticPhase::Parser),
                "{label}"
            );
        }
    }

    #[test]
    fn parses_typeclass_class_and_instance_declarations() {
        let module = parse_module(
            "\
class Add (A : Type) where
  add : A -> A -> A
instance Nat.add_inst : Add Nat where
  add := Nat.add",
        );

        assert_eq!(module.items.len(), 2);
        let HumanItem::Class(class) = &module.items[0] else {
            panic!("expected class");
        };
        assert_eq!(class.name.as_dotted(), "Add");
        assert_eq!(class.fields.len(), 1);
        assert_eq!(class.fields[0].name.as_dotted(), "add");

        let HumanItem::Instance(instance) = &module.items[1] else {
            panic!("expected instance");
        };
        assert_eq!(instance.name.as_dotted(), "Nat.add_inst");
        assert_eq!(instance.fields.len(), 1);
        assert_eq!(instance.fields[0].name.as_dotted(), "add");
    }

    #[test]
    fn parses_axiom_and_theorem_declarations() {
        let module = parse_module(
            "axiom excluded_middle : Prop
theorem p : Prop := excluded_middle",
        );

        assert!(matches!(module.items[0], HumanItem::Axiom(_)));
        assert!(matches!(module.items[1], HumanItem::Theorem(_)));
    }

    #[test]
    fn parses_theorem_by_block_with_intro_exact() {
        let module = parse_module("theorem id_nat : Nat -> Nat := by intro n exact n");
        let HumanItem::Theorem(decl) = &module.items[0] else {
            panic!("expected theorem");
        };
        let HumanDeclValue::ProofBlock(block) = &decl.value else {
            panic!("expected by proof block");
        };

        assert_eq!(block.script.tactics.len(), 2);
        let HumanTacticSyntax::Intro { name, .. } = &block.script.tactics[0] else {
            panic!("expected intro tactic");
        };
        assert_eq!(name.as_dotted(), "n");
        let HumanTacticSyntax::Exact { term, .. } = &block.script.tactics[1] else {
            panic!("expected exact tactic");
        };
        let HumanExpr::Ident { name, .. } = term else {
            panic!("expected exact term");
        };
        assert_eq!(name.as_dotted(), "n");
    }

    #[test]
    fn parses_multiline_by_block_and_preserves_tactic_order() {
        let module = parse_module(
            "\
theorem t : Prop := by
  intro n
  exact n
  apply f
  rw [h, <- Nat.add_zero]
  simp-lite
  smt [h, Nat.add_zero]
  finite_decide
  omega
  ring_nf
  bitblast
  induction n",
        );
        let HumanItem::Theorem(decl) = &module.items[0] else {
            panic!("expected theorem");
        };
        let HumanDeclValue::ProofBlock(block) = &decl.value else {
            panic!("expected by proof block");
        };

        assert!(matches!(
            block.script.tactics[0],
            HumanTacticSyntax::Intro { .. }
        ));
        assert!(matches!(
            block.script.tactics[1],
            HumanTacticSyntax::Exact { .. }
        ));
        assert!(matches!(
            block.script.tactics[2],
            HumanTacticSyntax::Apply { .. }
        ));
        let HumanTacticSyntax::Rewrite { rules, .. } = &block.script.tactics[3] else {
            panic!("expected rw tactic");
        };
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].direction, HumanRewriteDirection::Forward);
        assert_eq!(rules[1].direction, HumanRewriteDirection::Backward);
        let HumanExpr::Ident { name, .. } = &rules[1].term else {
            panic!("expected backward rw rule term");
        };
        assert_eq!(name.as_dotted(), "Nat.add_zero");
        assert!(matches!(
            block.script.tactics[4],
            HumanTacticSyntax::SimpLite { .. }
        ));
        let HumanTacticSyntax::Smt { lemmas, .. } = &block.script.tactics[5] else {
            panic!("expected smt tactic");
        };
        assert_eq!(lemmas.len(), 2);
        assert!(matches!(
            block.script.tactics[6],
            HumanTacticSyntax::FiniteDecide { .. }
        ));
        assert!(matches!(
            block.script.tactics[7],
            HumanTacticSyntax::Omega { .. }
        ));
        assert!(matches!(
            block.script.tactics[8],
            HumanTacticSyntax::RingNf { .. }
        ));
        assert!(matches!(
            block.script.tactics[9],
            HumanTacticSyntax::Bitblast { .. }
        ));
        assert!(matches!(
            block.script.tactics[10],
            HumanTacticSyntax::Induction { .. }
        ));
    }

    #[test]
    fn solver_tactics_parse_supported_solver_tactics_and_reject_unknown() {
        let supported = [
            (
                "finite_decide",
                "theorem t : Prop := by finite_decide",
                HumanTacticKind::FiniteDecide,
            ),
            (
                "omega",
                "theorem t : Prop := by omega",
                HumanTacticKind::Omega,
            ),
            (
                "ring_nf",
                "theorem t : Prop := by ring_nf",
                HumanTacticKind::RingNf,
            ),
            (
                "bitblast",
                "theorem t : Prop := by bitblast",
                HumanTacticKind::Bitblast,
            ),
            ("smt", "theorem t : Prop := by smt", HumanTacticKind::Smt),
        ];

        for (label, source, expected) in supported {
            let module = parse_module(source);
            let HumanItem::Theorem(decl) = &module.items[0] else {
                panic!("{label}: expected theorem");
            };
            let HumanDeclValue::ProofBlock(block) = &decl.value else {
                panic!("{label}: expected by proof block");
            };
            assert_eq!(block.script.tactics.len(), 1, "{label}");
            assert_eq!(block.script.tactics[0].kind(), expected, "{label}");
        }

        for (label, source) in [
            ("unknown solver", "theorem t : Prop := by linarith"),
            ("disabled solver alias", "theorem t : Prop := by ring"),
            ("raw SAT result", "theorem t : Prop := by unsat"),
        ] {
            let diagnostic = parse_diagnostic(source);
            assert_eq!(
                diagnostic.kind,
                HumanDiagnosticKind::UnsupportedTactic,
                "{label}"
            );
            assert_eq!(
                diagnostic
                    .payload
                    .as_ref()
                    .and_then(|payload| payload.phase),
                Some(HumanDiagnosticPhase::TacticParse),
                "{label}"
            );
        }
    }

    #[test]
    fn rejects_unsupported_and_future_tactic_syntax() {
        let unsupported = [
            ("constructor", "theorem t : Prop := by constructor"),
            ("cases", "theorem t : Prop := by cases h"),
            ("refine", "theorem t : Prop := by refine h"),
            ("have", "theorem t : Prop := by have h : Prop := Prop"),
            ("specialize", "theorem t : Prop := by specialize h x"),
            ("assumption", "theorem t : Prop := by assumption"),
            ("contradiction", "theorem t : Prop := by contradiction"),
            ("calc", "theorem t : Prop := by calc Prop"),
            (
                "case syntax",
                "theorem t : Prop := by case zero => exact zero",
            ),
            (
                "rewrite in hypotheses",
                "theorem t : Prop := by rw [h] at hp",
            ),
            (
                "occurrence selection",
                "theorem t : Prop := by rw [h] (occs := [1])",
            ),
            (
                "dependent induction modifiers",
                "theorem t : Prop := by induction n generalizing h",
            ),
            ("full simp", "theorem t : Prop := by simp"),
            ("ring", "theorem t : Prop := by ring"),
            ("linarith", "theorem t : Prop := by linarith"),
        ];

        for (feature, source) in unsupported {
            let diagnostic = parse_diagnostic(source);
            assert_eq!(
                diagnostic.kind,
                HumanDiagnosticKind::UnsupportedTactic,
                "{feature}"
            );
            assert_eq!(
                diagnostic
                    .payload
                    .as_ref()
                    .and_then(|payload| payload.phase),
                Some(HumanDiagnosticPhase::TacticParse),
                "{feature}"
            );
        }
    }

    #[test]
    fn rejects_malformed_rw_and_trailing_tactic_tokens() {
        assert_eq!(
            parse_err("theorem t : Prop := by rw []"),
            HumanDiagnosticKind::ParseError
        );
        assert_eq!(
            parse_err("theorem t : Prop := by rw [<- h"),
            HumanDiagnosticKind::ParseError
        );
        assert_eq!(
            parse_err("theorem t : Prop := by exact n ]"),
            HumanDiagnosticKind::UnsupportedTactic
        );
    }

    #[test]
    fn parses_simple_inductive_declaration() {
        let module = parse_module(
            "inductive Nat : Type where
| zero : Nat
| succ : forall (n : Nat), Nat",
        );
        let HumanItem::Inductive(decl) = &module.items[0] else {
            panic!("expected inductive");
        };

        assert_eq!(decl.name.as_dotted(), "Nat");
        assert_eq!(decl.constructors.len(), 2);
        assert_eq!(decl.constructors[1].name.as_dotted(), "succ");
    }

    #[test]
    fn parses_empty_inductive_declaration() {
        let module = parse_module("inductive Empty : Type where");
        let HumanItem::Inductive(decl) = &module.items[0] else {
            panic!("expected inductive");
        };

        assert_eq!(decl.name.as_dotted(), "Empty");
        assert!(decl.constructors.is_empty());
    }

    #[test]
    fn parses_notation_and_infix_declarations() {
        let module = parse_module(
            "notation \"zero\" => Nat.zero
infix:50 \" = \" => Eq
infixl:65 \" + \" => Nat.add
infixr:70 \" :: \" => List.cons",
        );

        assert_eq!(module.items.len(), 4);
        let HumanItem::Notation(generic) = &module.items[0] else {
            panic!("expected notation");
        };
        let HumanItem::Notation(infixl) = &module.items[2] else {
            panic!("expected infixl");
        };
        assert_eq!(generic.kind, HumanNotationKind::Notation);
        assert_eq!(generic.token, "zero");
        assert_eq!(infixl.kind, HumanNotationKind::Infixl);
        assert_eq!(infixl.precedence, 65);
        assert_eq!(infixl.token, "+");
    }

    #[test]
    fn parses_fun_forall_let_annotation_application_and_parens() {
        let term = parse_term("fun x => let y : (Nat) := x in (y : Nat)");
        let HumanExpr::Lam { binders, body, .. } = term else {
            panic!("expected lambda");
        };

        assert_eq!(binders.len(), 1);
        assert!(matches!(body.as_ref(), HumanExpr::Let { .. }));

        let forall = parse_term("forall (x y : Nat), Eq Nat x y");
        let HumanExpr::Pi { binders, body, .. } = forall else {
            panic!("expected Pi");
        };
        assert_eq!(binders.len(), 2);
        assert!(matches!(body.as_ref(), HumanExpr::App { .. }));
    }

    #[test]
    fn parses_arrows_as_right_associative_anonymous_pi() {
        let term = parse_term("Nat -> Nat → Nat");
        let HumanExpr::Pi { binders, body, .. } = term else {
            panic!("expected outer arrow Pi");
        };

        assert_eq!(binders.len(), 1);
        assert!(matches!(binders[0].kind, HumanBinderKind::Anonymous));
        assert!(matches!(body.as_ref(), HumanExpr::Pi { .. }));
    }

    #[test]
    fn parses_holes_and_explicit_head_mode() {
        assert!(matches!(
            parse_term("_"),
            HumanExpr::Hole { name: None, .. }
        ));

        let named = parse_term("?m");
        assert!(matches!(named, HumanExpr::Hole { name: Some(_), .. }));

        let explicit = parse_term("@Eq.refl.{1} Nat n");
        let HumanExpr::App { func, .. } = explicit else {
            panic!("expected application");
        };
        let HumanExpr::App { func, .. } = func.as_ref() else {
            panic!("expected nested application");
        };
        let HumanExpr::Ident { implicit_mode, .. } = func.as_ref() else {
            panic!("expected explicit head");
        };
        assert_eq!(*implicit_mode, HumanImplicitMode::Explicit);
    }

    #[test]
    fn parses_operator_terms_as_notation_applications() {
        let module = parse_module(
            "\
infixl:65 \" + \" => Nat.add
infix:50 \" = \" => Eq
def t (n : Nat) : Prop := n + Nat.zero = n",
        );
        let HumanItem::Def(decl) = &module.items[2] else {
            panic!("expected def");
        };
        let HumanDeclValue::Term(term) = &decl.value else {
            panic!("expected term value");
        };
        let HumanExpr::NotationApp { head, args, .. } = term else {
            panic!("expected outer notation app");
        };

        assert_eq!(head.token, "=");
        assert_eq!(head.associativity, HumanNotationAssociativity::NonAssoc);
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0], HumanExpr::NotationApp { .. }));
    }

    #[test]
    fn non_associative_infix_chain_is_parse_error() {
        let err = parse_err(
            "\
infix:50 \" = \" => Eq
def bad (a : Nat) (b : Nat) (c : Nat) : Prop := a = b = c",
        );

        assert_eq!(err, HumanDiagnosticKind::ParseError);
    }

    #[test]
    fn parse_error_payload_records_parser_phase() {
        let err = parse_human_module(FileId(0), "def bad : Type :=")
            .expect_err("invalid Human syntax should be rejected by parser");

        assert_eq!(err.kind, HumanDiagnosticKind::ParseError);
        assert_eq!(
            err.payload.as_ref().and_then(|payload| payload.phase),
            Some(HumanDiagnosticPhase::Parser)
        );
    }

    #[test]
    fn notation_conflict_is_deterministic_diagnostic() {
        let err = parse_err(
            "\
infixl:65 \" + \" => Nat.add
infixr:70 \" + \" => Other.add",
        );

        assert_eq!(err, HumanDiagnosticKind::NotationConflict);
    }

    #[test]
    fn open_namespace_notation_conflict_is_deterministic_diagnostic() {
        let err = parse_err(
            "\
namespace A
infixl:65 \" + \" => Nat.add
end A
namespace B
infixr:70 \" + \" => Other.add
end B
open A
open B",
        );

        assert_eq!(err, HumanDiagnosticKind::NotationConflict);
    }
}
