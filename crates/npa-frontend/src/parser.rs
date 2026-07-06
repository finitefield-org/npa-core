use crate::{
    lex,
    machine::{MachineDecl, MachineUniverseParam},
    FileId, MachineBinder, MachineDiagnostic, MachineDiagnosticKind, MachineItem, MachineLevel,
    MachineModule, MachineName, MachineTerm, Result, Span, Token, TokenKind,
};

pub fn parse_machine_module(file_id: FileId, source: &str) -> Result<MachineModule> {
    let tokens = lex(file_id, source)?;
    Parser::new(tokens).parse_module(file_id, source.len() as u32)
}

pub fn parse_machine_term(file_id: FileId, source: &str) -> Result<MachineTerm> {
    let tokens = lex(file_id, source)?;
    let mut parser = Parser::new(tokens);
    let term = parser.parse_term()?;
    if !parser.at_eof() {
        return Err(MachineDiagnostic::parse(
            parser.peek_span(),
            "expected end of Machine Surface term",
        ));
    }
    Ok(term)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_module(&mut self, file_id: FileId, source_len: u32) -> Result<MachineModule> {
        let mut items = Vec::new();
        let mut saw_non_import = false;

        while !self.at_eof() {
            let item = match self.peek_kind() {
                TokenKind::Import => {
                    if saw_non_import {
                        let span = self.peek_span();
                        return Err(MachineDiagnostic::error(
                            MachineDiagnosticKind::ImportAfterItem,
                            span,
                            "import items must appear before definitions and theorems",
                        ));
                    }
                    self.parse_import()?
                }
                TokenKind::Def => {
                    saw_non_import = true;
                    MachineItem::Def(self.parse_decl()?)
                }
                TokenKind::Theorem => {
                    saw_non_import = true;
                    MachineItem::Theorem(self.parse_decl()?)
                }
                TokenKind::Open
                | TokenKind::Namespace
                | TokenKind::Match
                | TokenKind::With
                | TokenKind::Notation
                | TokenKind::Infix
                | TokenKind::Infixl
                | TokenKind::Infixr => {
                    return Err(MachineDiagnostic::unsupported_syntax(
                        self.peek_span(),
                        "open, namespace, match, with, and notation declarations are not Machine Surface syntax",
                    ));
                }
                TokenKind::Axiom | TokenKind::Inductive => {
                    return Err(MachineDiagnostic::error(
                        MachineDiagnosticKind::UnsupportedItem,
                        self.peek_span(),
                        "source-level axiom and inductive declarations are not Machine Surface items",
                    ));
                }
                TokenKind::Hole | TokenKind::NamedHole(_) => {
                    return Err(self.hole_not_allowed(self.peek_span()));
                }
                _ => {
                    return Err(MachineDiagnostic::parse(
                        self.peek_span(),
                        "expected import, def, theorem, or end of file",
                    ));
                }
            };

            items.push(item);
        }

        Ok(MachineModule {
            file_id,
            items,
            span: Span::new(file_id, 0, source_len),
        })
    }

    fn parse_import(&mut self) -> Result<MachineItem> {
        let start = self.expect_import()?;
        let module = self.parse_name()?;
        let span = start.join(module.span);

        Ok(MachineItem::Import { module, span })
    }

    fn parse_decl(&mut self) -> Result<MachineDecl> {
        let start = match self.peek_kind() {
            TokenKind::Def => self.expect_def()?,
            TokenKind::Theorem => self.expect_theorem()?,
            _ => {
                return Err(MachineDiagnostic::parse(
                    self.peek_span(),
                    "expected def or theorem",
                ));
            }
        };
        let name = self.parse_name()?;
        let universe_params = self.parse_optional_universe_params()?;
        let mut binders = Vec::new();

        while matches!(self.peek_kind(), TokenKind::LParen) {
            binders.push(self.parse_binder()?);
        }

        self.expect_colon()?;
        let ty = self.parse_term()?;
        self.expect_colon_eq()?;
        let value = self.parse_term()?;
        let span = start.join(value.span());

        Ok(MachineDecl {
            name,
            universe_params,
            binders,
            ty,
            value,
            span,
        })
    }

    fn parse_binder(&mut self) -> Result<MachineBinder> {
        let start = self.expect_lparen()?;
        let (name, name_span) = self.expect_ident("expected binder name")?;

        if !matches!(self.peek_kind(), TokenKind::Colon) {
            return Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnannotatedBinder,
                name_span,
                "Machine Surface binders must have an explicit type annotation",
            ));
        }

        self.expect_colon()?;
        let ty = self.parse_term()?;
        let end = self.expect_rparen()?;
        let span = start.join(end);

        Ok(MachineBinder { name, ty, span })
    }

    fn parse_optional_universe_params(&mut self) -> Result<Vec<MachineUniverseParam>> {
        if !self.at_universe_brace() {
            return Ok(Vec::new());
        }

        self.expect_dot()?;
        self.expect_lbrace()?;
        let mut params = Vec::new();

        loop {
            let (name, span) = self.expect_ident("expected universe parameter name")?;
            params.push(MachineUniverseParam { name, span });

            if matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                continue;
            }

            break;
        }

        self.expect_rbrace()?;
        Ok(params)
    }

    fn parse_optional_universe_args(&mut self) -> Result<Option<(Vec<MachineLevel>, Span)>> {
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

    fn parse_term(&mut self) -> Result<MachineTerm> {
        match self.peek_kind() {
            TokenKind::Fun => self.parse_lam(),
            TokenKind::Forall => self.parse_pi(),
            TokenKind::Let => self.parse_let(),
            _ => self.parse_annotation(),
        }
    }

    fn parse_lam(&mut self) -> Result<MachineTerm> {
        let start = self.expect_fun()?;

        if !matches!(self.peek_kind(), TokenKind::LParen) {
            return Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnannotatedBinder,
                self.peek_span(),
                "lambda binders must use the form (x : A)",
            ));
        }

        let mut binders = Vec::new();
        while matches!(self.peek_kind(), TokenKind::LParen) {
            binders.push(self.parse_binder()?);
        }

        self.expect_fat_arrow()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(MachineTerm::Lam {
            binders,
            body: Box::new(body),
            span,
        })
    }

    fn parse_pi(&mut self) -> Result<MachineTerm> {
        let start = self.expect_forall()?;

        if !matches!(self.peek_kind(), TokenKind::LParen) {
            return Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnannotatedBinder,
                self.peek_span(),
                "forall binders must use the form (x : A)",
            ));
        }

        let mut binders = Vec::new();
        while matches!(self.peek_kind(), TokenKind::LParen) {
            binders.push(self.parse_binder()?);
        }

        self.expect_comma()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(MachineTerm::Pi {
            binders,
            body: Box::new(body),
            span,
        })
    }

    fn parse_let(&mut self) -> Result<MachineTerm> {
        let start = self.expect_let()?;
        let (name, name_span) = self.expect_ident("expected let binding name")?;

        if matches!(self.peek_kind(), TokenKind::ColonEq) {
            return Err(MachineDiagnostic::error(
                MachineDiagnosticKind::UnannotatedLet,
                name_span,
                "Machine Surface let bindings must have an explicit type annotation",
            ));
        }

        self.expect_colon()?;
        let ty = self.parse_term()?;
        self.expect_colon_eq()?;
        let value = self.parse_term()?;
        self.expect_in()?;
        let body = self.parse_term()?;
        let span = start.join(body.span());

        Ok(MachineTerm::Let {
            name,
            ty: Box::new(ty),
            value: Box::new(value),
            body: Box::new(body),
            span,
        })
    }

    fn parse_annotation(&mut self) -> Result<MachineTerm> {
        let expr = self.parse_app()?;

        if !matches!(self.peek_kind(), TokenKind::Colon) {
            return Ok(expr);
        }

        self.expect_colon()?;
        let ty = self.parse_term()?;
        let span = expr.span().join(ty.span());

        Ok(MachineTerm::Annot {
            expr: Box::new(expr),
            ty: Box::new(ty),
            span,
        })
    }

    fn parse_app(&mut self) -> Result<MachineTerm> {
        let mut term = self.parse_atom()?;

        while self.is_atom_start() {
            let arg = self.parse_atom()?;
            let span = term.span().join(arg.span());
            term = MachineTerm::App {
                func: Box::new(term),
                arg: Box::new(arg),
                span,
            };
        }

        Ok(term)
    }

    fn parse_atom(&mut self) -> Result<MachineTerm> {
        match self.peek_kind() {
            TokenKind::Ident(_) => self.parse_ref(false),
            TokenKind::At => {
                let at = self.expect_at()?;
                self.parse_explicit_ref(at)
            }
            TokenKind::Prop => self.parse_prop(),
            TokenKind::Type => self.parse_type(),
            TokenKind::Sort => self.parse_sort(),
            TokenKind::LParen => {
                self.expect_lparen()?;
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Ok(term)
            }
            TokenKind::Hole | TokenKind::NamedHole(_) => {
                Err(self.hole_not_allowed(self.peek_span()))
            }
            TokenKind::Number(_) => Err(MachineDiagnostic::unsupported_syntax(
                self.peek_span(),
                "numeric term literals are not Machine Surface syntax",
            )),
            _ => Err(MachineDiagnostic::parse(
                self.peek_span(),
                "expected Machine Surface term",
            )),
        }
    }

    fn parse_ref(&mut self, explicit_mode: bool) -> Result<MachineTerm> {
        let name = self.parse_name()?;
        let universe_args = self.parse_optional_universe_args()?;
        let span = match &universe_args {
            Some((_, args_span)) => name.span.join(*args_span),
            None => name.span,
        };

        Ok(MachineTerm::Ident {
            name,
            universe_args: universe_args.map(|(args, _)| args),
            explicit_mode,
            span,
        })
    }

    fn parse_explicit_ref(&mut self, at: Span) -> Result<MachineTerm> {
        let name = self.parse_name()?;
        let universe_args = self.parse_optional_universe_args()?;
        let span = match &universe_args {
            Some((_, args_span)) => at.join(*args_span),
            None => at.join(name.span),
        };

        Ok(MachineTerm::Ident {
            name,
            universe_args: universe_args.map(|(args, _)| args),
            explicit_mode: true,
            span,
        })
    }

    fn parse_prop(&mut self) -> Result<MachineTerm> {
        let span = self.expect_prop()?;
        Ok(MachineTerm::Prop { span })
    }

    fn parse_type(&mut self) -> Result<MachineTerm> {
        let start = self.expect_type()?;
        let base = if self.is_type_level_start() {
            self.parse_level()?
        } else {
            MachineLevel::Nat {
                value: 0,
                span: start,
            }
        };
        let span = start.join(base.span());

        Ok(MachineTerm::Type { level: base, span })
    }

    fn parse_sort(&mut self) -> Result<MachineTerm> {
        let start = self.expect_sort()?;
        let level = self.parse_level()?;
        let span = start.join(level.span());

        Ok(MachineTerm::Sort { level, span })
    }

    fn parse_level(&mut self) -> Result<MachineLevel> {
        match self.peek_kind() {
            TokenKind::Number(value) => {
                let value = *value;
                let span = self.advance().span;
                Ok(MachineLevel::Nat { value, span })
            }
            TokenKind::Succ => {
                let start = self.advance().span;
                let level = self.parse_level()?;
                let span = start.join(level.span());
                Ok(MachineLevel::Succ {
                    level: Box::new(level),
                    span,
                })
            }
            TokenKind::Max => {
                let start = self.advance().span;
                let lhs = self.parse_level()?;
                let rhs = self.parse_level()?;
                let span = start.join(rhs.span());
                Ok(MachineLevel::Max {
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
                Ok(MachineLevel::IMax {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span,
                })
            }
            TokenKind::Ident(name) => {
                let name = name.clone();
                let span = self.advance().span;
                Ok(MachineLevel::Param { name, span })
            }
            _ => Err(MachineDiagnostic::parse(
                self.peek_span(),
                "expected universe level",
            )),
        }
    }

    fn parse_name(&mut self) -> Result<MachineName> {
        let (first, first_span) = self.expect_ident("expected name")?;
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

        Ok(MachineName::new(parts, span))
    }

    fn is_atom_start(&self) -> bool {
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

    fn is_type_level_start(&self) -> bool {
        match self.peek_kind() {
            TokenKind::Number(_) => true,
            TokenKind::Succ | TokenKind::Max | TokenKind::IMax => true,
            TokenKind::Ident(_) => !matches!(
                self.peek_next_kind(),
                Some(TokenKind::Dot) | Some(TokenKind::LBrace)
            ),
            _ => false,
        }
    }

    fn at_universe_brace(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Dot)
            && matches!(self.peek_next_kind(), Some(TokenKind::LBrace))
    }

    fn hole_not_allowed(&self, span: Span) -> MachineDiagnostic {
        MachineDiagnostic::error(
            MachineDiagnosticKind::HoleNotAllowed,
            span,
            "holes are not allowed in Machine Surface",
        )
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

    fn expect_ident(&mut self, message: &'static str) -> Result<(String, Span)> {
        match self.peek_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                let span = self.advance().span;
                Ok((name, span))
            }
            _ => Err(MachineDiagnostic::parse(self.peek_span(), message)),
        }
    }

    fn expect_dotted_name_component(&mut self, message: &'static str) -> Result<(String, Span)> {
        let Some(spelling) = reserved_name_component_spelling(self.peek_kind()) else {
            return self.expect_ident(message);
        };
        let span = self.advance().span;
        Ok((spelling.to_owned(), span))
    }

    fn expect_import(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Import, "expected import")
    }

    fn expect_def(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Def, "expected def")
    }

    fn expect_theorem(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Theorem, "expected theorem")
    }

    fn expect_fun(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Fun, "expected fun")
    }

    fn expect_forall(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Forall, "expected forall")
    }

    fn expect_let(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Let, "expected let")
    }

    fn expect_in(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::In, "expected in")
    }

    fn expect_prop(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Prop, "expected Prop")
    }

    fn expect_type(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Type, "expected Type")
    }

    fn expect_sort(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Sort, "expected Sort")
    }

    fn expect_dot(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Dot, "expected '.'")
    }

    fn expect_lbrace(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::LBrace, "expected '{'")
    }

    fn expect_rbrace(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::RBrace, "expected '}'")
    }

    fn expect_lparen(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::LParen, "expected '('")
    }

    fn expect_rparen(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::RParen, "expected ')'")
    }

    fn expect_colon(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Colon, "expected ':'")
    }

    fn expect_colon_eq(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::ColonEq, "expected ':='")
    }

    fn expect_comma(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::Comma, "expected ','")
    }

    fn expect_fat_arrow(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::FatArrow, "expected '=>'")
    }

    fn expect_at(&mut self) -> Result<Span> {
        self.expect_unit(TokenKindName::At, "expected '@'")
    }

    fn expect_unit(&mut self, expected: TokenKindName, message: &'static str) -> Result<Span> {
        if expected.matches(self.peek_kind()) {
            Ok(self.advance().span)
        } else {
            Err(MachineDiagnostic::parse(self.peek_span(), message))
        }
    }
}

fn reserved_name_component_spelling(kind: &TokenKind) -> Option<&'static str> {
    Some(match kind {
        TokenKind::Import => "import",
        TokenKind::Def => "def",
        TokenKind::Theorem => "theorem",
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
        TokenKind::Open => "open",
        TokenKind::Namespace => "namespace",
        TokenKind::Match => "match",
        TokenKind::With => "with",
        TokenKind::Notation => "notation",
        TokenKind::Infix => "infix",
        TokenKind::Infixl => "infixl",
        TokenKind::Infixr => "infixr",
        TokenKind::Axiom => "axiom",
        TokenKind::Inductive => "inductive",
        _ => return None,
    })
}

#[derive(Clone, Copy)]
enum TokenKindName {
    Import,
    Def,
    Theorem,
    Fun,
    Forall,
    Let,
    In,
    Prop,
    Type,
    Sort,
    Dot,
    LBrace,
    RBrace,
    LParen,
    RParen,
    Colon,
    ColonEq,
    Comma,
    FatArrow,
    At,
}

impl TokenKindName {
    fn matches(self, kind: &TokenKind) -> bool {
        matches!(
            (self, kind),
            (Self::Import, TokenKind::Import)
                | (Self::Def, TokenKind::Def)
                | (Self::Theorem, TokenKind::Theorem)
                | (Self::Fun, TokenKind::Fun)
                | (Self::Forall, TokenKind::Forall)
                | (Self::Let, TokenKind::Let)
                | (Self::In, TokenKind::In)
                | (Self::Prop, TokenKind::Prop)
                | (Self::Type, TokenKind::Type)
                | (Self::Sort, TokenKind::Sort)
                | (Self::Dot, TokenKind::Dot)
                | (Self::LBrace, TokenKind::LBrace)
                | (Self::RBrace, TokenKind::RBrace)
                | (Self::LParen, TokenKind::LParen)
                | (Self::RParen, TokenKind::RParen)
                | (Self::Colon, TokenKind::Colon)
                | (Self::ColonEq, TokenKind::ColonEq)
                | (Self::Comma, TokenKind::Comma)
                | (Self::FatArrow, TokenKind::FatArrow)
                | (Self::At, TokenKind::At)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> MachineModule {
        parse_machine_module(FileId(0), source).expect("source should parse")
    }

    fn parse_err(source: &str) -> MachineDiagnosticKind {
        parse_machine_module(FileId(0), source)
            .expect_err("source should be rejected")
            .kind
    }

    fn ident_name(term: &MachineTerm) -> &str {
        match term {
            MachineTerm::Ident { name, .. } => &name.parts[0],
            other => panic!("expected ident term, got {other:?}"),
        }
    }

    fn module_snapshot(module: &MachineModule) -> Vec<String> {
        module.items.iter().map(item_snapshot).collect()
    }

    fn item_snapshot(item: &MachineItem) -> String {
        match item {
            MachineItem::Import { module, .. } => format!("import {}", module.as_dotted()),
            MachineItem::Def(decl) => format!("def {}", decl_snapshot(decl)),
            MachineItem::Theorem(decl) => format!("theorem {}", decl_snapshot(decl)),
        }
    }

    fn decl_snapshot(decl: &MachineDecl) -> String {
        let universe_params = decl
            .universe_params
            .iter()
            .map(|param| param.name.as_str())
            .collect::<Vec<_>>()
            .join(",");
        let binders = decl
            .binders
            .iter()
            .map(binder_snapshot)
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{}.{{{universe_params}}}[{binders}]:={} := {}",
            decl.name.as_dotted(),
            term_snapshot(&decl.ty),
            term_snapshot(&decl.value)
        )
    }

    fn binder_snapshot(binder: &MachineBinder) -> String {
        format!("{}:{}", binder.name, term_snapshot(&binder.ty))
    }

    fn level_snapshot(level: &MachineLevel) -> String {
        match level {
            MachineLevel::Nat { value, .. } => value.to_string(),
            MachineLevel::Param { name, .. } => name.clone(),
            MachineLevel::Succ { level, .. } => format!("succ({})", level_snapshot(level)),
            MachineLevel::Max { lhs, rhs, .. } => {
                format!("max({},{})", level_snapshot(lhs), level_snapshot(rhs))
            }
            MachineLevel::IMax { lhs, rhs, .. } => {
                format!("imax({},{})", level_snapshot(lhs), level_snapshot(rhs))
            }
        }
    }

    fn universe_args_snapshot(universe_args: Option<&Vec<MachineLevel>>) -> String {
        let Some(universe_args) = universe_args else {
            return String::new();
        };
        format!(
            ".{{{}}}",
            universe_args
                .iter()
                .map(level_snapshot)
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    fn term_snapshot(term: &MachineTerm) -> String {
        match term {
            MachineTerm::Ident {
                name,
                universe_args,
                explicit_mode,
                ..
            } => format!(
                "{}{}{}",
                if *explicit_mode { "@" } else { "" },
                name.as_dotted(),
                universe_args_snapshot(universe_args.as_ref())
            ),
            MachineTerm::Local { name, .. } => format!("local({name})"),
            MachineTerm::Prop { .. } => "Prop".to_owned(),
            MachineTerm::Type { level, .. } => format!("Type({})", level_snapshot(level)),
            MachineTerm::Sort { level, .. } => format!("Sort({})", level_snapshot(level)),
            MachineTerm::App { func, arg, .. } => {
                format!("app({}, {})", term_snapshot(func), term_snapshot(arg))
            }
            MachineTerm::Lam { binders, body, .. } => format!(
                "fun({}; {})",
                binders
                    .iter()
                    .map(binder_snapshot)
                    .collect::<Vec<_>>()
                    .join(","),
                term_snapshot(body)
            ),
            MachineTerm::Pi { binders, body, .. } => format!(
                "forall({}; {})",
                binders
                    .iter()
                    .map(binder_snapshot)
                    .collect::<Vec<_>>()
                    .join(","),
                term_snapshot(body)
            ),
            MachineTerm::Let {
                name,
                ty,
                value,
                body,
                ..
            } => format!(
                "let({name}:{}={}; {})",
                term_snapshot(ty),
                term_snapshot(value),
                term_snapshot(body)
            ),
            MachineTerm::Annot { expr, ty, .. } => {
                format!("({} : {})", term_snapshot(expr), term_snapshot(ty))
            }
        }
    }

    #[test]
    fn parses_empty_machine_module() {
        let module = parse_machine_module(FileId(0), " \n\t ").expect("empty module should parse");

        assert_eq!(module.file_id, FileId(0));
        assert!(module.items.is_empty());
        assert_eq!(module.span, Span::new(FileId(0), 0, 4));
    }

    #[test]
    fn parses_import() {
        let module = parse("import Std.Nat.Basic");

        assert_eq!(module.items.len(), 1);
        let MachineItem::Import { module, .. } = &module.items[0] else {
            panic!("expected import item");
        };
        assert_eq!(module.as_dotted(), "Std.Nat.Basic");
    }

    #[test]
    fn parses_reserved_spellings_after_dot_as_name_components() {
        let module = parse("def Test.kw.{u} : M.Type := M.match.{succ u}");

        let MachineItem::Def(decl) = &module.items[0] else {
            panic!("expected def item");
        };
        assert_eq!(decl.name.as_dotted(), "Test.kw");

        let MachineTerm::Ident { name, .. } = &decl.ty else {
            panic!("expected dotted type reference");
        };
        assert_eq!(name.as_dotted(), "M.Type");

        let MachineTerm::Ident {
            name,
            universe_args,
            ..
        } = &decl.value
        else {
            panic!("expected dotted value reference");
        };
        assert_eq!(name.as_dotted(), "M.match");
        assert!(matches!(
            &universe_args.as_ref().expect("universe args")[0],
            MachineLevel::Succ { .. }
        ));
    }

    #[test]
    fn parses_def_id() {
        let module = parse("def Test.id.{u} (A : Sort u) (x : A) : A := x");

        let MachineItem::Def(decl) = &module.items[0] else {
            panic!("expected def item");
        };
        assert_eq!(decl.name.as_dotted(), "Test.id");
        assert_eq!(decl.universe_params[0].name, "u");
        assert_eq!(decl.binders.len(), 2);
        assert_eq!(ident_name(&decl.ty), "A");
        assert_eq!(ident_name(&decl.value), "x");
    }

    #[test]
    fn parses_theorem_self_eq_with_explicit_universe_args() {
        let module = parse("theorem Test.self_eq (n : Nat) : Eq.{1} Nat n n := @Eq.refl.{1} Nat n");

        let MachineItem::Theorem(decl) = &module.items[0] else {
            panic!("expected theorem item");
        };
        assert_eq!(decl.name.as_dotted(), "Test.self_eq");

        let MachineTerm::App { func, .. } = &decl.ty else {
            panic!("expected theorem type application");
        };
        let MachineTerm::App { func, .. } = func.as_ref() else {
            panic!("expected theorem type application");
        };
        let MachineTerm::App { func, .. } = func.as_ref() else {
            panic!("expected theorem type application");
        };
        let MachineTerm::Ident {
            name,
            universe_args,
            ..
        } = func.as_ref()
        else {
            panic!("expected Eq ident");
        };
        assert_eq!(name.as_dotted(), "Eq");
        assert_eq!(universe_args.as_ref().expect("universe args").len(), 1);

        let MachineTerm::App { func, .. } = &decl.value else {
            panic!("expected proof application");
        };
        let MachineTerm::App { func, .. } = func.as_ref() else {
            panic!("expected proof application");
        };
        let MachineTerm::Ident {
            explicit_mode,
            name,
            ..
        } = func.as_ref()
        else {
            panic!("expected Eq.refl ident");
        };
        assert!(*explicit_mode);
        assert_eq!(name.as_dotted(), "Eq.refl");
    }

    #[test]
    fn parses_typed_fun_forall_let_and_annotation() {
        let module = parse(
            "def Test.f : forall (A : Sort 1), A := fun (A : Sort 1) => let x : A := (x : A) in x",
        );

        let MachineItem::Def(decl) = &module.items[0] else {
            panic!("expected def item");
        };
        assert!(matches!(decl.ty, MachineTerm::Pi { .. }));
        let MachineTerm::Lam { body, .. } = &decl.value else {
            panic!("expected lambda value");
        };
        let MachineTerm::Let { value, .. } = body.as_ref() else {
            panic!("expected let body");
        };
        assert!(matches!(value.as_ref(), MachineTerm::Annot { .. }));
    }

    #[test]
    fn parser_output_is_deterministic_for_same_input() {
        let source = "\
import Std.Nat.Basic
def Test.id.{u} (A : Sort u) (x : A) : A := (x : A)";

        let first = parse_machine_module(FileId(7), source).expect("source should parse");
        let second = parse_machine_module(FileId(7), source).expect("source should parse again");

        assert_eq!(first, second);
    }

    #[test]
    fn machine_surface_accepted_syntax_snapshot_is_stable() {
        let module = parse(
            "\
import Std.Nat.Basic
def Test.id.{u} (A : Sort u) (x : A) : A := x
theorem Test.self_eq (n : Nat) : Eq.{1} Nat n n := @Eq.refl.{1} Nat n
def Test.f : forall (A : Sort 1), A := fun (A : Sort 1) => let x : A := (x : A) in x",
        );

        assert_eq!(
            module_snapshot(&module),
            vec![
                "import Std.Nat.Basic",
                "def Test.id.{u}[A:Sort(u),x:A]:=A := x",
                "theorem Test.self_eq.{}[n:Nat]:=app(app(app(Eq.{1}, Nat), n), n) := app(app(@Eq.refl.{1}, Nat), n)",
                "def Test.f.{}[]:=forall(A:Sort(1); A) := fun(A:Sort(1); let(x:A=(x : A); x))",
            ]
        );
    }

    #[test]
    fn machine_surface_rejected_human_feature_snapshot_is_stable() {
        let cases = [
            ("open Nat", MachineDiagnosticKind::UnsupportedSyntax),
            ("namespace Nat", MachineDiagnosticKind::UnsupportedSyntax),
            (
                "notation \"x\" => Nat.zero",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "infixl:65 \" + \" => Nat.add",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "axiom choice : Prop",
                MachineDiagnosticKind::UnsupportedItem,
            ),
            (
                "inductive Nat : Type",
                MachineDiagnosticKind::UnsupportedItem,
            ),
            (
                "def Test.x : Nat := n + Nat.zero",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "def Test.x : Prop := _",
                MachineDiagnosticKind::HoleNotAllowed,
            ),
            (
                "def Test.x : Prop := \"x\"",
                MachineDiagnosticKind::ParseError,
            ),
            (
                "theorem Test.id : Nat -> Nat := by intro n exact n",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "theorem Test.rw : Prop := by rw [h]",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "theorem Test.simp : Prop := by simp-lite",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
            (
                "theorem Test.induction : Prop := by induction n simp-lite",
                MachineDiagnosticKind::UnsupportedSyntax,
            ),
        ];

        for (source, expected) in cases {
            assert_eq!(parse_err(source), expected, "{source}");
        }
    }

    #[test]
    fn unsupported_stateful_surface_features_do_not_affect_later_parse() {
        for source in [
            "open Nat",
            "namespace Nat",
            "notation \"x\" => Nat.zero",
            "infixl:65 \" + \" => Nat.add",
        ] {
            assert_eq!(parse_err(source), MachineDiagnosticKind::UnsupportedSyntax);
        }

        let module = parse("def Test.ok : Prop := Prop");
        assert_eq!(module.items.len(), 1);
    }

    #[test]
    fn rejects_import_after_item() {
        assert_eq!(
            parse_err("def Test.x : Prop := Prop\nimport Std.Nat.Basic"),
            MachineDiagnosticKind::ImportAfterItem
        );
    }

    #[test]
    fn rejects_unsupported_top_level_syntax() {
        for source in [
            "open Nat",
            "namespace Nat",
            "notation \"x\" => Nat.zero",
            "infix:50 \" = \" => Eq",
            "infixl:65 \" + \" => Nat.add",
            "infixr:70 \" :: \" => List.cons",
        ] {
            assert_eq!(parse_err(source), MachineDiagnosticKind::UnsupportedSyntax);
        }
    }

    #[test]
    fn rejects_unsupported_items() {
        assert_eq!(
            parse_err("axiom choice : Prop"),
            MachineDiagnosticKind::UnsupportedItem
        );
        assert_eq!(
            parse_err("inductive Nat : Type"),
            MachineDiagnosticKind::UnsupportedItem
        );
    }

    #[test]
    fn rejects_holes() {
        assert_eq!(parse_err("_"), MachineDiagnosticKind::HoleNotAllowed);
        assert_eq!(parse_err("?m"), MachineDiagnosticKind::HoleNotAllowed);
        assert_eq!(
            parse_err("def Test.x : Prop := _"),
            MachineDiagnosticKind::HoleNotAllowed
        );
        assert_eq!(
            parse_err("def Test.x : Prop := ?m"),
            MachineDiagnosticKind::HoleNotAllowed
        );
    }

    #[test]
    fn rejects_reserved_spellings_as_binders_universe_params_and_heads() {
        assert_eq!(
            parse_err("def Test.bad (succ : Prop) : Prop := Prop"),
            MachineDiagnosticKind::ParseError
        );
        assert_eq!(
            parse_err("def Test.bad.{max} : Prop := Prop"),
            MachineDiagnosticKind::ParseError
        );
        assert_eq!(
            parse_err("def Test.bad : Prop := match"),
            MachineDiagnosticKind::ParseError
        );
    }

    #[test]
    fn rejects_unannotated_lambda_binder() {
        assert_eq!(
            parse_err("def Test.id : Nat := fun x => x"),
            MachineDiagnosticKind::UnannotatedBinder
        );
    }

    #[test]
    fn rejects_unannotated_let() {
        assert_eq!(
            parse_err("def Test.x : Nat := let x := Nat.zero in x"),
            MachineDiagnosticKind::UnannotatedLet
        );
    }

    #[test]
    fn rejects_operator_notation() {
        assert_eq!(
            parse_err("def Test.x : Nat := n + Nat.zero"),
            MachineDiagnosticKind::UnsupportedSyntax
        );
    }

    #[test]
    fn rejects_comments_and_string_literals_as_machine_surface_syntax() {
        assert_eq!(parse_err("-- doc"), MachineDiagnosticKind::ParseError);
        assert_eq!(
            parse_err("def Test.x : Prop := \"x\""),
            MachineDiagnosticKind::ParseError
        );
    }
}
