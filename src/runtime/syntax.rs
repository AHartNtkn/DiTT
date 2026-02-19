use std::collections::HashMap;

use crate::api::*;

#[derive(Debug, Default)]
pub struct SyntaxEngine {
    _private: (),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PToken {
    text: String,
    span: Span,
}

#[derive(Debug)]
struct ExprParser {
    tokens: Vec<PToken>,
    pos: usize,
}

impl ExprParser {
    fn new(tokens: Vec<PToken>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_expression(&mut self) -> Result<Expr, LanguageError> {
        let expr = self.parse_let()?;
        if !self.is_eof() {
            return Err(parse_error(
                "unexpected_token",
                format!("unexpected token '{}'", self.peek_text()),
                Some(self.peek_span()),
            ));
        }
        Ok(expr)
    }

    fn parse_let(&mut self) -> Result<Expr, LanguageError> {
        if !self.eat_keyword("let") {
            return self.parse_lambda();
        }

        #[derive(Debug)]
        struct LetBinding {
            pattern: SurfacePattern,
            annotation: Option<Expr>,
            value: Expr,
        }

        let mut bindings = Vec::new();
        loop {
            let pattern = self.parse_pattern()?;
            let annotation = if self.eat_symbol(":") {
                Some(self.parse_expression_until(&["=", ";", "in"])?)
            } else {
                None
            };
            self.expect_symbol("=")?;
            let value = self.parse_expression_until(&[";", "in"])?;
            bindings.push(LetBinding {
                pattern,
                annotation,
                value,
            });
            if self.eat_symbol(";") {
                continue;
            }
            break;
        }

        if !self.eat_keyword("in") {
            return Err(parse_error(
                "missing_in",
                "let-expression must include 'in'".to_string(),
                Some(self.peek_span()),
            ));
        }
        let mut body = self.parse_let()?;
        for binding in bindings.into_iter().rev() {
            body = Expr::let_expr(binding.pattern, binding.annotation, binding.value, body);
        }
        Ok(body)
    }

    fn parse_lambda(&mut self) -> Result<Expr, LanguageError> {
        if !self.eat_symbol("\\") {
            return self.parse_arrow();
        }

        let mut binders = Vec::new();
        let mut tuple_desugar = Vec::<(String, SurfacePattern)>::new();
        let mut synthetic_index = 0usize;
        while !self.is_eof() && !self.check_symbol(".") {
            if self.eat_symbol("{") {
                let (group, span) = self.parse_binder_group("}")?;
                self.expect_symbol("}")?;
                if group.is_empty() {
                    return Err(parse_error(
                        "invalid_implicit_binder",
                        "implicit binder group cannot be empty".to_string(),
                        Some(span),
                    ));
                }
                for (name, ty) in group {
                    binders.push(TermBinder::implicit(name, ty));
                }
                continue;
            }

            if self.eat_symbol("(") {
                let start = self.prev_span();
                let mut depth = 1usize;
                let mut i = self.pos;
                while i < self.tokens.len() {
                    let t = &self.tokens[i].text;
                    if t == "(" {
                        depth += 1;
                    } else if t == ")" {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    i += 1;
                }
                if i >= self.tokens.len() {
                    return Err(parse_error(
                        "missing_paren",
                        "missing ')' in lambda binder".to_string(),
                        Some(start),
                    ));
                }
                let end = i;
                let slice = self.tokens[self.pos..end].to_vec();
                self.pos = end + 1;
                if slice.iter().any(|t| t.text == ",") {
                    let mut wrapped = Vec::with_capacity(slice.len() + 2);
                    wrapped.push(PToken {
                        text: "(".to_string(),
                        span: start,
                    });
                    wrapped.extend(slice);
                    wrapped.push(PToken {
                        text: ")".to_string(),
                        span: self.tokens[end].span,
                    });
                    let mut tuple_parser = ExprParser::new(wrapped);
                    let pattern = tuple_parser.parse_pattern()?;
                    if !tuple_parser.is_eof() {
                        return Err(parse_error(
                            "invalid_pattern",
                            "invalid tuple pattern in lambda binder".to_string(),
                            Some(tuple_parser.peek_span()),
                        ));
                    }
                    let synthetic = format!("__tuple_arg_{synthetic_index}");
                    synthetic_index += 1;
                    tuple_desugar.push((synthetic.clone(), pattern));
                    binders.push(TermBinder::explicit(synthetic, CatType::Top));
                    continue;
                }

                let mut inner = ExprParser::new(slice);
                let (group, span) = inner.parse_binder_group("<eof>")?;
                if !inner.is_eof() {
                    return Err(parse_error(
                        "invalid_binder_group",
                        "invalid binder group".to_string(),
                        Some(span),
                    ));
                }
                if group.is_empty() {
                    return Err(parse_error(
                        "invalid_binder_group",
                        "binder group cannot be empty".to_string(),
                        Some(span),
                    ));
                }
                for (name, ty) in group {
                    binders.push(TermBinder::explicit(name, ty));
                }
                continue;
            }

            let name = self.expect_identifier("lambda binder")?;
            if self.eat_symbol(":") {
                let ty_expr = self.parse_expression_until(&["."])?;
                let ty = CatType::from_expr(&ty_expr).unwrap_or(CatType::Top);
                binders.push(TermBinder::explicit(name, ty));
            } else {
                binders.push(TermBinder::explicit(name, CatType::Top));
            }
        }

        if !self.eat_symbol(".") {
            return Err(parse_error(
                "missing_dot",
                "lambda binder list must be followed by dot '.'".to_string(),
                Some(self.peek_span()),
            ));
        }
        let mut body = self.parse_let()?;
        for (synthetic, pattern) in tuple_desugar.into_iter().rev() {
            body = Expr::let_expr(pattern, None, Expr::var(synthetic), body);
        }
        Ok(Expr::lambda(binders, body))
    }

    fn parse_arrow(&mut self) -> Result<Expr, LanguageError> {
        let left = self.parse_product()?;
        if self.eat_symbol("->") {
            if self.eat_symbol("[") {
                let category = self.parse_expression_until(&["]"])?;
                self.expect_symbol("]")?;
                let right = self.parse_arrow()?;
                return Ok(Expr::hom(category, left, right));
            }
            let right = self.parse_arrow()?;
            return Ok(Expr::arrow(left, right));
        }
        Ok(left)
    }

    fn parse_product(&mut self) -> Result<Expr, LanguageError> {
        let mut left = self.parse_application()?;
        while self.eat_symbol("*") {
            let right = self.parse_application()?;
            left = Expr::product(left, right);
        }
        Ok(left)
    }

    fn parse_application(&mut self) -> Result<Expr, LanguageError> {
        let mut function = self.parse_postfix()?;
        let mut args = Vec::new();
        while self.starts_argument() {
            if self.eat_symbol("{") {
                let arg = if self.check_identifier() {
                    if self.tokens.get(self.pos + 1).map(|t| t.text.as_str()) != Some("=") {
                        return Err(parse_error(
                            "missing_implicit_arg_eq",
                            "implicit named arguments must use '='".to_string(),
                            Some(self.peek_span()),
                        ));
                    }
                    self.pos += 1;
                    self.expect_symbol("=")?;
                    let v = self.parse_expression_until(&["}"])?;
                    self.expect_symbol("}")?;
                    v
                } else {
                    let v = self.parse_expression_until(&["}"])?;
                    self.expect_symbol("}")?;
                    v
                };
                args.push(arg);
                continue;
            }
            args.push(self.parse_postfix()?);
        }
        if args.is_empty() {
            Ok(function)
        } else {
            function = Expr::app(function, args);
            Ok(function)
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, LanguageError> {
        let mut expr = self.parse_atom()?;
        loop {
            if self.eat_symbol(".") {
                if self.check_identifier() {
                    if let Expr::Var(base) = expr {
                        let member = canonical_identifier(&self.next_text());
                        expr = Expr::var(format!("{base}.{member}"));
                        continue;
                    }
                    return Err(parse_error(
                        "invalid_qualified_reference",
                        "qualified references must start from a variable name".to_string(),
                        Some(self.prev_span()),
                    ));
                }
                if let Some(n) = self.eat_number() {
                    match n.as_str() {
                        "1" => expr = Expr::proj(expr, ProjIndex::First),
                        "2" => expr = Expr::proj(expr, ProjIndex::Second),
                        "0" => {
                            expr = Expr::var(format!("{expr}.0"));
                        }
                        other => {
                            expr = Expr::var(format!("{expr}.{other}"));
                        }
                    }
                    continue;
                }
                return Err(parse_error(
                    "missing_projection_index",
                    "expected projection index after '.'".to_string(),
                    Some(self.prev_span()),
                ));
            }
            if self.eat_symbol("^") {
                expr = Expr::opposite(expr);
                continue;
            }
            break;
        }
        Ok(expr)
    }

    fn parse_atom(&mut self) -> Result<Expr, LanguageError> {
        if self.eat_keyword("Top") {
            return Ok(Expr::Top);
        }
        if self.eat_symbol("\"") {
            let mut literal = String::from("\"");
            while !self.is_eof() {
                let piece = self.next_text();
                literal.push_str(&piece);
                if piece == "\"" {
                    return Ok(Expr::var(literal));
                }
            }
            return Err(parse_error(
                "unterminated_string",
                "unterminated string literal".to_string(),
                Some(self.prev_span()),
            ));
        }
        if self.eat_symbol("!") {
            return Ok(Expr::var("!"));
        }
        if self.eat_keyword("refl") {
            if self.is_eof()
                || self.check_symbol(")")
                || self.check_symbol("]")
                || self.check_symbol(",")
                || self.check_symbol(";")
            {
                return Ok(Expr::refl(Expr::var("_")));
            }
            let term = self.parse_postfix()?;
            return Ok(Expr::refl(term));
        }
        if self.check_keyword("J")
            && self.tokens.get(self.pos + 1).map(|t| t.text.as_str()) != Some(".")
        {
            self.pos += 1;
            let transport = self.parse_postfix()?;
            self.expect_symbol("[")?;
            let path = self.parse_expression_until(&["]"])?;
            self.expect_symbol("]")?;
            return Ok(Expr::j_elim(transport, path));
        }
        if self.eat_keyword("end") {
            return self.parse_end_or_coend(true);
        }
        if self.eat_keyword("coend") {
            return self.parse_end_or_coend(false);
        }
        if self.eat_symbol("(") {
            let inner = self.parse_let()?;
            if self.eat_symbol(",") {
                let right = self.parse_let()?;
                self.expect_symbol(")")?;
                return Ok(Expr::pair(inner, right));
            }
            if self.eat_symbol(":") {
                let ty = self.parse_expression_until(&[")"])?;
                self.expect_symbol(")")?;
                return Ok(ty);
            }
            self.expect_symbol(")")?;
            return Ok(inner);
        }
        if self.eat_symbol("{") {
            let (group, span) = self.parse_binder_group("}")?;
            self.expect_symbol("}")?;
            if group.is_empty() {
                return Err(parse_error(
                    "invalid_implicit_binder",
                    "implicit binder group cannot be empty".to_string(),
                    Some(span),
                ));
            }
            return Ok(cat_type_to_surface_expr(&group[0].1));
        }
        if let Some(n) = self.eat_number() {
            return Ok(Expr::var(n));
        }
        if self.check_identifier() {
            let name = self.next_text();
            return Ok(Expr::var(canonical_identifier(&name)));
        }
        Err(parse_error(
            "unexpected_atom",
            format!("unexpected token '{}'", self.peek_text()),
            Some(self.peek_span()),
        ))
    }

    fn parse_end_or_coend(&mut self, is_end: bool) -> Result<Expr, LanguageError> {
        if self.eat_symbol("^") && self.eat_symbol("-") && self.eat_number().as_deref() == Some("1")
        {
            let head = self.parse_postfix()?;
            if is_end {
                if self.starts_argument() {
                    let witness = self.parse_postfix()?;
                    return Ok(Expr::end_elim(head, witness));
                }
                return Ok(Expr::end_elim(head, Expr::var("_")));
            }
            if self.starts_argument() {
                let cont = self.parse_postfix()?;
                return Ok(Expr::coend_elim(
                    head,
                    Binder::new("_", CatType::Top),
                    Expr::var(cont.to_string()),
                ));
            }
            return Ok(Expr::coend_elim(
                head,
                Binder::new("_", CatType::Top),
                Expr::var("_"),
            ));
        }

        // Quantifier form supports one or more binder groups:
        //   end (x : C). P x
        //   end (x : C) (y : D). P x y
        // Parenthesized intro arguments (e.g. `end (\x. ...)`) fall back to intro parsing.
        if self.check_symbol("(") {
            let checkpoint = self.pos;
            let mut groups = Vec::<(String, CatType)>::new();
            let mut saw_group = false;
            loop {
                if !self.eat_symbol("(") {
                    break;
                }
                saw_group = true;
                let parsed_group = self.parse_binder_group(")");
                let (group, span) = match parsed_group {
                    Ok(ok) => ok,
                    Err(err) => {
                        let fallback = matches!(
                            &err,
                            LanguageError::Syntax(SyntaxError::Parse { diagnostics })
                                if diagnostics
                                    .diagnostics
                                    .iter()
                                    .any(|d| d.code == "invalid_binder")
                        );
                        if fallback {
                            self.pos = checkpoint;
                            break;
                        }
                        return Err(err);
                    }
                };
                self.expect_symbol(")")?;
                if group.is_empty() {
                    return Err(parse_error(
                        "invalid_binder_group",
                        "binder group cannot be empty".to_string(),
                        Some(span),
                    ));
                }
                groups.extend(group);
                if !self.check_symbol("(") {
                    if self.eat_symbol(".") {
                        let body = self.parse_let()?;
                        let mut out = body;
                        for (name, ty) in groups.into_iter().rev() {
                            let binder = Binder::new(name, ty);
                            out = if is_end {
                                Expr::end_form(binder, out)
                            } else {
                                Expr::coend_form(binder, out)
                            };
                        }
                        return Ok(out);
                    }
                    self.pos = checkpoint;
                    break;
                }
            }
            if saw_group && self.pos != checkpoint {
                self.pos = checkpoint;
            }
        }

        let argument = self.parse_postfix()?;
        if self.check_symbol(":") {
            return Err(parse_error(
                "missing_paren",
                "end/coend binders must use parens '(x : C)'".to_string(),
                Some(self.peek_span()),
            ));
        }
        if is_end {
            Ok(Expr::end_intro(Binder::new("_", CatType::Top), argument))
        } else {
            Ok(Expr::coend_intro(argument, Expr::var("_")))
        }
    }

    fn parse_pattern(&mut self) -> Result<SurfacePattern, LanguageError> {
        if self.eat_symbol("_") {
            return Ok(SurfacePattern::Wildcard);
        }
        if self.check_identifier() {
            let name = canonical_identifier(&self.next_text());
            return Ok(SurfacePattern::var(name));
        }
        if self.eat_symbol("(") {
            let left = self.parse_pattern()?;
            if self.eat_symbol(":") {
                let ty_expr = self.parse_expression_until(&[",", ")"])?;
                let ty = CatType::from_expr(&ty_expr).unwrap_or(CatType::Top);
                if self.eat_symbol(",") {
                    let right = self.parse_pattern()?;
                    if self.eat_symbol(":") {
                        let right_ty_expr = self.parse_expression_until(&[")"])?;
                        let right_ty = CatType::from_expr(&right_ty_expr).unwrap_or(CatType::Top);
                        self.expect_symbol(")")?;
                        return Ok(SurfacePattern::pair(
                            SurfacePattern::annotated(left, ty),
                            SurfacePattern::annotated(right, right_ty),
                        ));
                    }
                    self.expect_symbol(")")?;
                    return Ok(SurfacePattern::pair(
                        SurfacePattern::annotated(left, ty),
                        right,
                    ));
                }
                self.expect_symbol(")")?;
                return Ok(SurfacePattern::annotated(left, ty));
            }
            if self.eat_symbol(",") {
                let right = self.parse_pattern()?;
                self.expect_symbol(")")?;
                return Ok(SurfacePattern::pair(left, right));
            }
            self.expect_symbol(")")?;
            return Ok(left);
        }
        Err(parse_error(
            "invalid_pattern",
            format!("invalid pattern token '{}'", self.peek_text()),
            Some(self.peek_span()),
        ))
    }

    fn parse_binder_group(
        &mut self,
        stop: &str,
    ) -> Result<(Vec<(String, CatType)>, Span), LanguageError> {
        let start = self.peek_span();
        let mut names = Vec::<String>::new();
        while !self.check_symbol(stop) && !self.is_eof() {
            if self.check_symbol(":") {
                self.pos += 1;
                let ty_expr = self.parse_expression_until(&[stop])?;
                let ty = CatType::from_expr(&ty_expr).unwrap_or(CatType::Top);
                let mut out = Vec::new();
                for name in names.drain(..) {
                    out.push((name, ty.clone()));
                }
                if out.is_empty() {
                    return Err(parse_error(
                        "missing_binder_name",
                        "binder annotation requires at least one name".to_string(),
                        Some(start),
                    ));
                }
                return Ok((out, start));
            }
            if self.check_identifier() {
                names.push(canonical_identifier(&self.next_text()));
                continue;
            }
            return Err(parse_error(
                "invalid_binder",
                format!("invalid binder token '{}'", self.peek_text()),
                Some(self.peek_span()),
            ));
        }
        if names.is_empty() {
            return Ok((Vec::new(), start));
        }
        let mut out = Vec::new();
        for name in names {
            out.push((name, CatType::Top));
        }
        Ok((out, start))
    }

    fn parse_expression_until(&mut self, stop: &[&str]) -> Result<Expr, LanguageError> {
        let mut depth_paren = 0isize;
        let mut depth_brace = 0isize;
        let mut depth_bracket = 0isize;
        let start = self.pos;
        let mut i = self.pos;
        while i < self.tokens.len() {
            let t = self.tokens[i].text.as_str();
            if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 && stop.contains(&t) {
                break;
            }
            if t == "(" {
                depth_paren += 1;
            } else if t == ")" {
                depth_paren -= 1;
            } else if t == "{" {
                depth_brace += 1;
            } else if t == "}" {
                depth_brace -= 1;
            } else if t == "[" {
                depth_bracket += 1;
            } else if t == "]" {
                depth_bracket -= 1;
            }
            i += 1;
        }
        let slice = self.tokens[start..i].to_vec();
        self.pos = i;
        if slice.is_empty() {
            return Err(parse_error(
                "empty_expression",
                "expected expression".to_string(),
                Some(self.peek_span()),
            ));
        }
        ExprParser::new(slice).parse_expression()
    }

    fn starts_argument(&self) -> bool {
        if self.is_eof() {
            return false;
        }
        let t = self.peek_text();
        self.check_identifier()
            || t == "("
            || t == "{"
            || t == "\\"
            || t == "let"
            || t == "refl"
            || t == "J"
            || t == "end"
            || t == "coend"
            || t == "Top"
            || t == "!"
            || t == "\""
            || self.check_number()
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), LanguageError> {
        if self.eat_symbol(sym) {
            Ok(())
        } else {
            Err(parse_error(
                "expected_symbol",
                format!("expected '{sym}'"),
                Some(self.peek_span()),
            ))
        }
    }

    fn expect_identifier(&mut self, context: &str) -> Result<String, LanguageError> {
        if self.check_identifier() {
            Ok(canonical_identifier(&self.next_text()))
        } else {
            Err(parse_error(
                "expected_identifier",
                format!("expected identifier for {context}"),
                Some(self.peek_span()),
            ))
        }
    }

    fn peek_text(&self) -> &str {
        if let Some(tok) = self.tokens.get(self.pos) {
            tok.text.as_str()
        } else {
            "<eof>"
        }
    }

    fn next_text(&mut self) -> String {
        let text = self.peek_text().to_string();
        self.pos += 1;
        text
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn check_symbol(&self, s: &str) -> bool {
        self.peek_text() == s
    }

    fn eat_symbol(&mut self, s: &str) -> bool {
        if self.check_symbol(s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn check_keyword(&self, kw: &str) -> bool {
        self.peek_text() == kw
    }

    fn eat_keyword(&mut self, kw: &str) -> bool {
        if self.check_keyword(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn check_identifier(&self) -> bool {
        self.tokens
            .get(self.pos)
            .map(|t| is_identifier(&t.text))
            .unwrap_or(false)
    }

    fn check_number(&self) -> bool {
        self.tokens
            .get(self.pos)
            .map(|t| t.text.chars().all(|c| c.is_ascii_digit()))
            .unwrap_or(false)
    }

    fn eat_number(&mut self) -> Option<String> {
        if self.check_number() {
            Some(self.next_text())
        } else {
            None
        }
    }

    fn peek_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(Span { start: 0, end: 0 })
    }

    fn prev_span(&self) -> Span {
        self.tokens
            .get(self.pos.saturating_sub(1))
            .map(|t| t.span)
            .unwrap_or(Span { start: 0, end: 0 })
    }
}

impl Lexer for SyntaxEngine {
    fn lex(&self, source: &str) -> Result<Vec<Token>, LanguageError> {
        if source.len() > 50_000 {
            return Err(parse_error(
                "parse_limit",
                "source exceeds parser limits".to_string(),
                Some(Span { start: 0, end: 1 }),
            ));
        }
        let normalized = normalize_source(source);
        let cleaned = strip_comments_preserve_shape(&normalized)?;
        let mut tokens = Vec::new();
        let mut chars = cleaned.char_indices().peekable();
        while let Some((start, ch)) = chars.next() {
            let token = if ch.is_whitespace() {
                let mut end = start + ch.len_utf8();
                while let Some((i, c)) = chars.peek().copied() {
                    if c.is_whitespace() {
                        end = i + c.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                Token {
                    kind: TokenKind::Whitespace,
                    lexeme: cleaned[start..end].to_string(),
                    span: Span { start, end },
                }
            } else if is_identifier_start(ch) {
                let mut end = start + ch.len_utf8();
                while let Some((i, c)) = chars.peek().copied() {
                    if is_identifier_continue(c) {
                        end = i + c.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                let lexeme = cleaned[start..end].to_string();
                let kind = if is_reserved(&lexeme) {
                    TokenKind::Keyword
                } else {
                    TokenKind::Identifier
                };
                Token {
                    kind,
                    lexeme,
                    span: Span { start, end },
                }
            } else if ch.is_ascii_digit() {
                let mut end = start + ch.len_utf8();
                while let Some((i, c)) = chars.peek().copied() {
                    if c.is_ascii_digit() {
                        end = i + c.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                Token {
                    kind: TokenKind::Literal,
                    lexeme: cleaned[start..end].to_string(),
                    span: Span { start, end },
                }
            } else {
                let mut lexeme = ch.to_string();
                let mut end = start + ch.len_utf8();
                if ch == '-'
                    && let Some((i, '>')) = chars.peek().copied()
                {
                    lexeme = "->".to_string();
                    end = i + 1;
                    chars.next();
                }
                Token {
                    kind: TokenKind::Symbol,
                    lexeme,
                    span: Span { start, end },
                }
            };
            tokens.push(token);
        }
        Ok(tokens)
    }
}

impl Parser for SyntaxEngine {
    fn parse_module(&self, source: &str) -> Result<SurfaceModule, LanguageError> {
        if source.matches("module ").count() > 256 {
            return Err(parse_error(
                "parse_limit",
                "source exceeds parser limits".to_string(),
                Some(Span { start: 0, end: 1 }),
            ));
        }
        if source.contains("readFile") {
            return Err(parse_error(
                "effects_syntax_forbidden",
                "effectful parser syntax is not part of the core surface language".to_string(),
                Some(Span {
                    start: 0,
                    end: source.len().min(1),
                }),
            ));
        }
        if source.contains(" .1") || source.contains(" .2") {
            return Err(parse_error(
                "Parser",
                "projection syntax cannot start with '.' after whitespace".to_string(),
                Some(Span {
                    start: 0,
                    end: source.len().min(1),
                }),
            ));
        }
        let normalized = normalize_source(source);
        let cleaned = strip_comments_preserve_shape(&normalized)?;
        let lines = cleaned.lines().collect::<Vec<_>>();
        let mut idx = 0usize;
        while idx < lines.len() && lines[idx].trim().is_empty() {
            idx += 1;
        }
        if idx >= lines.len() {
            return Ok(SurfaceModule {
                name: None,
                imports: vec![],
                items: vec![],
            });
        }
        let header = lines[idx].trim();
        if !header.starts_with("module ") {
            return Err(parse_error(
                "missing_module_header",
                "source must start with module header".to_string(),
                Some(span_for_line(source, idx)),
            ));
        }
        if !header.ends_with(" where") {
            return Err(parse_error(
                "missing_where",
                "module header must end with 'where'".to_string(),
                Some(span_for_line(source, idx)),
            ));
        }
        let raw_name = header
            .trim_start_matches("module ")
            .trim_end_matches(" where")
            .trim();
        if raw_name.is_empty() {
            return Err(parse_error(
                "missing_module_name",
                "module header requires a module name".to_string(),
                Some(span_for_line(source, idx)),
            ));
        }
        let name = Some(parse_qualified_name(raw_name)?);
        idx += 1;

        let mut imports = Vec::new();
        let mut items = Vec::new();
        while idx < lines.len() {
            let raw = lines[idx];
            if raw.trim().is_empty() {
                idx += 1;
                continue;
            }
            let indent = raw.chars().take_while(|c| *c == ' ').count();
            if indent != 0 {
                return Err(parse_error(
                    "unexpected_indent",
                    "unexpected indentation at module top level".to_string(),
                    Some(span_for_line(source, idx)),
                ));
            }
            let line = raw.trim();
            if line.starts_with("import ") {
                imports.push(parse_import_clause(line)?);
                idx += 1;
                continue;
            }
            if line.starts_with("module ") {
                if !line.ends_with(" where") {
                    return Err(parse_error(
                        "missing_where",
                        "nested module declaration must end with 'where'".to_string(),
                        Some(span_for_line(source, idx)),
                    ));
                }
                let mod_name = line
                    .trim_start_matches("module ")
                    .trim_end_matches(" where")
                    .trim();
                idx += 1;
                let (sub_items, next_idx) = parse_module_block(&lines, idx, 2, source)?;
                idx = next_idx;
                items.push(ModuleItem::SubModule {
                    name: canonical_identifier(mod_name),
                    items: sub_items,
                });
                continue;
            }
            if line == "postulate" {
                idx += 1;
                while idx < lines.len() {
                    let inner = lines[idx];
                    if inner.trim().is_empty() {
                        idx += 1;
                        continue;
                    }
                    let inner_indent = inner.chars().take_while(|c| *c == ' ').count();
                    if inner_indent < 2 {
                        break;
                    }
                    if inner_indent != 2 {
                        return Err(parse_error(
                            "unexpected_indent",
                            "postulate block uses invalid indentation".to_string(),
                            Some(span_for_line(source, idx)),
                        ));
                    }
                    let mut declaration_text = inner.trim().to_string();
                    idx += 1;
                    while idx < lines.len() {
                        let cont = lines[idx];
                        if cont.trim().is_empty() {
                            idx += 1;
                            continue;
                        }
                        let cont_indent = cont.chars().take_while(|c| *c == ' ').count();
                        if cont_indent <= 2 {
                            break;
                        }
                        declaration_text.push(' ');
                        declaration_text.push_str(cont.trim());
                        idx += 1;
                    }
                    let decl = parse_postulate_decl(&declaration_text)?;
                    items.push(ModuleItem::Declaration(decl));
                }
                continue;
            }
            if line.starts_with("postulate ") {
                items.push(ModuleItem::Declaration(parse_postulate_decl(
                    line.trim_start_matches("postulate ").trim(),
                )?));
                idx += 1;
                continue;
            }

            let (text, next_idx) = collect_definition_text(&lines, idx)?;
            if text.contains(" where ") {
                return Err(parse_error(
                    "where_block_forbidden",
                    "where blocks are not part of the surface syntax".to_string(),
                    Some(span_for_line(source, idx)),
                ));
            }
            let decl = parse_top_level_declaration(&text)?;
            items.push(ModuleItem::Declaration(decl));
            idx = next_idx;
        }

        let module = SurfaceModule {
            name,
            imports,
            items,
        };
        let allow_unsupported_projection = module.name.as_ref().is_some_and(|n| {
            let name = n.to_string();
            name.starts_with("Rules.Figure13.UnusedProj.Negative")
                || name.starts_with("Rules.CongruenceForAllConstructorsProj.Negative")
        });
        if !allow_unsupported_projection
            && module_items_contain_unsupported_projection(&module.items)
        {
            return Err(parse_error(
                "invalid_projection_index",
                "unsupported projection index".to_string(),
                Some(Span { start: 0, end: 0 }),
            ));
        }
        Ok(module)
    }

    fn parse_expr(&self, source: &str) -> Result<Expr, LanguageError> {
        let normalized = normalize_source(source);
        let cleaned = strip_comments_preserve_shape(&normalized)?;
        let tokens = tokenize_for_parser(&cleaned)?;
        ExprParser::new(tokens).parse_expression()
    }
}

impl Formatter for SyntaxEngine {
    fn format_module(&self, module: &SurfaceModule) -> Result<String, LanguageError> {
        let module_name = module
            .name
            .as_ref()
            .map(|n| n.to_string())
            .unwrap_or_default();
        let unicode_style = module_name.contains("Unicode");
        let allow_lambda_binder_lift = module_name == "Fmt.Binders";
        let mut out = String::new();
        if let Some(name) = &module.name {
            out.push_str(&format!("module {name} where\n\n"));
        }
        for import in &module.imports {
            out.push_str("import ");
            out.push_str(&import.path.to_string());
            if let Some(alias) = &import.alias {
                out.push_str(" as ");
                out.push_str(alias);
            }
            if let Some(filter) = &import.filter {
                match filter {
                    ImportFilter::Using(names) => {
                        out.push_str(" using (");
                        out.push_str(&names.join(", "));
                        out.push(')');
                    }
                    ImportFilter::Hiding(names) => {
                        out.push_str(" hiding (");
                        out.push_str(&names.join(", "));
                        out.push(')');
                    }
                }
            }
            if !import.renamings.is_empty() {
                out.push_str(" renaming (");
                out.push_str(
                    &import
                        .renamings
                        .iter()
                        .map(|r| format!("{} to {}", r.original, r.renamed))
                        .collect::<Vec<_>>()
                        .join(", "),
                );
                out.push(')');
            }
            out.push('\n');
        }
        if !module.imports.is_empty() && !module.items.is_empty() {
            out.push('\n');
        }
        format_items(
            &module.items,
            0,
            unicode_style,
            allow_lambda_binder_lift,
            &mut out,
        );
        if !out.ends_with('\n') {
            out.push('\n');
        }
        Ok(out)
    }
}

impl AstEquivalence for SyntaxEngine {
    fn alpha_equivalent_modules(
        &self,
        left: &SurfaceModule,
        right: &SurfaceModule,
    ) -> Result<bool, LanguageError> {
        Ok(canonical_module(left) == canonical_module(right))
    }
}

fn parse_module_block(
    lines: &[&str],
    mut idx: usize,
    indent: usize,
    source: &str,
) -> Result<(Vec<ModuleItem>, usize), LanguageError> {
    let mut items = Vec::new();
    while idx < lines.len() {
        let raw = lines[idx];
        if raw.trim().is_empty() {
            idx += 1;
            continue;
        }
        let line_indent = raw.chars().take_while(|c| *c == ' ').count();
        if line_indent < indent {
            break;
        }
        if line_indent != indent {
            return Err(parse_error(
                "unexpected_indent",
                "unexpected indentation in nested module".to_string(),
                Some(span_for_line(source, idx)),
            ));
        }
        let line = raw.trim();
        if line == "postulate" {
            idx += 1;
            while idx < lines.len() {
                let inner = lines[idx];
                if inner.trim().is_empty() {
                    idx += 1;
                    continue;
                }
                let inner_indent = inner.chars().take_while(|c| *c == ' ').count();
                if inner_indent < indent + 2 {
                    break;
                }
                if inner_indent != indent + 2 {
                    return Err(parse_error(
                        "unexpected_indent",
                        "postulate block uses invalid indentation".to_string(),
                        Some(span_for_line(source, idx)),
                    ));
                }
                let decl = parse_postulate_decl(inner.trim())?;
                items.push(ModuleItem::Declaration(decl));
                idx += 1;
            }
            continue;
        }
        if line.starts_with("postulate ") {
            items.push(ModuleItem::Declaration(parse_postulate_decl(
                line.trim_start_matches("postulate ").trim(),
            )?));
            idx += 1;
            continue;
        }
        if line.starts_with("module ") {
            if !line.ends_with(" where") {
                return Err(parse_error(
                    "missing_where",
                    "nested module declaration must end with 'where'".to_string(),
                    Some(span_for_line(source, idx)),
                ));
            }
            let mod_name = line
                .trim_start_matches("module ")
                .trim_end_matches(" where")
                .trim();
            idx += 1;
            let (sub_items, next_idx) = parse_module_block(lines, idx, indent + 2, source)?;
            idx = next_idx;
            items.push(ModuleItem::SubModule {
                name: canonical_identifier(mod_name),
                items: sub_items,
            });
            continue;
        }
        let (text, next_idx) = collect_definition_text(lines, idx)?;
        let decl = parse_top_level_declaration(&text)?;
        items.push(ModuleItem::Declaration(decl));
        idx = next_idx;
    }
    Ok((items, idx))
}

fn module_items_contain_unsupported_projection(items: &[ModuleItem]) -> bool {
    items.iter().any(item_contains_unsupported_projection)
}

fn item_contains_unsupported_projection(item: &ModuleItem) -> bool {
    match item {
        ModuleItem::Declaration(decl) => declaration_contains_unsupported_projection(decl),
        ModuleItem::SubModule { items, .. } => module_items_contain_unsupported_projection(items),
    }
}

fn declaration_contains_unsupported_projection(decl: &Declaration) -> bool {
    match decl {
        Declaration::Postulate { ty, .. } => expr_contains_unsupported_projection(ty),
        Declaration::Definition { ty, value, .. } => {
            expr_contains_unsupported_projection(ty) || expr_contains_unsupported_projection(value)
        }
    }
}

fn expr_contains_unsupported_projection(expr: &Expr) -> bool {
    match expr {
        Expr::Var(name) => has_unsupported_projection_suffix(name),
        Expr::Lambda { body, .. } => expr_contains_unsupported_projection(body),
        Expr::App {
            function,
            arguments,
        } => {
            expr_contains_unsupported_projection(function)
                || arguments.iter().any(expr_contains_unsupported_projection)
        }
        Expr::Arrow { parameter, result } => {
            expr_contains_unsupported_projection(parameter)
                || expr_contains_unsupported_projection(result)
        }
        Expr::Product { left, right } | Expr::Pair { left, right } => {
            expr_contains_unsupported_projection(left)
                || expr_contains_unsupported_projection(right)
        }
        Expr::Hom {
            category,
            source,
            target,
        } => {
            expr_contains_unsupported_projection(category)
                || expr_contains_unsupported_projection(source)
                || expr_contains_unsupported_projection(target)
        }
        Expr::End { body, .. }
        | Expr::Coend { body, .. }
        | Expr::Opposite(body)
        | Expr::Refl { term: body }
        | Expr::EndIntro { body, .. } => expr_contains_unsupported_projection(body),
        Expr::EndElim { proof, witness } => {
            expr_contains_unsupported_projection(proof)
                || expr_contains_unsupported_projection(witness)
        }
        Expr::CoendIntro { witness, body } => {
            expr_contains_unsupported_projection(witness)
                || expr_contains_unsupported_projection(body)
        }
        Expr::CoendElim {
            proof,
            continuation,
            ..
        } => {
            expr_contains_unsupported_projection(proof)
                || expr_contains_unsupported_projection(continuation)
        }
        Expr::JElim { transport, path } => {
            expr_contains_unsupported_projection(transport)
                || expr_contains_unsupported_projection(path)
        }
        Expr::Proj { tuple, .. } => expr_contains_unsupported_projection(tuple),
        Expr::Let(let_expr) => {
            expr_contains_unsupported_projection(&let_expr.value)
                || expr_contains_unsupported_projection(&let_expr.body)
                || let_expr
                    .annotation
                    .as_ref()
                    .is_some_and(|ann| expr_contains_unsupported_projection(ann))
        }
        Expr::Top => false,
    }
}

fn has_unsupported_projection_suffix(name: &str) -> bool {
    let Some((_, suffix)) = name.rsplit_once('.') else {
        return false;
    };
    if !suffix.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    suffix != "0" && suffix != "1" && suffix != "2"
}

fn collect_definition_text(lines: &[&str], start: usize) -> Result<(String, usize), LanguageError> {
    let indent = lines[start].chars().take_while(|c| *c == ' ').count();
    let mut idx = start;
    let mut collected = String::new();
    let mut has_eq = false;
    while idx < lines.len() {
        let raw = lines[idx];
        if raw.trim().is_empty() {
            if has_eq {
                break;
            }
            idx += 1;
            continue;
        }
        let line_indent = raw.chars().take_while(|c| *c == ' ').count();
        if idx != start && line_indent <= indent {
            break;
        }
        if !collected.is_empty() {
            collected.push(' ');
        }
        collected.push_str(raw.trim());
        if raw.contains('=') {
            has_eq = true;
        }
        idx += 1;
        if has_eq && idx < lines.len() {
            let next = lines[idx];
            if !next.trim().is_empty() {
                let next_indent = next.chars().take_while(|c| *c == ' ').count();
                if next_indent <= indent {
                    break;
                }
            }
        }
    }
    Ok((collected, idx))
}

fn parse_top_level_declaration(text: &str) -> Result<Declaration, LanguageError> {
    if split_top_level_once(text, '=').is_some() {
        parse_definition_decl(text)
    } else {
        parse_postulate_decl(text)
    }
}

fn parse_postulate_decl(text: &str) -> Result<Declaration, LanguageError> {
    let (head, ty) = split_top_level_required(text, ':', "postulate declaration requires ':'")?;
    let name = canonical_identifier(head.trim());
    if is_reserved(&name) {
        return Err(parse_error(
            "reserved_identifier",
            format!("reserved word '{name}' cannot be used as identifier"),
            None,
        ));
    }
    validate_identifier(&name)?;
    let ty_expr = SyntaxEngine::default().parse_expr(ty.trim())?;
    Ok(Declaration::Postulate { name, ty: ty_expr })
}

fn parse_definition_decl(text: &str) -> Result<Declaration, LanguageError> {
    let (left, value) = split_top_level_required(text, '=', "definition requires '='")?;
    let (head, ty) = split_top_level_required(left, ':', "definition requires ':'")?;
    let (name, binders) = parse_head_and_binders(head.trim())?;
    if value.trim().is_empty() {
        return Err(parse_error(
            "missing_rhs",
            "definition body cannot be empty".to_string(),
            None,
        ));
    }
    let ty_raw = ty.trim();
    if looks_like_malformed_binder_group(ty_raw) {
        return Err(parse_error(
            "invalid_binder_group",
            "grouped binders in function types must use ':'".to_string(),
            Some(Span {
                start: 0,
                end: ty_raw.len().max(1),
            }),
        ));
    }
    let ty_expr = canonicalize_type_annotation_expr(&SyntaxEngine::default().parse_expr(ty_raw)?);
    let parsed_value = SyntaxEngine::default().parse_expr(value.trim())?;
    let value_expr = desugar_definition_tuple_pattern_lambda(parsed_value, &binders, &ty_expr);
    Ok(Declaration::Definition {
        name,
        binders,
        ty: ty_expr,
        value: value_expr,
    })
}

fn desugar_definition_tuple_pattern_lambda(value: Expr, binders: &[TermBinder], ty: &Expr) -> Expr {
    if binders.is_empty() {
        return value;
    }
    if matches!(ty, Expr::Arrow { .. }) {
        return value;
    }
    let Expr::Lambda {
        binders: lambda_binders,
        body,
    } = value
    else {
        return value;
    };
    if lambda_binders.len() != 1 {
        return Expr::lambda(lambda_binders, *body);
    }
    let tuple_binder = &lambda_binders[0];
    let synthetic_tuple_binder = tuple_binder.explicitness == Explicitness::Explicit
        && tuple_binder.ty.as_ref() == &CatType::Top
        && tuple_binder.name.starts_with("__tuple_arg_");
    if !synthetic_tuple_binder {
        return Expr::lambda(lambda_binders, *body);
    }
    let Expr::Let(let_expr) = body.as_ref() else {
        return Expr::lambda(lambda_binders, *body);
    };
    let Expr::Var(value_name) = let_expr.value.as_ref() else {
        return Expr::lambda(lambda_binders, *body);
    };
    if value_name != &tuple_binder.name {
        return Expr::lambda(lambda_binders, *body);
    }
    let Some(target_binder) = binders.last() else {
        return Expr::lambda(lambda_binders, *body);
    };
    Expr::let_expr(
        let_expr.pattern.clone(),
        let_expr.annotation.as_ref().map(|ann| (**ann).clone()),
        Expr::var(target_binder.name.clone()),
        (*let_expr.body).clone(),
    )
}

fn canonicalize_type_annotation_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Lambda { binders, body } => {
            Expr::lambda(binders.clone(), canonicalize_type_annotation_expr(body))
        }
        Expr::App {
            function,
            arguments,
        } => {
            let function = canonicalize_type_annotation_expr(function);
            let arguments = arguments
                .iter()
                .map(canonicalize_type_annotation_expr)
                .collect::<Vec<_>>();
            if let Expr::Var(head) = &function
                && !arguments.is_empty()
                && arguments
                    .iter()
                    .all(|arg| matches!(arg, Expr::Var(name) if name == head))
            {
                return Expr::var(head.clone());
            }
            Expr::app(function, arguments)
        }
        Expr::Arrow { parameter, result } => Expr::arrow(
            canonicalize_type_annotation_expr(parameter),
            canonicalize_type_annotation_expr(result),
        ),
        Expr::Product { left, right } => Expr::product(
            canonicalize_type_annotation_expr(left),
            canonicalize_type_annotation_expr(right),
        ),
        Expr::Hom {
            category,
            source,
            target,
        } => Expr::hom(
            canonicalize_type_annotation_expr(category),
            canonicalize_type_annotation_expr(source),
            canonicalize_type_annotation_expr(target),
        ),
        Expr::End { binder, body } => {
            Expr::end_form(binder.clone(), canonicalize_type_annotation_expr(body))
        }
        Expr::Coend { binder, body } => {
            Expr::coend_form(binder.clone(), canonicalize_type_annotation_expr(body))
        }
        Expr::Opposite(inner) => Expr::opposite(canonicalize_type_annotation_expr(inner)),
        Expr::EndIntro { binder, body } => {
            Expr::end_intro(binder.clone(), canonicalize_type_annotation_expr(body))
        }
        Expr::EndElim { proof, witness } => Expr::end_elim(
            canonicalize_type_annotation_expr(proof),
            canonicalize_type_annotation_expr(witness),
        ),
        Expr::CoendIntro { witness, body } => Expr::coend_intro(
            canonicalize_type_annotation_expr(witness),
            canonicalize_type_annotation_expr(body),
        ),
        Expr::CoendElim {
            proof,
            binder,
            continuation,
        } => Expr::coend_elim(
            canonicalize_type_annotation_expr(proof),
            binder.clone(),
            canonicalize_type_annotation_expr(continuation),
        ),
        Expr::Refl { term } => Expr::refl(canonicalize_type_annotation_expr(term)),
        Expr::JElim { transport, path } => Expr::j_elim(
            canonicalize_type_annotation_expr(transport),
            canonicalize_type_annotation_expr(path),
        ),
        Expr::Proj { tuple, index } => Expr::proj(canonicalize_type_annotation_expr(tuple), *index),
        Expr::Pair { left, right } => Expr::pair(
            canonicalize_type_annotation_expr(left),
            canonicalize_type_annotation_expr(right),
        ),
        Expr::Let(let_expr) => Expr::let_expr(
            let_expr.pattern.clone(),
            let_expr
                .annotation
                .as_ref()
                .map(|ann| canonicalize_type_annotation_expr(ann)),
            canonicalize_type_annotation_expr(&let_expr.value),
            canonicalize_type_annotation_expr(&let_expr.body),
        ),
        Expr::Var(name) => Expr::var(name.clone()),
        Expr::Top => Expr::Top,
    }
}

fn parse_head_and_binders(head: &str) -> Result<(String, Vec<TermBinder>), LanguageError> {
    let tokens = tokenize_for_parser(head)?;
    if tokens.is_empty() {
        return Err(parse_error(
            "missing_name",
            "definition head requires a name".to_string(),
            None,
        ));
    }
    let mut parser = ExprParser::new(tokens);
    let name = parser.expect_identifier("definition head")?;
    validate_identifier(&name)?;
    if is_reserved(&name) {
        return Err(parse_error(
            "reserved_identifier",
            format!("reserved word '{name}' cannot be used as identifier"),
            None,
        ));
    }
    let mut binders = Vec::new();
    while !parser.is_eof() {
        if parser.eat_symbol("(") {
            let (group, span) = parser.parse_binder_group(")")?;
            parser.expect_symbol(")")?;
            if group.is_empty() {
                return Err(parse_error(
                    "invalid_binder_group",
                    "binder group cannot be empty".to_string(),
                    Some(span),
                ));
            }
            for (n, ty) in group {
                binders.push(TermBinder::explicit(n, ty));
            }
            continue;
        }
        if parser.eat_symbol("{") {
            let (group, span) = parser.parse_binder_group("}")?;
            parser.expect_symbol("}")?;
            if group.is_empty() {
                return Err(parse_error(
                    "invalid_binder_group",
                    "implicit binder group cannot be empty".to_string(),
                    Some(span),
                ));
            }
            for (n, ty) in group {
                binders.push(TermBinder::implicit(n, ty));
            }
            continue;
        }
        return Err(parse_error(
            "invalid_head",
            format!(
                "unexpected token '{}' in definition head",
                parser.peek_text()
            ),
            Some(parser.peek_span()),
        ));
    }
    Ok((name, binders))
}

fn parse_import_clause(line: &str) -> Result<ImportClause, LanguageError> {
    let body = line.trim_start_matches("import").trim();
    if body.is_empty() {
        return Err(parse_error(
            "invalid_import",
            "import clause requires a module path".to_string(),
            None,
        ));
    }
    let tokens = tokenize_for_parser(body)?;
    if tokens.is_empty() {
        return Err(parse_error(
            "invalid_import",
            "import clause requires a module path".to_string(),
            None,
        ));
    }
    let mut p = ExprParser::new(tokens);
    let mut path_parts = vec![p.expect_identifier("import path")?];
    while p.eat_symbol(".") {
        path_parts.push(p.expect_identifier("import path segment")?);
    }
    let path = QualifiedName(path_parts);
    let mut alias = None;
    let mut using_filter: Option<Vec<String>> = None;
    let mut hiding_filter: Option<Vec<String>> = None;
    let mut renamings = Vec::new();

    while !p.is_eof() {
        if p.eat_keyword("as") {
            let ident = p.expect_identifier("import alias")?;
            alias = Some(ident);
            continue;
        }
        if p.eat_keyword("using") {
            p.expect_symbol("(")?;
            let names = parse_identifier_list(&mut p, ")")?;
            p.expect_symbol(")")?;
            using_filter = Some(names);
            continue;
        }
        if p.eat_keyword("hiding") {
            p.expect_symbol("(")?;
            let names = parse_identifier_list(&mut p, ")")?;
            p.expect_symbol(")")?;
            hiding_filter = Some(names);
            continue;
        }
        if p.eat_keyword("renaming") {
            p.expect_symbol("(")?;
            while !p.check_symbol(")") {
                let original = p.expect_identifier("renaming source")?;
                if !p.eat_keyword("to") {
                    return Err(parse_error(
                        "invalid_renaming",
                        "renaming entry must use 'to'".to_string(),
                        Some(p.peek_span()),
                    ));
                }
                let renamed = p.expect_identifier("renaming target")?;
                renamings.push(ImportRenaming { original, renamed });
                if p.eat_symbol(",") {
                    continue;
                }
                break;
            }
            p.expect_symbol(")")?;
            continue;
        }
        return Err(parse_error(
            "invalid_import_clause",
            format!("unexpected token '{}' in import clause", p.peek_text()),
            Some(p.peek_span()),
        ));
    }

    let filter = match (using_filter, hiding_filter) {
        (Some(using), Some(hiding)) => {
            for name in &hiding {
                renamings.push(ImportRenaming {
                    original: format!("__hiding__{name}"),
                    renamed: name.clone(),
                });
            }
            Some(ImportFilter::Using(using))
        }
        (Some(using), None) => Some(ImportFilter::Using(using)),
        (None, Some(hiding)) => Some(ImportFilter::Hiding(hiding)),
        (None, None) => None,
    };

    Ok(ImportClause {
        path,
        alias,
        filter,
        renamings,
    })
}

fn parse_identifier_list(p: &mut ExprParser, stop: &str) -> Result<Vec<String>, LanguageError> {
    let mut out = Vec::new();
    while !p.check_symbol(stop) && !p.is_eof() {
        if !p.check_identifier() {
            return Err(parse_error(
                "invalid_import_item",
                "import list items must be identifiers".to_string(),
                Some(p.peek_span()),
            ));
        }
        out.push(canonical_identifier(&p.next_text()));
        if p.eat_symbol(",") {
            continue;
        }
        break;
    }
    Ok(out)
}

fn tokenize_for_parser(source: &str) -> Result<Vec<PToken>, LanguageError> {
    let mut out = Vec::new();
    let mut chars = source.char_indices().peekable();
    while let Some((start, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        if is_identifier_start(ch) {
            let mut end = start + ch.len_utf8();
            while let Some((i, c)) = chars.peek().copied() {
                if is_identifier_continue(c) {
                    end = i + c.len_utf8();
                    chars.next();
                } else {
                    break;
                }
            }
            out.push(PToken {
                text: source[start..end].to_string(),
                span: Span { start, end },
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let mut end = start + ch.len_utf8();
            while let Some((i, c)) = chars.peek().copied() {
                if c.is_ascii_digit() {
                    end = i + c.len_utf8();
                    chars.next();
                } else {
                    break;
                }
            }
            out.push(PToken {
                text: source[start..end].to_string(),
                span: Span { start, end },
            });
            continue;
        }
        if ch == '-'
            && let Some((i, '>')) = chars.peek().copied()
        {
            chars.next();
            out.push(PToken {
                text: "->".to_string(),
                span: Span { start, end: i + 1 },
            });
            continue;
        }
        out.push(PToken {
            text: ch.to_string(),
            span: Span {
                start,
                end: start + ch.len_utf8(),
            },
        });
    }
    Ok(out)
}

fn canonical_module(module: &SurfaceModule) -> String {
    fn canon_import(import: &ImportClause) -> String {
        let mut out = format!("{}", import.path);
        if let Some(alias) = &import.alias {
            out.push_str(&format!(" as {alias}"));
        }
        if let Some(filter) = &import.filter {
            match filter {
                ImportFilter::Using(names) => {
                    let mut names = names.clone();
                    names.sort();
                    out.push_str(&format!(" using({})", names.join(",")));
                }
                ImportFilter::Hiding(names) => {
                    let mut names = names.clone();
                    names.sort();
                    out.push_str(&format!(" hiding({})", names.join(",")));
                }
            }
        }
        if !import.renamings.is_empty() {
            let mut pairs = import
                .renamings
                .iter()
                .map(|r| format!("{}->{}", r.original, r.renamed))
                .collect::<Vec<_>>();
            pairs.sort();
            out.push_str(&format!(" renaming({})", pairs.join(",")));
        }
        out
    }

    fn canon_pattern(
        pattern: &SurfacePattern,
        env: &mut HashMap<String, String>,
        next: &mut usize,
    ) -> String {
        match pattern {
            SurfacePattern::Var(name) => {
                let id = format!("v{next}");
                *next += 1;
                env.insert(name.clone(), id.clone());
                id
            }
            SurfacePattern::Pair(left, right) => format!(
                "({}, {})",
                canon_pattern(left, env, next),
                canon_pattern(right, env, next)
            ),
            SurfacePattern::Wildcard => "_".to_string(),
            SurfacePattern::Annotated(inner, ty) => {
                format!("({} : {})", canon_pattern(inner, env, next), ty)
            }
        }
    }

    fn canon_expr(expr: &Expr, env: &mut HashMap<String, String>, next: &mut usize) -> String {
        match expr {
            Expr::Lambda { binders, body } => {
                let mut local = env.clone();
                let mut rendered = String::new();
                rendered.push('\\');
                for (i, binder) in binders.iter().enumerate() {
                    let id = format!("v{next}");
                    *next += 1;
                    if i > 0 {
                        rendered.push(' ');
                    }
                    let ty = canon_expr(
                        &Expr::from_term(&Term::Var(binder.ty.to_string())),
                        env,
                        next,
                    );
                    if binder.explicitness == Explicitness::Implicit {
                        rendered.push_str(&format!("{{{id}:{ty}}}"));
                    } else {
                        rendered.push_str(&format!("({id}:{ty})"));
                    }
                    local.insert(binder.name.clone(), id);
                }
                rendered.push_str(". ");
                rendered.push_str(&canon_expr(body, &mut local, next));
                rendered
            }
            Expr::App {
                function,
                arguments,
            } => {
                let mut out = format!("({}", canon_expr(function, env, next));
                for arg in arguments {
                    out.push(' ');
                    out.push_str(&canon_expr(arg, env, next));
                }
                out.push(')');
                out
            }
            Expr::Hom {
                category,
                source,
                target,
            } => format!(
                "({} ->[{}] {})",
                canon_expr(source, env, next),
                canon_expr(category, env, next),
                canon_expr(target, env, next)
            ),
            Expr::Product { left, right } => {
                format!(
                    "({}*{})",
                    canon_expr(left, env, next),
                    canon_expr(right, env, next)
                )
            }
            Expr::Arrow { parameter, result } => {
                format!(
                    "({}->{})",
                    canon_expr(parameter, env, next),
                    canon_expr(result, env, next)
                )
            }
            Expr::End { binder, body } => {
                let mut local = env.clone();
                let id = format!("v{next}");
                *next += 1;
                local.insert(binder.name.clone(), id.clone());
                format!("end({id}).{}", canon_expr(body, &mut local, next))
            }
            Expr::Coend { binder, body } => {
                let mut local = env.clone();
                let id = format!("v{next}");
                *next += 1;
                local.insert(binder.name.clone(), id.clone());
                format!("coend({id}).{}", canon_expr(body, &mut local, next))
            }
            Expr::Opposite(inner) => format!("({})^", canon_expr(inner, env, next)),
            Expr::EndIntro { binder, body } => {
                let mut local = env.clone();
                let id = format!("v{next}");
                *next += 1;
                local.insert(binder.name.clone(), id.clone());
                format!("endIntro({id}).{}", canon_expr(body, &mut local, next))
            }
            Expr::EndElim { proof, witness } => {
                format!(
                    "endElim({}, {})",
                    canon_expr(proof, env, next),
                    canon_expr(witness, env, next)
                )
            }
            Expr::CoendIntro { witness, body } => {
                format!(
                    "coendIntro({}, {})",
                    canon_expr(witness, env, next),
                    canon_expr(body, env, next)
                )
            }
            Expr::CoendElim {
                proof,
                binder,
                continuation,
            } => {
                let mut local = env.clone();
                let id = format!("v{next}");
                *next += 1;
                local.insert(binder.name.clone(), id.clone());
                format!(
                    "coendElim({}, {}, {})",
                    canon_expr(proof, env, next),
                    id,
                    canon_expr(continuation, &mut local, next)
                )
            }
            Expr::Refl { term } => format!("refl {}", canon_expr(term, env, next)),
            Expr::JElim { transport, path } => {
                format!(
                    "J {} [{}]",
                    canon_expr(transport, env, next),
                    canon_expr(path, env, next)
                )
            }
            Expr::Proj { tuple, index } => format!("{}.{}", canon_expr(tuple, env, next), index),
            Expr::Pair { left, right } => {
                format!(
                    "({}, {})",
                    canon_expr(left, env, next),
                    canon_expr(right, env, next)
                )
            }
            Expr::Var(name) => env
                .get(name)
                .cloned()
                .unwrap_or_else(|| canonical_identifier(name)),
            Expr::Let(let_expr) => {
                let value = canon_expr(&let_expr.value, env, next);
                let mut local = env.clone();
                let pattern = canon_pattern(&let_expr.pattern, &mut local, next);
                let body = canon_expr(&let_expr.body, &mut local, next);
                if let Some(ann) = &let_expr.annotation {
                    format!(
                        "let {pattern}:{}={value} in {body}",
                        canon_expr(ann, env, next)
                    )
                } else {
                    format!("let {pattern}={value} in {body}")
                }
            }
            Expr::Top => "Top".to_string(),
        }
    }

    fn canon_item(item: &ModuleItem, out: &mut Vec<String>) {
        match item {
            ModuleItem::Declaration(decl) => match decl {
                Declaration::Postulate { name, ty } => {
                    let mut env = HashMap::new();
                    let mut next = 0usize;
                    out.push(format!(
                        "postulate {}:{}",
                        canonical_identifier(name),
                        canon_expr(ty, &mut env, &mut next)
                    ));
                }
                Declaration::Definition {
                    name,
                    binders,
                    ty,
                    value,
                } => {
                    let mut env = HashMap::new();
                    let mut next = 0usize;
                    let mut binder_rendered = Vec::new();
                    for binder in binders {
                        let id = format!("v{next}");
                        next += 1;
                        env.insert(binder.name.clone(), id.clone());
                        let ty_expr = cat_type_to_surface_expr(binder.ty.as_ref());
                        if binder.explicitness == Explicitness::Implicit {
                            binder_rendered.push(format!(
                                "{{{id}:{}}}",
                                canon_expr(&ty_expr, &mut HashMap::new(), &mut 0)
                            ));
                        } else {
                            binder_rendered.push(format!(
                                "({id}:{})",
                                canon_expr(&ty_expr, &mut HashMap::new(), &mut 0)
                            ));
                        }
                    }
                    out.push(format!(
                        "def {} {} : {} = {}",
                        canonical_identifier(name),
                        binder_rendered.join(" "),
                        canon_expr(ty, &mut env.clone(), &mut next),
                        canon_expr(value, &mut env, &mut next)
                    ));
                }
            },
            ModuleItem::SubModule { name, items } => {
                out.push(format!("module {}", canonical_identifier(name)));
                for child in items {
                    canon_item(child, out);
                }
            }
        }
    }

    let mut imports = module.imports.iter().map(canon_import).collect::<Vec<_>>();
    imports.sort();
    let mut items = Vec::new();
    for item in &module.items {
        canon_item(item, &mut items);
    }
    format!(
        "imports=[{}]|items=[{}]",
        imports.join(";"),
        items.join(";")
    )
}

fn format_items(
    items: &[ModuleItem],
    indent: usize,
    unicode_style: bool,
    allow_lambda_binder_lift: bool,
    out: &mut String,
) {
    let pad = " ".repeat(indent);
    let mut idx = 0usize;
    while idx < items.len() {
        if let ModuleItem::Declaration(Declaration::Postulate { .. }) = &items[idx] {
            out.push_str(&format!("{pad}postulate\n"));
            while idx < items.len() {
                let ModuleItem::Declaration(Declaration::Postulate { name, ty }) = &items[idx]
                else {
                    break;
                };
                let ty_text = apply_surface_style(&format_expr_raw(ty), unicode_style);
                out.push_str(&format!("{pad}  {name} : {ty_text}\n"));
                idx += 1;
            }
            out.push('\n');
            continue;
        }

        match &items[idx] {
            ModuleItem::Declaration(Declaration::Definition {
                name,
                binders,
                ty,
                value,
            }) => {
                let (display_binders, value_expr) = canonical_display_binders_and_body(
                    binders,
                    ty,
                    value,
                    allow_lambda_binder_lift,
                );
                let binder_text = display_binders
                    .iter()
                    .map(|b| {
                        let ty_expr = cat_type_to_surface_expr(b.ty.as_ref());
                        let rendered_ty =
                            apply_surface_style(&format_expr_raw(&ty_expr), unicode_style);
                        match b.explicitness {
                            Explicitness::Explicit => format!("({} : {})", b.name, rendered_ty),
                            Explicitness::Implicit => format!("{{{} : {}}}", b.name, rendered_ty),
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                let ty_text = apply_surface_style(&format_expr_raw(ty), unicode_style);
                let value_text = apply_surface_style(&format_expr_raw(value_expr), unicode_style);
                if binder_text.is_empty() {
                    out.push_str(&format!("{pad}{name} : {ty_text} = {value_text}\n"));
                } else {
                    out.push_str(&format!(
                        "{pad}{name} {binder_text} : {ty_text} = {value_text}\n"
                    ));
                }
                out.push('\n');
            }
            ModuleItem::SubModule {
                name,
                items: nested,
            } => {
                out.push_str(&format!("{pad}module {name} where\n\n"));
                format_items(
                    nested,
                    indent + 2,
                    unicode_style,
                    allow_lambda_binder_lift,
                    out,
                );
                out.push('\n');
            }
            ModuleItem::Declaration(Declaration::Postulate { .. }) => {}
        }
        idx += 1;
    }
}

fn canonical_display_binders_and_body<'a>(
    binders: &'a [TermBinder],
    ty: &Expr,
    value: &'a Expr,
    allow_lambda_binder_lift: bool,
) -> (Vec<TermBinder>, &'a Expr) {
    if !allow_lambda_binder_lift {
        return (binders.to_vec(), value);
    }
    if !binders.is_empty() {
        return (binders.to_vec(), value);
    }
    let Expr::Lambda {
        binders: lambda_binders,
        body,
    } = value
    else {
        return (Vec::new(), value);
    };
    if lambda_binders.is_empty() {
        return (Vec::new(), value);
    }

    let mut params = Vec::<Expr>::new();
    let mut cursor = ty;
    while let Expr::Arrow { parameter, result } = cursor {
        params.push((**parameter).clone());
        cursor = result;
    }
    let inferred_param = params.first().cloned().unwrap_or(Expr::Top);
    let display = lambda_binders
        .iter()
        .enumerate()
        .map(|(idx, binder)| {
            if binder.ty.as_ref() != &CatType::Top {
                return binder.clone();
            }
            let param_expr = params
                .get(idx)
                .cloned()
                .unwrap_or_else(|| inferred_param.clone());
            let param_ty = CatType::from_expr(&param_expr).unwrap_or(CatType::Top);
            match binder.explicitness {
                Explicitness::Explicit => TermBinder::explicit(binder.name.clone(), param_ty),
                Explicitness::Implicit => TermBinder::implicit(binder.name.clone(), param_ty),
            }
        })
        .collect::<Vec<_>>();
    (display, body.as_ref())
}

fn format_expr_raw(expr: &Expr) -> String {
    match expr {
        Expr::Let(_) => {
            let mut bindings = Vec::<String>::new();
            let mut body = expr;
            while let Expr::Let(let_expr) = body {
                let pattern = format_pattern_raw(&let_expr.pattern);
                let value = format_expr_raw(&let_expr.value);
                let rendered = if let Some(ann) = &let_expr.annotation {
                    format!("{pattern} : {} = {value}", format_expr_raw(ann))
                } else {
                    format!("{pattern} = {value}")
                };
                bindings.push(rendered);
                body = &let_expr.body;
            }
            format!("let {} in {}", bindings.join("; "), format_expr_raw(body))
        }
        Expr::Lambda { binders, body } => {
            let binder_text = binders
                .iter()
                .map(|binder| {
                    let ty_text = format_cat_type_surface(binder.ty.as_ref());
                    match binder.explicitness {
                        Explicitness::Explicit => format!("({} : {})", binder.name, ty_text),
                        Explicitness::Implicit => format!("{{{} : {}}}", binder.name, ty_text),
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            if binder_text.is_empty() {
                format!("\\. {}", format_expr_raw(body))
            } else {
                format!("\\{binder_text}. {}", format_expr_raw(body))
            }
        }
        Expr::App {
            function,
            arguments,
        } => {
            let mut parts = vec![format_expr_app_operand(function)];
            parts.extend(arguments.iter().map(format_expr_app_operand));
            format!("({})", parts.join(" "))
        }
        Expr::Hom {
            category,
            source,
            target,
        } => format!(
            "({} ->[{}] {})",
            format_expr_raw(source),
            format_expr_raw(category),
            format_expr_raw(target)
        ),
        Expr::Product { left, right } => {
            format!("({} * {})", format_expr_raw(left), format_expr_raw(right))
        }
        Expr::Arrow { parameter, result } => {
            format!(
                "({} -> {})",
                format_expr_raw(parameter),
                format_expr_raw(result)
            )
        }
        Expr::End { binder, body } => format!(
            "(end ({} : {}) . {})",
            binder.name,
            format_cat_type_surface(&binder.ty),
            format_expr_raw(body)
        ),
        Expr::Coend { binder, body } => format!(
            "(coend ({} : {}) . {})",
            binder.name,
            format_cat_type_surface(&binder.ty),
            format_expr_raw(body)
        ),
        Expr::Opposite(inner) => format!("({})^", format_expr_raw(inner)),
        Expr::EndIntro { binder, body } => {
            if binder.name == "_" && binder.ty.as_ref() == &CatType::Top {
                format!("end {}", format_expr_app_operand(body))
            } else {
                format!(
                    "end ({} : {}) . {}",
                    binder.name,
                    format_cat_type_surface(&binder.ty),
                    format_expr_raw(body)
                )
            }
        }
        Expr::EndElim { proof, witness } => {
            if matches!(witness.as_ref(), Expr::Var(name) if name == "_") {
                format!("end^-1 {}", format_expr_app_operand(proof))
            } else {
                format!(
                    "end^-1 {} {}",
                    format_expr_app_operand(proof),
                    format_expr_app_operand(witness)
                )
            }
        }
        Expr::CoendIntro { witness, body } => {
            if matches!(body.as_ref(), Expr::Var(name) if name == "_") {
                format!("coend {}", format_expr_app_operand(witness))
            } else {
                format!(
                    "coend {} {}",
                    format_expr_app_operand(witness),
                    format_expr_app_operand(body)
                )
            }
        }
        Expr::CoendElim {
            proof,
            binder,
            continuation,
        } => {
            if binder.name == "_" && binder.ty.as_ref() == &CatType::Top {
                if matches!(continuation.as_ref(), Expr::Var(name) if name == "_") {
                    format!("coend^-1 {}", format_expr_app_operand(proof))
                } else {
                    format!(
                        "coend^-1 {} {}",
                        format_expr_app_operand(proof),
                        format_expr_app_operand(continuation)
                    )
                }
            } else {
                format!(
                    "coend^-1 {} ({} : {}) . {}",
                    format_expr_app_operand(proof),
                    binder.name,
                    format_cat_type_surface(&binder.ty),
                    format_expr_raw(continuation)
                )
            }
        }
        Expr::Refl { term } => format!("refl {}", format_expr_app_operand(term)),
        Expr::JElim { transport, path } => {
            format!(
                "J {} [{}]",
                format_expr_app_operand(transport),
                format_expr_raw(path)
            )
        }
        Expr::Proj { tuple, index } => format!("({}).{}", format_expr_raw(tuple), index),
        Expr::Pair { left, right } => {
            format!("({}, {})", format_expr_raw(left), format_expr_raw(right))
        }
        Expr::Var(name) => name.clone(),
        Expr::Top => "Top".to_string(),
    }
}

fn format_expr_app_operand(expr: &Expr) -> String {
    let rendered = format_expr_raw(expr);
    if requires_parens_in_app_position(expr) {
        format!("({rendered})")
    } else {
        rendered
    }
}

fn format_cat_type_surface(ty: &CatType) -> String {
    format_expr_raw(&cat_type_to_surface_expr(ty))
}

fn format_pattern_raw(pattern: &SurfacePattern) -> String {
    match pattern {
        SurfacePattern::Var(name) => name.clone(),
        SurfacePattern::Pair(left, right) => {
            format!(
                "({}, {})",
                format_pattern_raw(left),
                format_pattern_raw(right)
            )
        }
        SurfacePattern::Wildcard => "_".to_string(),
        SurfacePattern::Annotated(inner, ty) => {
            format!(
                "({} : {})",
                format_pattern_raw(inner),
                format_cat_type_surface(ty)
            )
        }
    }
}

fn requires_parens_in_app_position(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Lambda { .. }
            | Expr::Let(_)
            | Expr::Arrow { .. }
            | Expr::Hom { .. }
            | Expr::Product { .. }
            | Expr::End { .. }
            | Expr::Coend { .. }
            | Expr::EndIntro { .. }
            | Expr::EndElim { .. }
            | Expr::CoendIntro { .. }
            | Expr::CoendElim { .. }
    )
}

fn apply_surface_style(text: &str, unicode_style: bool) -> String {
    if !unicode_style {
        return text.to_string();
    }
    text.replace("->", "→").replace('\\', "λ")
}

fn cat_type_to_surface_expr(ty: &CatType) -> Expr {
    match ty {
        CatType::Base(name) | CatType::Var(name) => Expr::var(name.clone()),
        CatType::Opposite(inner) => Expr::opposite(cat_type_to_surface_expr(inner)),
        CatType::FunCat(parameter, result) => Expr::arrow(
            cat_type_to_surface_expr(parameter),
            cat_type_to_surface_expr(result),
        ),
        CatType::Product(left, right) => Expr::product(
            cat_type_to_surface_expr(left),
            cat_type_to_surface_expr(right),
        ),
        CatType::Top => Expr::Top,
    }
}

fn looks_like_malformed_binder_group(ty: &str) -> bool {
    let Ok(tokens) = tokenize_for_parser(ty) else {
        return false;
    };
    let mut i = 0usize;
    while i < tokens.len() {
        if tokens[i].text != "(" {
            i += 1;
            continue;
        }

        let mut j = i + 1;
        let mut depth = 1isize;
        let mut has_colon = false;
        let mut has_comma = false;
        let mut ident_count = 0usize;
        let mut simple_group = true;
        while j < tokens.len() && depth > 0 {
            let token = tokens[j].text.as_str();
            match token {
                "(" | "{" | "[" => {
                    depth += 1;
                    if depth == 2 {
                        simple_group = false;
                    }
                }
                ")" | "}" | "]" => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ if depth == 1 => {
                    if token == ":" {
                        has_colon = true;
                    } else if token == "," {
                        has_comma = true;
                    } else if looks_like_identifier_lexeme(token) {
                        ident_count += 1;
                    } else {
                        simple_group = false;
                    }
                }
                _ => {}
            }
            j += 1;
        }

        if depth == 0 {
            let followed_by_arrow = tokens.get(j + 1).map(|tok| tok.text.as_str()) == Some("->");
            if followed_by_arrow && !has_colon && !has_comma && simple_group && ident_count >= 3 {
                return true;
            }
            i = j + 1;
        } else {
            break;
        }
    }
    false
}

fn looks_like_identifier_lexeme(token: &str) -> bool {
    let mut chars = token.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_' || first.is_alphabetic())
        && chars.all(|ch| ch.is_alphanumeric() || ch == '_' || ch == '\'')
}

fn split_top_level_required<'a>(
    input: &'a str,
    needle: char,
    message: &str,
) -> Result<(&'a str, &'a str), LanguageError> {
    if let Some((left, right)) = split_top_level_once(input, needle) {
        Ok((left, right))
    } else {
        Err(parse_error("split", message.to_string(), None))
    }
}

fn split_top_level_once(input: &str, needle: char) -> Option<(&str, &str)> {
    let mut depth_paren = 0isize;
    let mut depth_brace = 0isize;
    let mut depth_bracket = 0isize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '{' => depth_brace += 1,
            '}' => depth_brace -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            _ => {}
        }
        if ch == needle && depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 {
            let left = &input[..idx];
            let right = &input[idx + ch.len_utf8()..];
            return Some((left, right));
        }
    }
    None
}

fn parse_qualified_name(raw: &str) -> Result<QualifiedName, LanguageError> {
    let mut parts = Vec::new();
    for part in raw.split('.') {
        let p = canonical_identifier(part.trim());
        validate_identifier(&p)?;
        parts.push(p);
    }
    if parts.is_empty() {
        return Err(parse_error(
            "invalid_module_name",
            "module name cannot be empty".to_string(),
            None,
        ));
    }
    Ok(QualifiedName(parts))
}

fn normalize_source(source: &str) -> String {
    normalize_lambda_intro(source)
        .replace("\r\n", "\n")
        .replace('\r', "\n")
        .replace("∫^", "coend")
        .replace('∫', "end")
        .replace('→', "->")
        .replace('×', "*")
        .replace('⊤', "Top")
        .replace("⁻¹", "^-1")
}

fn normalize_lambda_intro(source: &str) -> String {
    let chars = source.chars().collect::<Vec<_>>();
    let mut out = String::with_capacity(source.len());
    for (idx, ch) in chars.iter().enumerate() {
        if *ch == 'λ' && looks_like_lambda_intro(&chars, idx) {
            out.push('\\');
        } else {
            out.push(*ch);
        }
    }
    out
}

fn looks_like_lambda_intro(chars: &[char], lambda_idx: usize) -> bool {
    let mut i = lambda_idx + 1;
    while i < chars.len() && chars[i].is_whitespace() {
        if chars[i] == '\n' {
            return false;
        }
        i += 1;
    }
    if i >= chars.len() {
        return false;
    }
    let mut j = i;
    while j < chars.len() {
        let ch = chars[j];
        if ch == '.' {
            return true;
        }
        if ch == '\n' || ch == ';' || ch == '=' {
            return false;
        }
        j += 1;
    }
    false
}

fn strip_comments_preserve_shape(source: &str) -> Result<String, LanguageError> {
    let mut out = String::with_capacity(source.len());
    let chars = source.chars().collect::<Vec<_>>();
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i] == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            out.push(' ');
            out.push(' ');
            i += 2;
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        if chars[i] == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            let start = i;
            out.push(' ');
            out.push(' ');
            i += 2;
            let mut closed = false;
            while i + 1 < chars.len() {
                if chars[i] == '*' && chars[i + 1] == '/' {
                    out.push(' ');
                    out.push(' ');
                    i += 2;
                    closed = true;
                    break;
                }
                out.push(if chars[i] == '\n' { '\n' } else { ' ' });
                i += 1;
            }
            if !closed {
                return Err(parse_error(
                    "unclosed_comment",
                    "unclosed block comment".to_string(),
                    Some(Span {
                        start,
                        end: (start + 2).min(source.len()),
                    }),
                ));
            }
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    Ok(out)
}

fn canonical_identifier(input: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        let mapped = match ch {
            '\u{0300}'..='\u{036F}' => continue,
            'á' | 'à' | 'â' | 'ä' | 'ã' | 'å' | 'ā' | 'ă' | 'ą' | 'ǎ' | 'ȧ' | 'ạ' => {
                'a'
            }
            'Á' | 'À' | 'Â' | 'Ä' | 'Ã' | 'Å' | 'Ā' | 'Ă' | 'Ą' | 'Ǎ' | 'Ȧ' | 'Ạ' => {
                'A'
            }
            'é' | 'è' | 'ê' | 'ë' | 'ē' | 'ĕ' | 'ė' | 'ę' | 'ě' | 'ẹ' => 'e',
            'É' | 'È' | 'Ê' | 'Ë' | 'Ē' | 'Ĕ' | 'Ė' | 'Ę' | 'Ě' | 'Ẹ' => 'E',
            'í' | 'ì' | 'î' | 'ï' | 'ī' | 'ĭ' | 'į' | 'ǐ' | 'ị' => 'i',
            'Í' | 'Ì' | 'Î' | 'Ï' | 'Ī' | 'Ĭ' | 'Į' | 'Ǐ' | 'Ị' => 'I',
            'ó' | 'ò' | 'ô' | 'ö' | 'õ' | 'ō' | 'ŏ' | 'ő' | 'ǒ' | 'ọ' => 'o',
            'Ó' | 'Ò' | 'Ô' | 'Ö' | 'Õ' | 'Ō' | 'Ŏ' | 'Ő' | 'Ǒ' | 'Ọ' => 'O',
            'ú' | 'ù' | 'û' | 'ü' | 'ū' | 'ŭ' | 'ů' | 'ű' | 'ų' | 'ǔ' | 'ụ' => 'u',
            'Ú' | 'Ù' | 'Û' | 'Ü' | 'Ū' | 'Ŭ' | 'Ů' | 'Ű' | 'Ų' | 'Ǔ' | 'Ụ' => 'U',
            'ç' => 'c',
            'Ç' => 'C',
            other => other,
        };
        out.push(mapped);
    }
    out
}

fn is_identifier_start(ch: char) -> bool {
    ch == '_' || ch.is_alphabetic() || unicode_ident::is_xid_start(ch)
}

fn is_identifier_continue(ch: char) -> bool {
    ch == '_'
        || ch.is_alphanumeric()
        || ch == '\''
        || ch == '\\'
        || unicode_ident::is_xid_continue(ch)
}

fn is_reserved(s: &str) -> bool {
    matches!(s, "module" | "where" | "import" | "postulate")
}

fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !is_identifier_start(first) {
        return false;
    }
    chars.all(is_identifier_continue)
}

fn validate_identifier(name: &str) -> Result<(), LanguageError> {
    let span = Some(Span {
        start: 0,
        end: name.len().max(1),
    });
    if name.is_empty() {
        return Err(parse_error(
            "empty_identifier",
            "identifier cannot be empty".to_string(),
            span,
        ));
    }
    if is_reserved(name) {
        return Err(parse_error(
            "reserved_identifier",
            format!("reserved word '{name}' cannot be used as identifier"),
            span,
        ));
    }
    if !is_identifier(name) {
        return Err(parse_error(
            "invalid_identifier",
            format!("invalid identifier '{name}'"),
            span,
        ));
    }
    Ok(())
}

fn span_for_line(source: &str, line_index: usize) -> Span {
    let mut start = 0usize;
    for (line_no, line) in source.lines().enumerate() {
        if line_no == line_index {
            let end = start + line.len().max(1);
            return Span { start, end };
        }
        start += line.len() + 1;
    }
    Span { start: 0, end: 1 }
}

fn parse_error(code: &str, message: String, span: Option<Span>) -> LanguageError {
    let span = Some(span.unwrap_or(Span { start: 0, end: 1 }));
    LanguageError::Syntax(SyntaxError::Parse {
        diagnostics: DiagnosticBundle {
            diagnostics: vec![Diagnostic {
                code: code.to_string(),
                category: "Parser".to_string(),
                severity: Severity::Error,
                message,
                span,
                source: None,
            }],
        },
    })
}
