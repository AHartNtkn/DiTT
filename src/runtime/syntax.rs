use crate::api::*;

#[derive(Debug, Default)]
pub struct SyntaxEngine {
    _private: (),
}

impl Lexer for SyntaxEngine {
    fn lex(&self, _source: &str) -> Result<Vec<Token>, LanguageError> {
        unimplemented!("lexer")
    }
}

impl Parser for SyntaxEngine {
    fn parse_module(&self, _source: &str) -> Result<SurfaceModule, LanguageError> {
        unimplemented!("parser.parse_module")
    }

    fn parse_expr(&self, _source: &str) -> Result<Expr, LanguageError> {
        unimplemented!("parser.parse_expr")
    }
}

impl Formatter for SyntaxEngine {
    fn format_module(&self, _module: &SurfaceModule) -> Result<String, LanguageError> {
        unimplemented!("formatter")
    }
}

impl AstEquivalence for SyntaxEngine {
    fn alpha_equivalent_modules(
        &self,
        _left: &SurfaceModule,
        _right: &SurfaceModule,
    ) -> Result<bool, LanguageError> {
        unimplemented!("ast_equivalence")
    }
}
