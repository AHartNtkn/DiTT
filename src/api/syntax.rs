use super::*;

pub trait Lexer {
    fn lex(&self, source: &str) -> Result<Vec<Token>, LanguageError>;
}

pub trait Parser {
    fn parse_module(&self, source: &str) -> Result<SurfaceModule, LanguageError>;
    /// Parse an expression snippet (module header optional).
    fn parse_expr(&self, source: &str) -> Result<Expr, LanguageError>;
}

pub trait Formatter {
    /// Format a surface module to canonical text.
    /// Returns `Err` if the module contains malformed structure that prevents formatting.
    fn format_module(&self, module: &SurfaceModule) -> Result<String, LanguageError>;
}

pub trait AstEquivalence {
    fn alpha_equivalent_modules(
        &self,
        left: &SurfaceModule,
        right: &SurfaceModule,
    ) -> Result<bool, LanguageError>;
}
