use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn parser_rejects_effect_syntax_from_surface_language() {
    let syntax = SyntaxEngine::default();
    let source = r#"
module Effects.ParserBoundary where
main : IO Unit = readFile "/tmp/in"
"#;
    let bundle = syntax.parse_module(source).unwrap_err().into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
    }
}

#[test]
fn typechecker_rejects_effect_like_primitives_even_if_parser_accepts_tokens() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Effects.TypeBoundary where
postulate C : Cat
bad : C = open "/etc/passwd"
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.message.is_empty());
    }
}
