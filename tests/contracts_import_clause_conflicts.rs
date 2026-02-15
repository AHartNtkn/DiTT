use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn using_and_hiding_overlap_is_rejected() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Import.Overlap where
import Std.Category using (id) hiding (id)
postulate C : Cat
x : C = x
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn invalid_renaming_source_is_rejected() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Import.BadRenaming where
import Std.Category renaming (missing to id)
postulate C : Cat
x : C = x
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn duplicate_import_aliases_are_rejected() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Import.DuplicateAlias where
import A as X
import B as X
postulate C : Cat
x : C = x
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn ambiguous_qualified_reference_is_rejected() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Import.AmbiguousQualified where
import A as X using (id)
import B as X using (id)
postulate C : Cat
u : C = X.id
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}
