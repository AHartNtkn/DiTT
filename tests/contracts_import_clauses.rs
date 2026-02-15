mod common;

use common::conformance::read_fixture;
use common::engines::compile_module;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

#[test]
fn composed_import_clauses_parse_and_typecheck() {
    let source = read_fixture("conformance/syntax/positive/import_clauses_valid.ditt");
    let _typed = compile_module(&source);
}

#[test]
fn import_clause_entries_are_name_only() {
    let syntax = SyntaxEngine::default();
    let source = read_fixture("conformance/syntax/negative/import_clauses_invalid_item.ditt");
    let err = syntax.parse_module(&source).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
    }
}

#[test]
fn import_alias_requires_alias_name() {
    let syntax = SyntaxEngine::default();
    let source = read_fixture("conformance/syntax/negative/import_alias_missing_name.ditt");
    let err = syntax.parse_module(&source).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}
