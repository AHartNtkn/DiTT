mod common;

use common::engines::compile_with_engines;
use common::support::directed_theory_module;
use ditt_lang::api::*;
use ditt_lang::runtime::{SyntaxEngine, ToolingEngine};

#[test]
fn parser_enforces_parse_limits_with_structured_timeout_or_budget_errors() {
    let syntax = SyntaxEngine::default();
    let source = "module M where\n".repeat(1000);
    let err = syntax.parse_module(&source).unwrap_err();

    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn evaluator_reports_structured_diagnostics_for_non_executable_term() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let term = Expr::var("non_terminating_candidate");
    let err = semantics.evaluate_term(&typed, &term).unwrap_err();

    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn cancellation_contract_for_long_running_lsp_request() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/long.ditt".to_string());
    tooling
        .open_document(&uri, "module M where\nhuge = (...)\n")
        .unwrap();
    tooling.cancel(RequestId::from(7)).unwrap();
    let diagnostics = tooling.diagnostics(&uri).unwrap();
    for diagnostic in diagnostics.diagnostics {
        assert!(!diagnostic.category.is_empty());
        assert!(!diagnostic.message.is_empty());
        if let Some(span) = diagnostic.span {
            assert!(span.start <= span.end);
        }
    }
}
