mod common;

use common::engines::compile_with_engines;
use common::support::invocation;
use ditt_lang::api::*;
use ditt_lang::runtime::{SyntaxEngine, ToolingEngine};
use serde_json::Value;

#[test]
fn api_cli_and_lsp_agree_on_valid_module_semantics() {
    let source = r#"
module Main where
postulate C : Cat
refl_intro (x : C) : x ->[C] x = refl x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let mut tooling = ToolingEngine::default();
    let api_result = semantics.check(
        &typed,
        &CheckJudgment::TermTyping(Context::default(), Term::var("refl_intro"), CatType::Top),
    );

    let cli = tooling
        .invoke(&invocation(&["check", "--json"], source))
        .unwrap();

    let uri = DocumentUri("file:///tmp/consistency_valid.ditt".to_string());
    tooling.open_document(&uri, source).unwrap();
    let lsp = tooling.diagnostics(&uri).unwrap();

    assert!(
        api_result.is_ok(),
        "API must report derivable for valid module"
    );
    assert_eq!(cli.exit_code, 0);
    let cli_json = cli
        .json
        .as_ref()
        .expect("check --json must emit machine-readable payload");
    let json: Value = serde_json::from_str(cli_json).expect("cli json must be valid");
    assert_eq!(json.get("status").and_then(Value::as_str), Some("ok"));
    assert!(lsp.diagnostics.is_empty());
}

#[test]
fn api_cli_and_lsp_agree_on_invalid_module_semantics() {
    let syntax = SyntaxEngine::default();
    let mut tooling = ToolingEngine::default();
    let source = "module Main where\nbad =\n";

    let parser_bundle = syntax.parse_module(source).unwrap_err().into_diagnostics();
    let cli = tooling
        .invoke(&invocation(&["check", "--json"], source))
        .unwrap();

    let uri = DocumentUri("file:///tmp/consistency_invalid.ditt".to_string());
    tooling.open_document(&uri, source).unwrap();
    let lsp = tooling.diagnostics(&uri).unwrap();

    assert!(!parser_bundle.diagnostics.is_empty());
    assert_ne!(cli.exit_code, 0);
    let cli_json = cli
        .json
        .as_ref()
        .expect("check --json must emit machine-readable payload");
    let json: Value = serde_json::from_str(cli_json).expect("cli json must be valid");
    assert_eq!(json.get("status").and_then(Value::as_str), Some("error"));
    assert!(!lsp.diagnostics.is_empty());
}
