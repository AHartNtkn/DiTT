use std::collections::BTreeMap;

use ditt_lang::api::*;
use ditt_lang::runtime::{SyntaxEngine, ToolingEngine};

#[test]
fn parser_results_are_invariant_under_lf_and_crlf_line_endings() {
    let syntax = SyntaxEngine::default();
    let lf = "module M where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";
    let crlf = lf.replace('\n', "\r\n");

    let lf_ast = syntax.parse_module(lf).unwrap();
    let crlf_ast = syntax.parse_module(&crlf).unwrap();
    assert_eq!(lf_ast, crlf_ast);
}

#[test]
fn parser_treats_unicode_normalization_variants_equivalently() {
    let syntax = SyntaxEngine::default();
    let composed = "module Café where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";
    let decomposed = "module Cafe\u{301} where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";

    let a = syntax.parse_module(composed).unwrap();
    let b = syntax.parse_module(decomposed).unwrap();
    assert_eq!(a, b);
}

#[test]
fn cli_machine_output_is_locale_timezone_independent() {
    let tooling = ToolingEngine::default();
    let source = "module Main where\npostulate C : Cat\nt : (x : C) -> C = \\x. x\n";

    let mut env_a = BTreeMap::new();
    env_a.insert("LC_ALL".to_string(), "en_US.UTF-8".to_string());
    env_a.insert("TZ".to_string(), "UTC".to_string());

    let mut env_b = BTreeMap::new();
    env_b.insert("LC_ALL".to_string(), "tr_TR.UTF-8".to_string());
    env_b.insert("TZ".to_string(), "America/New_York".to_string());

    let a = tooling
        .invoke(&CliInvocation {
            args: vec!["check".to_string(), "--json".to_string()],
            stdin: source.to_string(),
            env: env_a,
        })
        .unwrap();
    let b = tooling
        .invoke(&CliInvocation {
            args: vec!["check".to_string(), "--json".to_string()],
            stdin: source.to_string(),
            env: env_b,
        })
        .unwrap();

    assert_eq!(a, b);
}

#[test]
fn lsp_uri_path_separator_variants_are_handled_equivalently() {
    let mut tooling = ToolingEngine::default();
    let posix = DocumentUri("file:///workspace/project/main.ditt".to_string());
    let windows = DocumentUri("file:///C:/workspace/project/main.ditt".to_string());
    tooling
        .open_document(
            &posix,
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        )
        .unwrap();
    tooling
        .open_document(
            &windows,
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        )
        .unwrap();

    let d1 = tooling.diagnostics(&posix).unwrap();
    let d2 = tooling.diagnostics(&windows).unwrap();
    assert_eq!(d1, d2);
}
