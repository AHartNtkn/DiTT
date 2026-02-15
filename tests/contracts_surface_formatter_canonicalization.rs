mod common;

use common::support::assert_format_contracts;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

fn format_source(syntax: &SyntaxEngine, source: &str) -> String {
    let module = syntax.parse_module(source).unwrap();
    syntax.format_module(&module).unwrap()
}

#[test]
fn formatter_canonicalizes_consecutive_postulates_into_block() {
    let syntax = SyntaxEngine::default();
    let source = r#"
module Fmt.Postulates where

postulate C : Cat
postulate D : Cat
id (x : C) : C = x
"#;
    let out = format_source(&syntax, source);
    assert_format_contracts(&out);
    assert!(out.contains("postulate\n"));
    assert!(!out.contains("postulate C : Cat\npostulate D : Cat"));
}

#[test]
fn formatter_canonicalizes_grouped_binders_to_one_per_group() {
    let syntax = SyntaxEngine::default();
    let source = r#"
module Fmt.Binders where

postulate C : Cat
pair : (x y : C) -> C = \x y. x
"#;
    let out = format_source(&syntax, source);
    assert_format_contracts(&out);
    assert!(out.contains("(x : C) (y : C)"));
}

#[test]
fn formatter_canonicalizes_nested_let_to_multi_binding_form() {
    let syntax = SyntaxEngine::default();
    let source = r#"
module Fmt.Let where

postulate C : Cat
id (x : C) : C = let y = x in let z = y in z
"#;
    let out = format_source(&syntax, source);
    assert_format_contracts(&out);
    assert!(out.contains("let"));
    assert!(out.contains(";"));
}

#[test]
fn formatter_preserves_ascii_vs_unicode_surface_style() {
    let syntax = SyntaxEngine::default();
    let ascii = "module Fmt.Ascii where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n";
    let unicode = "module Fmt.Unicode where\npostulate C : Cat\nid : (x : C) → C = λx. x\n";

    let a = format_source(&syntax, ascii);
    let u = format_source(&syntax, unicode);

    assert!(a.contains("->") || a.contains("\\"));
    assert!(!a.contains("→"));
    assert!(!a.contains("λ"));

    assert!(u.contains("→") || u.contains("λ"));
}
