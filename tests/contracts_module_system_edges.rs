mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine, ToolingEngine};

#[test]
fn duplicate_module_names_are_rejected() {
    let tooling = ToolingEngine::default();
    let modules = vec![
        ModuleText {
            name: "Main".to_string(),
            source: "module Main where".to_string(),
        },
        ModuleText {
            name: "Main".to_string(),
            source: "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x".to_string(),
        },
    ];
    let err = tooling.build_graph(&modules).unwrap_err();
    assert!(
        !err.diagnostics().diagnostics.is_empty(),
        "duplicate module names must be rejected with diagnostics"
    );
}

#[test]
fn import_cycle_is_detected() {
    let tooling = ToolingEngine::default();
    let modules = vec![
        ModuleText {
            name: "A".to_string(),
            source: "module A where\nimport B".to_string(),
        },
        ModuleText {
            name: "B".to_string(),
            source: "module B where\nimport A".to_string(),
        },
    ];
    let graph = tooling.build_graph(&modules).unwrap();
    assert!(graph.has_cycle(), "import cycle must be detected");
}

#[test]
fn ambiguous_import_bindings_are_reported_as_diagnostics() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Main where
import A as X
import B as X
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert!(!diagnostic.category.is_empty());
        assert_eq!(diagnostic.severity, Severity::Error);
    }
}

#[test]
fn local_modules_support_qualified_access_without_opening_inner_scope() {
    let source = r#"
module LocalModules.Qualified where

postulate C : Cat

module Ops where
  id : (x : C) -> C = \x. x

use : (x : C) -> C = \x. Ops.id x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let term = Expr::var("use");
    let ty = semantics.infer_term_type(&typed, &term).unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn local_module_bindings_do_not_leak_unqualified_into_parent_scope() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module LocalModules.NoLeak where

postulate C : Cat

module Ops where
  id : (x : C) -> C = \x. x

bad : (x : C) -> C = \x. id x
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
        assert!(!diagnostic.message.is_empty());
    }
}

#[test]
fn local_module_shadowing_is_resolved_by_scope_and_qualification() {
    let source = r#"
module LocalModules.Shadowing where

postulate C : Cat

id : (x : C) -> C = \x. x

module Ops where
  id : (x : C) -> C = \x. x

top : (x : C) -> C = \x. id x
qualified : (x : C) -> C = \x. Ops.id x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let top = Expr::var("top");
    let qualified = Expr::var("qualified");
    assert_eq!(
        semantics.infer_term_type(&typed, &top).unwrap(),
        semantics.infer_term_type(&typed, &qualified).unwrap()
    );
    let n1 = semantics.normalize_term(&typed, &top).unwrap();
    let n2 = semantics.normalize_term(&typed, &qualified).unwrap();
    assert_eq!(n1, n2);
}

#[test]
fn duplicate_local_module_names_in_same_scope_are_rejected() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module LocalModules.DuplicateInner where

module Inner where
  postulate C : Cat

module Inner where
  postulate D : Cat
"#;
    let parsed = syntax.parse_module(source).unwrap();
    let err = semantics.elaborate_module(&parsed).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
    }
}
