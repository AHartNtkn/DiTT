mod common;

use std::collections::BTreeSet;

use common::conformance::canonical_severity;
use ditt_lang::api::*;
use ditt_lang::runtime::ToolingEngine;

type DiagnosticKey = (String, String, Option<usize>, Option<usize>, String);

fn modules() -> Vec<ModuleText> {
    vec![
        ModuleText {
            name: "A".to_string(),
            source: "module A where".to_string(),
        },
        ModuleText {
            name: "B".to_string(),
            source: "module B where\nimport A".to_string(),
        },
        ModuleText {
            name: "Main".to_string(),
            source: "module Main where\nimport B".to_string(),
        },
    ]
}

fn diagnostic_signature_set(bundle: &DiagnosticBundle) -> BTreeSet<DiagnosticKey> {
    bundle
        .diagnostics
        .iter()
        .map(|d| {
            (
                d.category.clone(),
                canonical_severity(&d.severity).to_string(),
                d.span.map(|s| s.start),
                d.span.map(|s| s.end),
                d.message.clone(),
            )
        })
        .collect()
}

#[test]
fn module_graph_is_acyclic_for_linear_import_chain() {
    let tooling = ToolingEngine::default();
    let graph = tooling.build_graph(&modules()).unwrap();

    assert!(!graph.has_cycle());
}

#[test]
fn lsp_hover_and_completions_are_available_after_document_open() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/main.ditt".to_string());
    tooling
        .open_document(
            &uri,
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        )
        .unwrap();

    let hover = tooling
        .hover(
            &uri,
            Position {
                line: 1,
                character: 5,
            },
        )
        .unwrap();
    let completions = tooling
        .completions(
            &uri,
            Position {
                line: 1,
                character: 5,
            },
        )
        .unwrap();

    assert!(hover.is_some());
    assert!(!completions.is_empty());
}

#[test]
fn lsp_definition_rename_and_semantic_tokens_are_available() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/defs.ditt".to_string());
    tooling
        .open_document(
            &uri,
            "module Main where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\nuse : (x : C) -> C = id x\n",
        )
        .unwrap();

    let position = Position {
        line: 3,
        character: 11,
    };
    let def = tooling.definition(&uri, position).unwrap();
    assert!(def.is_some());

    let edit = tooling.rename_symbol(&uri, position, "ident").unwrap();
    assert!(!edit.changes.is_empty());

    let tokens = tooling.semantic_tokens(&uri).unwrap();
    assert!(!tokens.is_empty());
    for token in tokens {
        assert!(token.length > 0);
        assert!(matches!(
            token.token_type,
            SemanticTokenType::Keyword
                | SemanticTokenType::Type
                | SemanticTokenType::Variable
                | SemanticTokenType::Operator
                | SemanticTokenType::Literal
                | SemanticTokenType::Comment
                | SemanticTokenType::Function
                | SemanticTokenType::Module
                | SemanticTokenType::Predicate
        ));
    }
}

#[test]
fn diagnostics_are_stable_under_repeated_queries() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/repeat.ditt".to_string());
    tooling
        .open_document(
            &uri,
            "module Repeat where\npostulate C : Cat\nid : (x : C) -> C = \\x. x\n",
        )
        .unwrap();

    for line in [0, 1, 2, 5, 10] {
        for character in [0, 1, 4, 8, 15] {
            let _ = tooling.hover(&uri, Position { line, character }).unwrap();
            let first = tooling.diagnostics(&uri).unwrap();
            let second = tooling.diagnostics(&uri).unwrap();
            assert_eq!(
                diagnostic_signature_set(&first),
                diagnostic_signature_set(&second),
                "diagnostic content must remain stable regardless of emission order"
            );
        }
    }
}

#[test]
fn diagnostics_spans_remain_valid_after_incremental_edits() {
    let mut tooling = ToolingEngine::default();
    let uri = DocumentUri("file:///tmp/span_stability.ditt".to_string());
    tooling
        .open_document(&uri, "module S where\nbad =\n")
        .unwrap();
    let before = tooling.diagnostics(&uri).unwrap();

    tooling
        .change_document(&uri, "module S where\n\nbad =\nalso_bad =\n")
        .unwrap();
    let after = tooling.diagnostics(&uri).unwrap();

    for d in before
        .diagnostics
        .into_iter()
        .chain(after.diagnostics.into_iter())
    {
        if let Some(span) = d.span {
            assert!(span.start <= span.end);
        }
    }
}
