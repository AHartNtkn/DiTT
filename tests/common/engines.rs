#![allow(dead_code)]

use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

pub fn compile_module(source: &str) -> TypedModule {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let parsed = syntax.parse_module(source).unwrap();
    semantics.elaborate_module(&parsed).unwrap()
}

pub fn compile_with_engines(source: &str) -> (SyntaxEngine, SemanticEngine, TypedModule) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let parsed = syntax.parse_module(source).unwrap();
    let typed = semantics.elaborate_module(&parsed).unwrap();
    (syntax, semantics, typed)
}
