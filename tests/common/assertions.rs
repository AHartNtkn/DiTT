#![allow(dead_code)]

use ditt_lang::api::*;
use ditt_lang::runtime::SemanticEngine;

pub fn assert_def_equal(
    semantics: &SemanticEngine,
    module: &TypedModule,
    left: &str,
    right: &str,
    context: &str,
) {
    let result = semantics
        .definitionally_equal(module, &Expr::var(left), &Expr::var(right))
        .unwrap();
    assert!(result, "{context}");
}
