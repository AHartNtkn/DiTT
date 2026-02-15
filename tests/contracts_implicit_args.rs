mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn implicit_arguments_are_inferred_when_omitted() {
    let source = r#"
module Implicit.Infer where

postulate C : Cat
id : {x : C} -> C = \{x}. x
use : (y : C) -> C = \y. id
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let use_term = Expr::var("use");
    let ty = semantics.infer_term_type(&typed, &use_term).unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn implicit_arguments_and_explicit_arguments_agree_definitionally() {
    let source = r#"
module Implicit.ExplicitAgreement where

postulate C : Cat
id : {x : C} -> C = \{x}. x
a : (y : C) -> C = \y. id
b : (y : C) -> C = \y. id {x = y}
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let a = Expr::var("a");
    let b = Expr::var("b");
    let n_a = semantics.normalize_term(&typed, &a).unwrap();
    let n_b = semantics.normalize_term(&typed, &b).unwrap();
    assert_eq!(n_a.structure().to_string(), n_b.structure().to_string());
}

#[test]
fn let_binding_alpha_renaming_preserves_equivalence() {
    let syntax = SyntaxEngine::default();
    let left = r#"
module Implicit.LetAlpha where

postulate C : Cat
postulate a : C
probe : C = let x : C = a in x
"#;
    let right = r#"
module Implicit.LetAlpha where

postulate C : Cat
postulate a : C
probe : C = let y : C = a in y
"#;
    let left_ast = syntax.parse_module(left).unwrap();
    let right_ast = syntax.parse_module(right).unwrap();
    let eq = syntax
        .alpha_equivalent_modules(&left_ast, &right_ast)
        .unwrap();
    assert!(eq);
}

#[test]
fn ambiguous_implicit_argument_resolution_returns_structured_diagnostics() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Implicit.Ambiguous where

postulate C : Cat
choose : {x : C} -> {y : C} -> C = \{x} {y}. x
bad : (z : C) -> C = \z. choose
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
fn partial_explicit_implicit_instantiation_matches_fully_explicit_form() {
    let source = r#"
module Implicit.PartialExplicit where

postulate C : Cat
apply : {x : C} -> (f : (z : C) -> C) -> C = \{x} f. f x
id : (z : C) -> C = \z. z
u_partial : {x : C} -> C = \{x}. apply id
u_explicit : {x : C} -> C = \{x}. apply {x = x} id
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let partial = Expr::var("u_partial");
    let explicit = Expr::var("u_explicit");
    let n_partial = semantics.normalize_term(&typed, &partial).unwrap();
    let n_explicit = semantics.normalize_term(&typed, &explicit).unwrap();
    assert_eq!(
        n_partial.structure().to_string(),
        n_explicit.structure().to_string()
    );
}

#[test]
fn multi_implicit_inference_is_coherent_with_fully_annotated_application() {
    let source = r#"
module Implicit.MultiInference where

postulate C : Cat
pick_left : {x : C} -> {y : C} -> C = \{x} {y}. x
inferred : {x : C} -> {y : C} -> C = \{x} {y}. pick_left
annotated : {x : C} -> {y : C} -> C = \{x} {y}. pick_left {x = x} {y = y}
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let inferred = Expr::var("inferred");
    let annotated = Expr::var("annotated");
    assert_eq!(
        semantics.infer_term_type(&typed, &inferred).unwrap(),
        semantics.infer_term_type(&typed, &annotated).unwrap()
    );
    let n_inferred = semantics.normalize_term(&typed, &inferred).unwrap();
    let n_annotated = semantics.normalize_term(&typed, &annotated).unwrap();
    assert_eq!(
        n_inferred.structure().to_string(),
        n_annotated.structure().to_string()
    );
}

#[test]
fn cross_module_implicit_name_ambiguity_is_reported_at_check_boundary() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module Implicit.CrossModuleAmbiguous where

import A using (id)
import B using (id)
postulate C : Cat
bad : (z : C) -> C = \z. id {x = z}
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
fn kernel_derive_judgment_rejects_implicit_binders_without_elaboration() {
    let semantics = SemanticEngine::default();
    let typed = TypedModule {
        name: None,
        imports: vec![],
        declarations: vec![
            TypedDeclaration {
                declaration: Declaration::Postulate {
                    name: "C".to_string(),
                    ty: Expr::var("Cat"),
                },
                elaborated_type: ElaboratedType::Cat(CatType::Var("Cat".into())),
            },
            TypedDeclaration {
                declaration: Declaration::Definition {
                    name: "bad_kernel_term".to_string(),
                    binders: vec![],
                    ty: Expr::arrow(Expr::var("C"), Expr::var("C")),
                    value: Expr::lambda(
                        vec![TermBinder::explicit("x", CatType::Var("C".into()))],
                        Expr::var("x"),
                    ),
                },
                elaborated_type: ElaboratedType::Cat(CatType::FunCat(
                    Box::new(CatType::Var("C".into())),
                    Box::new(CatType::Var("C".into())),
                )),
            },
        ],
    };

    let result = semantics.check(
        &typed,
        &CheckJudgment::TermTyping(
            Context::default(),
            Term::var("bad_kernel_term"),
            CatType::Top,
        ),
    );
    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "kernel implicit rejection must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}
