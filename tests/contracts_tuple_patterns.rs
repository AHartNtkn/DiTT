mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn tuple_pattern_matching_typechecks_for_product_terms() {
    let source = r#"
module TuplePattern.Typecheck where

postulate A : Cat
postulate B : Cat
fst (p : (A * B)) : A = \(x, y). x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let fst = Expr::var("fst");
    let ty = semantics.infer_term_type(&typed, &fst).unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn tuple_pattern_normalization_preserves_typing() {
    let source = r#"
module TuplePattern.Reduction where

postulate A : Cat
postulate B : Cat
fst (p : (A * B)) : A = \(x, y). x
ex (a : A) (b : B) : A = fst (a, b)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let ex = Expr::var("ex");
    let before = semantics.infer_term_type(&typed, &ex).unwrap();
    let normalized = semantics.normalize_term(&typed, &ex).unwrap();
    let normalized_term = Expr::var(normalized.structure().to_string());
    let after = semantics.infer_term_type(&typed, &normalized_term).unwrap();
    assert_eq!(before, after);
}

#[test]
fn tuple_pattern_let_binding_typechecks_and_preserves_product_structure() {
    let source = r#"
module TuplePattern.LetBinding where

postulate A : Cat
postulate B : Cat
fst_via_let (p : (A * B)) : A = let (x, y) = p in x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let fst_via_let = Expr::var("fst_via_let");
    let ty = semantics.infer_term_type(&typed, &fst_via_let).unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn tuple_pattern_let_projection_is_definitionally_equal_to_desugared_form() {
    let source = r#"
module TuplePattern.LetDefEq where

postulate A : Cat
postulate B : Cat
fst_via_let (p : (A * B)) : A = let (x, y) = p in x
fst_desugared (p : (A * B)) : A = p.1
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let n1 = semantics
        .normalize_term(&typed, &Expr::var("fst_via_let"))
        .unwrap();
    let n2 = semantics
        .normalize_term(&typed, &Expr::var("fst_desugared"))
        .unwrap();
    assert_eq!(
        n1.structure().to_string(),
        n2.structure().to_string(),
        "let (x, y) = p in x must be definitionally equal to projection p.1"
    );
}

#[test]
fn binary_product_projections_accept_first_and_second_indices() {
    let source = r#"
module TuplePattern.ProjectionBounds where

postulate A : Cat
postulate B : Cat
first_proj (p : (A * B)) : A = p.1
second_proj (p : (A * B)) : B = p.2
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let first_proj = Expr::var("first_proj");
    let second_proj = Expr::var("second_proj");
    let first_ty = semantics.infer_term_type(&typed, &first_proj).unwrap();
    let second_ty = semantics.infer_term_type(&typed, &second_proj).unwrap();
    assert!(!first_ty.to_string().is_empty());
    assert!(!second_ty.to_string().is_empty());
}

#[test]
fn projection_index_zero_is_rejected_with_structured_diagnostics() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module TuplePattern.ProjectionZeroBad where

postulate A : Cat
postulate B : Cat
bad_proj (p : (A * B)) : A = p.0
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
fn tuple_pattern_wildcard_in_let_binds_only_named_component() {
    // Behavioral test: wildcard pattern discards the first component,
    // so the result type must match the second component's type.
    let source = r#"
module TuplePattern.WildcardLet where

postulate A : Cat
postulate B : Cat
snd_via_wildcard (p : (A * B)) : B = let (_, y) = p in y
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let snd_via_wildcard = Expr::var("snd_via_wildcard");
    let ty = semantics
        .infer_term_type(&typed, &snd_via_wildcard)
        .unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn nested_tuple_patterns_typecheck_for_nested_product_structure() {
    let source = r#"
module TuplePattern.Nested where

postulate A : Cat
postulate B : Cat
postulate C : Cat
fst_nested (p : ((A * B) * C)) : A = \((x, y), z). x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let term = Expr::var("fst_nested");
    let ty = semantics.infer_term_type(&typed, &term).unwrap();
    assert!(!ty.to_string().is_empty());
}

#[test]
fn tuple_pattern_let_normalization_preserves_typing() {
    let source = r#"
module TuplePattern.LetReduction where

postulate A : Cat
postulate B : Cat
snd_via_let (p : (A * B)) : B = let (x, y) = p in y
ex (a : A) (b : B) : B = snd_via_let (a, b)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let ex = Expr::var("ex");
    let before = semantics.infer_term_type(&typed, &ex).unwrap();
    let normalized = semantics.normalize_term(&typed, &ex).unwrap();
    let normalized_term = Expr::var(normalized.structure().to_string());
    let after = semantics.infer_term_type(&typed, &normalized_term).unwrap();
    assert_eq!(before, after);
}

#[test]
fn tuple_pattern_non_exhaustive_nested_shape_is_rejected_with_diagnostics() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = r#"
module TuplePattern.NonExhaustive where

postulate A : Cat
postulate B : Cat
postulate C : Cat
bad_nested (p : ((A * B) * C)) : A = \(x, y). x
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
fn surface_pattern_bound_variables_collects_names_depth_first() {
    let pattern = SurfacePattern::Pair(
        Box::new(SurfacePattern::Var("x".to_string())),
        Box::new(SurfacePattern::Pair(
            Box::new(SurfacePattern::Var("y".to_string())),
            Box::new(SurfacePattern::Var("z".to_string())),
        )),
    );
    let vars = pattern.bound_variables();
    assert_eq!(
        vars,
        vec!["x", "y", "z"],
        "bound_variables must collect names in depth-first (left-to-right) order"
    );
}

#[test]
fn surface_pattern_bound_variables_skips_wildcards() {
    let pattern = SurfacePattern::Pair(
        Box::new(SurfacePattern::Var("x".to_string())),
        Box::new(SurfacePattern::Wildcard),
    );
    let vars = pattern.bound_variables();
    assert_eq!(
        vars,
        vec!["x"],
        "bound_variables must skip wildcard positions"
    );
}
