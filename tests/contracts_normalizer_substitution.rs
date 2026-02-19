mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;

// ---------------------------------------------------------------------------
// Bug: normalize_var_expr re-normalizes substituted values through the same
// substitution, creating infinite loops when beta-reduction maps parameter
// names to expressions containing those same names.
//
// Root cause: src/runtime/semantics.rs, normalize_var_expr line ~3245:
//   return normalize_expr(module, value, subst, seen);
// The `subst` carries the beta-reduction mapping, so looking up a variable
// returns a value, and re-normalizing that value through the same subst
// can look up the same (or another mapped) variable again, ad infinitum.
//
// Two patterns trigger this:
// 1. Direct cycle:  subst has f → expr_containing(Var("f"))
// 2. Indirect cycle: subst has f → Var("g") AND g → Var("f")
// ---------------------------------------------------------------------------

/// Direct cycle: compose_assoc calls compose with an argument that is itself
/// a compose call. compose's parameter `f` gets mapped to the inner compose
/// result, which still contains Var("f") (compose_assoc's bound variable).
/// normalize_var_expr looks up f → inner_result → re-normalizes → hits f again.
#[test]
fn normalizer_does_not_loop_on_nested_self_named_args() {
    let source = r#"
module Test where
postulate C : Cat

diag (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) = \k. k

comp (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag c) [f]) g

// comp's params (a, b, c, f, g) collide with assoc's params.
// The inner `comp a b c f g` normalizes to an expr containing Var("f"),
// then the outer comp maps its own f → that expr, creating f → ...f... cycle.
assoc (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (k : c ->[C] d) : a ->[C] d =
  comp a c d (comp a b c f g) k
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let result = semantics.evaluate_term(&typed, &Expr::var("assoc"));
    assert!(result.is_ok(), "evaluate_term must not stack-overflow: {:?}", result.err());
}

/// Indirect cycle: yoneda_ff_forward calls compose_C with swapped arguments
/// (g, f) instead of (f, g). compose_C's substitution becomes f→Var("g")
/// and g→Var("f"), forming a 2-step cycle: f→g→f→g→...
#[test]
fn normalizer_does_not_loop_on_swapped_arg_names() {
    let source = r#"
module Test where
postulate C : Cat

diag (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) = \k. k

comp (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag c) [f]) g

// Calls comp with g and f SWAPPED relative to comp's parameter names.
// comp's subst becomes {f → Var("g"), g → Var("f")} — indirect cycle.
swap (a : C) (b : C) (f : a ->[C] b) : end (x : C). ((x ->[C] a) -> (x ->[C] b)) =
  \x. \g. comp x a b g f
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let result = semantics.evaluate_term(&typed, &Expr::var("swap"));
    assert!(result.is_ok(), "evaluate_term must not stack-overflow: {:?}", result.err());
}

/// Transitive chain: subst has {a→Var("x"), b→Var("a"), c→Var("b")}.
/// Without the fix, c resolves to x (following c→b→a→x) instead of
/// the correct Var("b").
#[test]
fn normalizer_does_not_chain_substitutions_transitively() {
    let source = r#"
module Test where
postulate C : Cat

diag (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) = \k. k

comp (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag c) [f]) g

// comp is called with (x, a, b, ...) — its parameter `a` maps to Var("x"),
// `b` maps to Var("a"), `c` maps to Var("b"). The body references `c`,
// which should resolve to the argument value Var("b"), not chain through
// b→a→x.
precomp (a : C) (b : C) (f : a ->[C] b) (alpha : end (x : C). ((a ->[C] x) -> (x ->[C] b))) : end (x : C). ((b ->[C] x) -> (x ->[C] b)) =
  \x. \g. alpha x (comp a b x f g)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let result = semantics.evaluate_term(&typed, &Expr::var("precomp"));
    assert!(result.is_ok(), "evaluate_term must not stack-overflow: {:?}", result.err());
    let output = result.unwrap();
    // The normalized form should reference parameters a, b, f, alpha —
    // not collapse them via transitive substitution.
    assert!(
        output.value.contains("alpha"),
        "normalized form must still reference 'alpha', got: {}",
        output.value
    );
}

/// Stdlib smoke test: compose_assoc from Morphism.ditt evaluates without overflow.
#[test]
fn stdlib_morphism_compose_assoc_evaluates() {
    let source = std::fs::read_to_string("stdlib/Morphism.ditt")
        .expect("stdlib/Morphism.ditt must exist");
    let (_syntax, semantics, typed) = compile_with_engines(&source);
    let result = semantics.evaluate_term(&typed, &Expr::var("compose_assoc"));
    assert!(
        result.is_ok(),
        "compose_assoc must evaluate without overflow: {:?}",
        result.err()
    );
}

/// Stdlib smoke test: yoneda_ff_forward from Yoneda.ditt evaluates without overflow.
#[test]
fn stdlib_yoneda_ff_forward_evaluates() {
    let source =
        std::fs::read_to_string("stdlib/Yoneda.ditt").expect("stdlib/Yoneda.ditt must exist");
    let (_syntax, semantics, typed) = compile_with_engines(&source);
    let result = semantics.evaluate_term(&typed, &Expr::var("yoneda_ff_forward"));
    assert!(
        result.is_ok(),
        "yoneda_ff_forward must evaluate without overflow: {:?}",
        result.err()
    );
}
