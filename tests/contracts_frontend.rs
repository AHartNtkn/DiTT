mod common;

use common::support::*;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

fn tiny_module(name: &str, ident: &str) -> String {
    format!(
        "module {name} where\npostulate C : Cat\n{ident} : (x : C) -> C = \\x. x\n",
        name = name,
        ident = ident
    )
}

#[test]
fn lexer_token_spans_are_sorted_and_non_overlapping() {
    let syntax = SyntaxEngine::default();
    let modules = ["M", "Core9", "Contracts_1"];
    let idents = ["id", "map2", "transport_7"];

    for module in modules {
        for ident in idents {
            let source = tiny_module(module, ident);
            let tokens = syntax.lex(&source).unwrap();

            let mut prev_end = 0usize;
            for token in tokens {
                assert!(token.span.start <= token.span.end);
                assert!(token.span.start >= prev_end);
                prev_end = token.span.end;
            }
        }
    }
}

#[test]
fn parser_is_deterministic_for_identical_input() {
    let syntax = SyntaxEngine::default();
    let source = example_module();

    let one = syntax.parse_module(source).unwrap();
    let two = syntax.parse_module(source).unwrap();

    assert_eq!(one, two);
}

#[test]
fn parser_populates_concrete_term_structure_for_core_expr_variants() {
    let syntax = SyntaxEngine::default();

    let var = syntax.parse_expr("x").unwrap();
    assert!(
        matches!(var, Expr::Var(ref name) if name == "x"),
        "term parser must produce Var for variables"
    );

    let pair = syntax.parse_expr("(x, y)").unwrap();
    assert!(
        matches!(pair, Expr::Pair { .. }),
        "term parser must produce Pair for pair expressions"
    );

    let app = syntax.parse_expr("f x").unwrap();
    assert!(
        matches!(app, Expr::App { .. }),
        "term parser must produce App for applications"
    );
}

#[test]
fn parser_formatter_roundtrip_preserves_semantics_and_meets_format_constraints() {
    let syntax = SyntaxEngine::default();
    let modules = ["M", "Core9", "Contracts_1"];
    let idents = ["id", "map2", "transport_7"];

    for module in modules {
        for ident in idents {
            let source = tiny_module(module, ident);

            let parsed_1 = syntax.parse_module(&source).unwrap();
            let printed_1 = syntax.format_module(&parsed_1).unwrap();
            assert_format_contracts(&printed_1);
            let parsed_2 = syntax.parse_module(&printed_1).unwrap();
            let printed_2 = syntax.format_module(&parsed_2).unwrap();
            assert_format_contracts(&printed_2);
            let equivalent = syntax
                .alpha_equivalent_modules(&parsed_1, &parsed_2)
                .unwrap();
            assert!(equivalent);
        }
    }
}

#[test]
fn alpha_equivalence_holds_under_bound_renaming() {
    let syntax = SyntaxEngine::default();
    let names = ["x", "a", "value9", "long_name"];

    for lhs_var in names {
        for rhs_var in names {
            let left = format!(
                "module M where\nid : (x : C) -> C = \\{v}. {v}\n",
                v = lhs_var
            );
            let right = format!(
                "module M where\nid : (x : C) -> C = \\{v}. {v}\n",
                v = rhs_var
            );

            let left_ast = syntax.parse_module(&left).unwrap();
            let right_ast = syntax.parse_module(&right).unwrap();
            let equivalent = syntax
                .alpha_equivalent_modules(&left_ast, &right_ast)
                .unwrap();

            assert!(equivalent);
        }
    }
}

#[test]
fn parser_reports_structured_diagnostics_for_invalid_syntax() {
    let syntax = SyntaxEngine::default();
    let err = syntax.parse_module(invalid_module()).unwrap_err();

    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert!(!diagnostic.category.is_empty());
        assert!(!diagnostic.message.is_empty());
        if let Some(span) = diagnostic.span {
            assert!(span.start <= span.end);
        }
    }
}

#[test]
fn parser_recovery_reports_multiple_errors_in_stable_order() {
    let syntax = SyntaxEngine::default();
    let source = "module M where\nx =\ny =\n";

    let bundle1 = syntax.parse_module(source).unwrap_err().into_diagnostics();
    let bundle2 = syntax.parse_module(source).unwrap_err().into_diagnostics();

    assert_eq!(bundle1, bundle2);
    let mut prev_start = 0usize;
    for d in &bundle1.diagnostics {
        if let Some(span) = d.span {
            assert!(span.start >= prev_start);
            prev_start = span.start;
        }
    }
}
