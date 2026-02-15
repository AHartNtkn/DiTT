mod common;

use common::conformance::read_fixture;
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[derive(Debug, Clone, Copy)]
enum NegativeStage {
    Parse,
    Check,
}

fn run_positive_fixture(relative: &str) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = read_fixture(relative);
    let module = syntax.parse_module(&source).unwrap();
    let _typed = semantics.elaborate_module(&module).unwrap();
}

fn run_negative_fixture(relative: &str, stage: NegativeStage) {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let source = read_fixture(relative);
    match stage {
        NegativeStage::Parse => {
            let bundle = syntax.parse_module(&source).unwrap_err().into_diagnostics();
            assert!(!bundle.diagnostics.is_empty());
            for diagnostic in bundle.diagnostics {
                assert!(!diagnostic.category.is_empty());
                assert!(!diagnostic.message.is_empty());
                if let Some(span) = diagnostic.span {
                    assert!(span.start <= span.end);
                }
            }
        }
        NegativeStage::Check => {
            let module = syntax.parse_module(&source).unwrap();
            let err = semantics.elaborate_module(&module).unwrap_err();
            let bundle = err.into_diagnostics();
            assert!(!bundle.diagnostics.is_empty());
        }
    }
}

macro_rules! surface_case {
    ($name:ident, $pos:literal, $neg:literal, Parse) => {
        #[test]
        fn $name() {
            run_positive_fixture($pos);
            run_negative_fixture($neg, NegativeStage::Parse);
        }
    };
    ($name:ident, $pos:literal, $neg:literal, Check) => {
        #[test]
        fn $name() {
            run_positive_fixture($pos);
            run_negative_fixture($neg, NegativeStage::Check);
        }
    };
}

surface_case!(
    module_header_contract,
    "conformance/syntax/positive/module_header_valid.ditt",
    "conformance/syntax/negative/module_header_missing_where.ditt",
    Parse
);
surface_case!(
    local_modules_contract,
    "conformance/syntax/positive/local_modules_valid.ditt",
    "conformance/syntax/negative/local_modules_missing_where_invalid.ditt",
    Parse
);
surface_case!(
    import_basic_contract,
    "conformance/syntax/positive/import_basic_valid.ditt",
    "conformance/syntax/negative/import_basic_invalid.ditt",
    Parse
);
surface_case!(
    import_alias_contract,
    "conformance/syntax/positive/import_alias_valid.ditt",
    "conformance/syntax/negative/import_alias_missing_name.ditt",
    Parse
);
surface_case!(
    import_clauses_contract,
    "conformance/syntax/positive/import_clauses_valid.ditt",
    "conformance/syntax/negative/import_clauses_invalid_item.ditt",
    Parse
);
surface_case!(
    reserved_words_contract,
    "conformance/syntax/positive/reserved_words_valid.ditt",
    "conformance/syntax/negative/reserved_word_as_identifier.ditt",
    Parse
);
surface_case!(
    unicode_identifiers_contract,
    "conformance/syntax/positive/unicode_identifier_valid.ditt",
    "conformance/syntax/negative/unicode_identifier_invalid.ditt",
    Parse
);
surface_case!(
    identifier_digit_start_contract,
    "conformance/syntax/positive/identifier_digit_after_first_valid.ditt",
    "conformance/syntax/negative/identifier_digit_start_invalid.ditt",
    Parse
);
surface_case!(
    one_line_definition_contract,
    "conformance/syntax/positive/one_line_definition_valid.ditt",
    "conformance/syntax/negative/split_definition_invalid.ditt",
    Parse
);
surface_case!(
    duplicate_top_level_contract,
    "conformance/syntax/positive/one_line_definition_valid.ditt",
    "conformance/syntax/negative/duplicate_top_level_invalid.ditt",
    Check
);
surface_case!(
    lambda_forms_contract,
    "conformance/syntax/positive/lambda_forms_valid.ditt",
    "conformance/syntax/negative/lambda_missing_dot_invalid.ditt",
    Parse
);
surface_case!(
    arrow_forms_contract,
    "conformance/syntax/positive/arrow_forms_valid.ditt",
    "conformance/syntax/negative/arrow_malformed_invalid.ditt",
    Parse
);
surface_case!(
    directed_hom_notation_contract,
    "conformance/syntax/positive/directed_hom_forms_valid.ditt",
    "conformance/syntax/negative/directed_hom_bad_invalid.ditt",
    Parse
);
surface_case!(
    refl_term_contract,
    "conformance/syntax/positive/refl_term_valid.ditt",
    "conformance/syntax/negative/refl_term_wrong_arity_invalid.ditt",
    Check
);
surface_case!(
    directed_j_eliminator_contract,
    "conformance/syntax/positive/directed_j_eliminator_valid.ditt",
    "conformance/syntax/negative/directed_j_eliminator_bad_brackets_invalid.ditt",
    Parse
);
surface_case!(
    end_coend_proof_operators_contract,
    "conformance/syntax/positive/end_coend_proof_operators_valid.ditt",
    "conformance/syntax/negative/end_coend_proof_operators_missing_paren_invalid.ditt",
    Parse
);
surface_case!(
    opposite_notation_contract,
    "conformance/syntax/positive/opposite_notation_valid.ditt",
    "conformance/syntax/negative/opposite_prefix_invalid.ditt",
    Parse
);
surface_case!(
    tuple_projection_contract,
    "conformance/syntax/positive/tuple_projection_valid.ditt",
    "conformance/syntax/negative/tuple_projection_bad_index.ditt",
    Parse
);
surface_case!(
    let_forms_contract,
    "conformance/syntax/positive/let_forms_valid.ditt",
    "conformance/syntax/negative/let_in_missing_invalid.ditt",
    Parse
);
surface_case!(
    let_chaining_contract,
    "conformance/syntax/positive/let_chaining_valid.ditt",
    "conformance/syntax/negative/let_chaining_bad_separator.ditt",
    Parse
);
surface_case!(
    end_coend_quantifiers_contract,
    "conformance/syntax/positive/end_coend_forms_valid.ditt",
    "conformance/syntax/negative/end_coend_missing_paren_invalid.ditt",
    Parse
);
surface_case!(
    comments_contract,
    "conformance/syntax/positive/comments_valid.ditt",
    "conformance/syntax/negative/comments_unclosed_block_invalid.ditt",
    Parse
);
surface_case!(
    precedence_projection_application_contract,
    "conformance/syntax/positive/precedence_projection_application_valid.ditt",
    "conformance/syntax/negative/precedence_projection_application_invalid.ditt",
    Parse
);
surface_case!(
    precedence_product_arrow_contract,
    "conformance/syntax/positive/precedence_product_arrow_valid.ditt",
    "conformance/syntax/negative/precedence_product_arrow_invalid.ditt",
    Parse
);
surface_case!(
    arrow_right_associativity_contract,
    "conformance/syntax/positive/arrow_right_assoc_valid.ditt",
    "conformance/syntax/negative/arrow_right_assoc_invalid.ditt",
    Parse
);
surface_case!(
    implicit_named_args_contract,
    "conformance/syntax/positive/implicit_named_args_valid.ditt",
    "conformance/syntax/negative/implicit_named_args_missing_eq.ditt",
    Parse
);
surface_case!(
    binder_grouping_contract,
    "conformance/syntax/positive/binder_grouping_valid.ditt",
    "conformance/syntax/negative/binder_grouping_invalid.ditt",
    Parse
);
surface_case!(
    no_where_blocks_contract,
    "conformance/syntax/positive/no_where_block_valid.ditt",
    "conformance/syntax/negative/where_block_invalid.ditt",
    Parse
);
surface_case!(
    top_shared_bottom_forbidden_contract,
    "conformance/syntax/positive/top_shared_valid.ditt",
    "conformance/syntax/negative/bottom_invalid.ditt",
    Check
);
surface_case!(
    annotated_patterns_contract,
    "conformance/syntax/positive/annotated_patterns_valid.ditt",
    "conformance/syntax/negative/annotated_patterns_bad_annotation.ditt",
    Parse
);
