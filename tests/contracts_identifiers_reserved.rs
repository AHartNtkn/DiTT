mod common;

use common::conformance::read_fixture;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

#[test]
fn unicode_identifiers_and_digits_after_first_character_are_accepted() {
    let syntax = SyntaxEngine::default();

    let unicode = read_fixture("conformance/syntax/positive/unicode_identifier_valid.ditt");
    let with_digits =
        read_fixture("conformance/syntax/positive/identifier_digit_after_first_valid.ditt");

    let _u = syntax.parse_module(&unicode).unwrap();
    let _d = syntax.parse_module(&with_digits).unwrap();
}

#[test]
fn reserved_words_cannot_be_used_as_identifiers() {
    let syntax = SyntaxEngine::default();
    let source = read_fixture("conformance/syntax/negative/reserved_word_as_identifier.ditt");
    let bundle = syntax.parse_module(&source).unwrap_err().into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}

#[test]
fn identifiers_cannot_start_with_digits() {
    let syntax = SyntaxEngine::default();
    let source = read_fixture("conformance/syntax/negative/identifier_digit_start_invalid.ditt");
    let bundle = syntax.parse_module(&source).unwrap_err().into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
}
