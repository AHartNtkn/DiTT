pub mod assertions;
pub mod conformance;
pub mod engines;
pub mod fixtures;
pub mod support;

/// Data-driven test for rules that are purely check_accepts + check_rejects.
#[macro_export]
macro_rules! rule_contract {
    ($(#[$meta:meta])* $name:ident, positive: $pos:expr, negatives: [$($neg:expr),+ $(,)?], category: $cat:expr) => {
        #[test]
        $(#[$meta])*
        fn $name() {
            common::conformance::check_accepts($pos);
            common::conformance::check_rejects(&[$($neg),+], $cat);
        }
    };
}

/// Data-driven test for alpha-equivalence between two source modules.
#[macro_export]
macro_rules! alpha_equiv_test {
    ($name:ident, $left:expr, $right:expr) => {
        #[test]
        fn $name() {
            use ditt_lang::api::{AstEquivalence, Parser};
            let syntax = ditt_lang::runtime::SyntaxEngine::default();
            let a = syntax.parse_module($left).unwrap();
            let b = syntax.parse_module($right).unwrap();
            assert!(
                syntax.alpha_equivalent_modules(&a, &b).unwrap(),
                "sources must be alpha-equivalent"
            );
        }
    };
}
