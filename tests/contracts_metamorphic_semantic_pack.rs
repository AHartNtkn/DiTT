mod common;

use common::engines::compile_module;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;
use proptest::prelude::*;

prop_compose! {
    fn ident()(head in "[a-z]", tail in "[a-z0-9_]{0,10}") -> String {
        format!("{head}{tail}")
    }
}

proptest! {
    #[test]
    fn prop_grouped_and_split_binders_are_semantically_equivalent(x in ident(), y in ident()) {
        prop_assume!(x != y);
        let grouped = format!(
            "module M where\npostulate C : Cat\nf : ({x} {y} : C) -> C = {x}\n"
        );
        let split = format!(
            "module M where\npostulate C : Cat\nf : ({x} : C) ({y} : C) -> C = {x}\n"
        );

        let tg = compile_module(&grouped);
        let ts = compile_module(&split);
        prop_assert_eq!(tg, ts);
    }

    #[test]
    fn prop_ascii_and_unicode_lambda_surface_forms_are_semantically_equivalent(x in ident()) {
        let ascii = format!(
            "module M where\npostulate C : Cat\nid : ({} : C) -> C = \\{}. {}\n",
            x, x, x
        );
        let unicode = format!(
            "module M where\npostulate C : Cat\nid : ({} : C) → C = λ{}. {}\n",
            x, x, x
        );

        let ta = compile_module(&ascii);
        let tu = compile_module(&unicode);
        prop_assert_eq!(ta, tu);
    }

    #[test]
    fn prop_nested_and_multi_binding_let_forms_are_semantically_equivalent(x in ident()) {
        let nested = format!(
            "module M where\npostulate C : Cat\nid : C -> C = \\{}. let y = {} in let z = y in z\n",
            x, x
        );
        let chained = format!(
            "module M where\npostulate C : Cat\nid : C -> C = \\{}. let y = {}; z = y in z\n",
            x, x
        );

        let tn = compile_module(&nested);
        let tc = compile_module(&chained);
        prop_assert_eq!(tn, tc);
    }

    #[test]
    fn prop_import_using_clause_permutation_preserves_parse_semantics(a in ident(), b in ident()) {
        prop_assume!(a != b);
        let syntax = SyntaxEngine::default();
        let left = format!(
            "module M where\nimport Std.Category using ({a}, {b})\npostulate C : Cat\nt : (x : C) -> C = \\x. x\n"
        );
        let right = format!(
            "module M where\nimport Std.Category using ({b}, {a})\npostulate C : Cat\nt : (x : C) -> C = \\x. x\n"
        );

        let l = syntax.parse_module(&left).unwrap();
        let r = syntax.parse_module(&right).unwrap();
        let eq = syntax.alpha_equivalent_modules(&l, &r).unwrap();
        prop_assert!(eq);
    }

    #[test]
    fn prop_ascii_and_unicode_end_forms_are_semantically_equivalent(x in ident()) {
        let ascii = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : end ({} : C). P {} = e\n",
            x, x, x
        );
        let unicode = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : ∫ ({} : C). P {} = e\n",
            x, x, x
        );

        let ta = compile_module(&ascii);
        let tu = compile_module(&unicode);
        prop_assert_eq!(ta, tu);
    }

    #[test]
    fn prop_nested_and_multibinder_end_forms_are_semantically_equivalent(x in ident(), y in ident()) {
        prop_assume!(x != y);
        let nested = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : end ({} : C). end ({} : C). P {} = e\n",
            x, x, y, x
        );
        let multibinder = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : end ({} : C) ({} : C). P {} = e\n",
            x, x, y, x
        );

        let tn = compile_module(&nested);
        let tm = compile_module(&multibinder);
        prop_assert_eq!(tn, tm);
    }

    #[test]
    fn prop_ascii_and_unicode_coend_forms_are_semantically_equivalent(x in ident()) {
        let ascii = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : coend ({} : C). P {} = e\n",
            x, x, x
        );
        let unicode = format!(
            "module M where\npostulate C : Cat\npostulate P : ({} : C) -> Prop\ne : ∫^ ({} : C). P {} = e\n",
            x, x, x
        );

        let ta = compile_module(&ascii);
        let tu = compile_module(&unicode);
        prop_assert_eq!(ta, tu);
    }
}
