mod common;

use common::support::{compile_checked, entailment};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};
use proptest::prelude::*;

/// Language keywords that cannot appear as variable names in expression position.
const KEYWORDS: &[&str] = &[
    "module", "where", "import", "postulate", "let", "in", "Top", "refl", "J", "end", "coend",
    "as", "using", "hiding", "renaming", "to",
];

fn ident() -> impl Strategy<Value = String> {
    ("\\p{XID_Start}", "\\p{XID_Continue}{0,120}")
        .prop_map(|(head, tail)| format!("{head}{tail}"))
        .prop_filter("must not be a language keyword", |id| {
            !KEYWORDS.contains(&id.as_str())
        })
}

prop_compose! {
    fn ws_noise()(s in "[ \\t\\n\\r]{0,256}") -> String {
        s
    }
}

prop_compose! {
    fn module_ident()(head in "[A-Z]", tail in "[A-Za-z0-9_]{0,10}") -> String {
        format!("{head}{tail}")
    }
}

proptest! {
    #[test]
    fn prop_alpha_renaming_preserves_judgment_outcome(left_var in ident(), right_var in ident()) {
        let syntax = SyntaxEngine::default(); let semantics = SemanticEngine::default();
        let left = format!(
            "module M where\npostulate C : Cat\nt : ({left_var} : C) -> {left_var} ->[C] {left_var} = refl {left_var}\n"
        );
        let right = format!(
            "module M where\npostulate C : Cat\nt : ({right_var} : C) -> {right_var} ->[C] {right_var} = refl {right_var}\n"
        );

        let l = compile_checked(&syntax, &semantics,&left);
        let r = compile_checked(&syntax, &semantics,&right);
        let j = entailment("t");
        let lo = semantics.derive(&l, &j, InferenceRule::Refl).unwrap();
        let ro = semantics.derive(&r, &j, InferenceRule::Refl).unwrap();
        prop_assert_eq!(lo, ro);
    }

    #[test]
    fn prop_import_order_invariance_for_acyclic_modules(a in ident(), b in ident()) {
        prop_assume!(a != b);
        let syntax = SyntaxEngine::default(); let semantics = SemanticEngine::default();
        let left = format!("module Main where\nimport {a}\nimport {b}\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n");
        let right = format!("module Main where\nimport {b}\nimport {a}\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n");

        let l = compile_checked(&syntax, &semantics,&left);
        let r = compile_checked(&syntax, &semantics,&right);
        let j = entailment("t");
        let lo = semantics.derive(&l, &j, InferenceRule::Refl).unwrap();
        let ro = semantics.derive(&r, &j, InferenceRule::Refl).unwrap();
        prop_assert_eq!(lo, ro);
    }

    #[test]
    fn prop_whitespace_comment_noise_preserves_parse_semantics(prefix in ws_noise(), suffix in ws_noise()) {
        let syntax = SyntaxEngine::default();
        let noisy = format!(
            "{prefix}// head noise\nmodule M where\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n// tail noise\n{suffix}"
        );
        let parsed = syntax.parse_module(&noisy).unwrap();
        let clean = syntax
            .parse_module("module M where\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n")
            .unwrap();
        let eq = syntax.alpha_equivalent_modules(&parsed, &clean).unwrap();
        prop_assert!(eq);
    }

    #[test]
    fn prop_local_module_alpha_renaming_preserves_judgment_outcome(inner_left in module_ident(), inner_right in module_ident()) {
        prop_assume!(inner_left != inner_right);
        let syntax = SyntaxEngine::default(); let semantics = SemanticEngine::default();
        let left = format!(
            "module M where\npostulate C : Cat\nmodule {inner_left} where\n  r : (x : C) -> x ->[C] x = refl x\nt : (x : C) -> x ->[C] x = {inner_left}.r x\n"
        );
        let right = format!(
            "module M where\npostulate C : Cat\nmodule {inner_right} where\n  r : (x : C) -> x ->[C] x = refl x\nt : (x : C) -> x ->[C] x = {inner_right}.r x\n"
        );

        let l = compile_checked(&syntax, &semantics,&left);
        let r = compile_checked(&syntax, &semantics,&right);
        let j = entailment("t");
        let lo = semantics.derive(&l, &j, InferenceRule::Refl).unwrap();
        let ro = semantics.derive(&r, &j, InferenceRule::Refl).unwrap();
        prop_assert_eq!(lo, ro);
    }

    #[test]
    fn prop_implicit_argument_spelling_preserves_judgment_outcome(x in ident()) {
        let syntax = SyntaxEngine::default(); let semantics = SemanticEngine::default();
        let inferred = format!(
            "module M where\npostulate C : Cat\nlift : {{a : C}} -> a ->[C] a = refl a\nt : ({x} : C) -> {x} ->[C] {x} = lift\n"
        );
        let explicit = format!(
            "module M where\npostulate C : Cat\nlift : {{a : C}} -> a ->[C] a = refl a\nt : ({x} : C) -> {x} ->[C] {x} = lift {{a = {x}}}\n"
        );

        let l = compile_checked(&syntax, &semantics,&inferred);
        let r = compile_checked(&syntax, &semantics,&explicit);
        let j = entailment("t");
        let lo = semantics.derive(&l, &j, InferenceRule::Refl).unwrap();
        let ro = semantics.derive(&r, &j, InferenceRule::Refl).unwrap();
        prop_assert_eq!(lo, ro);
    }

    #[test]
    fn prop_tuple_projection_and_tuple_pattern_forms_preserve_type_inference(a in ident(), b in ident()) {
        prop_assume!(a != b);
        let syntax = SyntaxEngine::default(); let semantics = SemanticEngine::default();
        let projection = format!(
            "module M where\npostulate A : Cat\npostulate B : Cat\nfst (p : (A * B)) : A = p.1\nuse : ({a} : A) ({b} : B) -> A = fst ({a}, {b})\n"
        );
        let pattern = format!(
            "module M where\npostulate A : Cat\npostulate B : Cat\nfst (p : (A * B)) : A = \\(x, y). x\nuse : ({a} : A) ({b} : B) -> A = fst ({a}, {b})\n"
        );

        let l = compile_checked(&syntax, &semantics,&projection);
        let r = compile_checked(&syntax, &semantics,&pattern);
        let term = Expr::var("use");
        let lt = semantics.infer_term_type(&l, &term).unwrap();
        let rt = semantics.infer_term_type(&r, &term).unwrap();
        prop_assert_eq!(lt, rt);
    }
}
