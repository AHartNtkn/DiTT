mod common;

use common::support::{compile_checked, entailment};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn judgment_outcomes_are_invariant_under_alpha_renaming() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let base = r#"
module M where
postulate C : Cat
t : (x : C) -> x ->[C] x = refl x
"#;
    let renamed = r#"
module M where
postulate C : Cat
t : (y : C) -> y ->[C] y = refl y
"#;

    let t_base = compile_checked(&syntax, &semantics, base);
    let t_renamed = compile_checked(&syntax, &semantics, renamed);
    let j = entailment("t");
    let r1 = semantics.derive(&t_base, &j, InferenceRule::Refl).unwrap();
    let r2 = semantics
        .derive(&t_renamed, &j, InferenceRule::Refl)
        .unwrap();
    assert_eq!(r1, r2);
}

#[test]
fn judgment_outcomes_are_invariant_under_import_reordering_when_acyclic() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let a = "module Main where\nimport A\nimport B\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n";
    let b = "module Main where\nimport B\nimport A\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n";

    let ta = compile_checked(&syntax, &semantics, a);
    let tb = compile_checked(&syntax, &semantics, b);
    let j = entailment("t");
    assert_eq!(
        semantics.derive(&ta, &j, InferenceRule::Refl).unwrap(),
        semantics.derive(&tb, &j, InferenceRule::Refl).unwrap()
    );
}

#[test]
fn judgment_outcomes_are_invariant_under_whitespace_comment_noise_and_module_refactor() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let compact = "module M where\npostulate C : Cat\nt:(x:C)->x->[C]x=refl x\n";
    let noisy = "\n// header\nmodule M where\n\npostulate C : Cat\nt : (x : C) -> x ->[C] x = refl x\n// footer\n";

    let tc = compile_checked(&syntax, &semantics, compact);
    let tn = compile_checked(&syntax, &semantics, noisy);
    let j = entailment("t");
    assert_eq!(
        semantics.derive(&tc, &j, InferenceRule::Refl).unwrap(),
        semantics.derive(&tn, &j, InferenceRule::Refl).unwrap()
    );
}
