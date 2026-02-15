mod common;

use common::assertions::assert_def_equal;
use common::conformance::{check_accepts, check_rejects, check_semantic_boundary};
use common::engines::compile_with_engines;
use common::support::{directed_theory_module, entailment, entailment_in_context};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[test]
fn substitution_and_renaming_preserve_typing() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let subst = semantics
        .derive(&typed, &entailment("subst_ty"), InferenceRule::Var)
        .expect("substitution_preserves_typing must be derivable");
    let rename = semantics
        .derive(&typed, &entailment("rename_ty"), InferenceRule::Var)
        .expect("renaming_preserves_typing must be derivable");

    assert_eq!(
        subst.rule.paper_rule_id(),
        "Figure11.Var",
        "substitution_preserves_typing: derivation root rule must match"
    );
    assert_eq!(
        rename.rule.paper_rule_id(),
        "Figure11.Var",
        "renaming_preserves_typing: derivation root rule must match"
    );
}

#[test]
fn weakening_and_exchange_are_admissible() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let weakening = semantics
        .derive(&typed, &entailment("weakening"), InferenceRule::Wk)
        .expect("weakening must be derivable");
    let exchange = semantics
        .derive(&typed, &entailment("exchange"), InferenceRule::Var)
        .expect("exchange must be derivable");

    assert_eq!(
        weakening.rule.paper_rule_id(),
        "Figure11.Wk",
        "weakening_admissible: derivation root rule must match"
    );
    assert_eq!(
        exchange.rule.paper_rule_id(),
        "Figure11.Var",
        "exchange_admissible: derivation root rule must match"
    );
}

#[test]
fn weakening_and_exchange_support_explicit_context_inputs() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let context = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::Var("C".to_string()),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::Var("D".to_string()),
            Variance::Covariant,
        ))
        .weaken(vec![]);

    let weakening = semantics
        .derive(
            &typed,
            &entailment_in_context("weakening", context.clone()),
            InferenceRule::Wk,
        )
        .expect("weakening in context must be derivable");
    let exchanged_context = context
        .exchange(0, 1)
        .expect("exchange must succeed for valid context indices");
    let exchange = semantics
        .derive(
            &typed,
            &entailment_in_context("exchange", exchanged_context),
            InferenceRule::Var,
        )
        .expect("exchange in context must be derivable");

    assert_eq!(
        weakening.rule.paper_rule_id(),
        "Figure11.Wk",
        "weakening_admissible_in_context: derivation root rule must match"
    );
    assert_eq!(
        exchange.rule.paper_rule_id(),
        "Figure11.Var",
        "exchange_admissible_in_context: derivation root rule must match"
    );
}

#[test]
fn meta_property_and_inference_rule_categories_are_not_interchangeable() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.MetaObjectBoundary where
postulate
  C : Cat

refl_probe (x : C) : x ->[C] x =
  refl x

start (x : C) : x ->[C] x =
  refl x

subject_reduction (x : C) : x ->[C] x =
  start x
"#,
    );

    let refl_result = semantics.derive(&typed, &entailment("refl_probe"), InferenceRule::Refl);
    assert!(
        refl_result.is_ok(),
        "refl_probe must be derivable under Refl rule"
    );

    let refl_as_meta = semantics.derive(&typed, &entailment("refl_probe"), InferenceRule::JRule);
    assert!(
        refl_as_meta.is_err(),
        "inference-rule probes must be rejected when checked as different rule judgments"
    );

    let subject_reduction_meta = semantics.derive(
        &typed,
        &entailment("subject_reduction"),
        InferenceRule::JRule,
    );
    assert!(
        subject_reduction_meta.is_ok(),
        "subject_reduction must be derivable under JRule"
    );

    let subject_reduction_as_rule = semantics.derive(
        &typed,
        &entailment("subject_reduction"),
        InferenceRule::Refl,
    );
    assert!(
        subject_reduction_as_rule.is_err(),
        "meta-property probes must be rejected when checked as inference-rule judgments"
    );
}

#[test]
fn transport_identity_and_composition_laws_hold() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.TransportLaws where
postulate
  C : Cat
  P : (x : C) -> Prop
  a : C
  b : C
  c : C
  e1 : a ->[C] b
  e2 : b ->[C] c
  p : P a

transport_id : P a = J (\z. \r. p) [refl a]
transport_comp : P c = J (\z. \r. J (\w. \s. p) [e1]) [e2]
"#,
    );
    let id_result = semantics.derive(&typed, &entailment("transport_id"), InferenceRule::JRule);
    assert!(id_result.is_ok(), "TransportIdentity law must be derivable");

    let comp_result = semantics.derive(&typed, &entailment("transport_comp"), InferenceRule::JRule);
    assert!(
        comp_result.is_ok(),
        "TransportComposition law must be derivable"
    );
}

#[test]
fn end_coend_adjunction_and_end_intro_elim_iso_laws_hold() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.EndCoendLaws where
postulate
  C : Cat
  P : (x : C) -> Prop
  h_end : end (x : C). P x
  h_coend : coend (x : C). P x

end_coend_adjunction_probe (a : C) : P a =
  (end^-1 h_end) a

end_intro_elim_iso_probe : end (x : C). P x =
  end (\x. (end^-1 h_end) x)

coend_intro_elim_iso_probe : coend (x : C). P x =
  coend (\x. (coend^-1 h_coend) x)
"#,
    );

    let adj_result = semantics.derive(
        &typed,
        &entailment("end_coend_adjunction_probe"),
        InferenceRule::EndElim,
    );
    assert!(
        adj_result.is_ok(),
        "EndCoendAdjunction law must be derivable"
    );

    let end_iso_result = semantics.derive(
        &typed,
        &entailment("end_intro_elim_iso_probe"),
        InferenceRule::EndIntro,
    );
    assert!(
        end_iso_result.is_ok(),
        "EndIntroElimIso law must be derivable for ends"
    );

    let coend_iso_result = semantics.derive(
        &typed,
        &entailment("coend_intro_elim_iso_probe"),
        InferenceRule::CoendIntro,
    );
    assert!(
        coend_iso_result.is_ok(),
        "CoendIntroElimIso law must be derivable for coends"
    );
}

#[test]
fn subject_reduction_is_executable_as_meta_property_judgment() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.SubjectReduction.Positive where

postulate
  C : Cat

start (x : C) : x ->[C] x = refl x
stepped (x : C) : x ->[C] x = start x
subject_reduction (x : C) : x ->[C] x = stepped x
"#,
    );

    let preserves = semantics
        .derive(
            &typed,
            &entailment("subject_reduction"),
            InferenceRule::JRule,
        )
        .expect("subject_reduction must be derivable");

    assert_eq!(
        preserves.rule.paper_rule_id(),
        "Figure11.JRule",
        "subject_reduction: derivation root rule must match"
    );
}

#[test]
fn subject_reduction_rejects_type_changing_step() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.SubjectReduction.Negative where

postulate
  C : Cat

start (x : C) : x ->[C] x = refl x
stepped (x : C) : C = x
subject_reduction (x : C) : x ->[C] x = start x
"#,
    );

    let result = semantics.derive(
        &typed,
        &entailment("subject_reduction"),
        InferenceRule::JRule,
    );

    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "subject reduction type change must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

#[test]
fn substitution_preserves_typing_rejects_type_violating_substitution() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.SubstitutionPreservesTyping.TypeViolatingSubstitute where

postulate
  A : Cat
  B : Cat
  f : (x : A) -> B

probe (x : B) : B = f x
"#,
    );

    let result = semantics.derive(&typed, &entailment("probe"), InferenceRule::Var);

    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "type-violating substitution must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

#[test]
fn op_involution_and_beta_eta_laws_hold_definitionally() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.OpBetaEta.Definitional where

postulate
  C : Cat

C_op : Cat =
  C^

op_left : Cat =
  C_op^

op_right : Cat =
  C

op_involution (x : C) : x ->[op_left] x =
  refl x

beta_left (x : C) : C =
  (\y. y) x

beta_right (x : C) : C =
  x

beta (x : C) : C =
  beta_left x

eta_left (f : (x : C) -> C) : (x : C) -> C =
  \x. f x

eta_right (f : (x : C) -> C) : (x : C) -> C =
  f

eta (f : (x : C) -> C) : (x : C) -> C =
  eta_left f
"#,
    );

    // Verify judgmental equality: witness reuse under each equational-law judgment.
    let op = semantics
        .derive(&typed, &entailment("op_involution"), InferenceRule::Refl)
        .expect("op_involution must be derivable");
    let beta = semantics
        .derive(&typed, &entailment("beta"), InferenceRule::JRule)
        .expect("beta must be derivable");
    let eta = semantics
        .derive(&typed, &entailment("eta"), InferenceRule::JRule)
        .expect("eta must be derivable");

    assert_eq!(
        op.rule.paper_rule_id(),
        "Figure11.Refl",
        "op_involution: derivation root rule must match"
    );
    assert_eq!(
        beta.rule.paper_rule_id(),
        "Figure11.JRule",
        "beta_law: derivation root rule must match"
    );
    assert_eq!(
        eta.rule.paper_rule_id(),
        "Figure11.JRule",
        "eta_law: derivation root rule must match"
    );

    // Verify computational equality: left = right for each equation.
    assert_def_equal(
        &semantics,
        &typed,
        "op_left",
        "op_right",
        "OpInvolution: (C^)^ must be definitionally equal to C",
    );
    assert_def_equal(
        &semantics,
        &typed,
        "beta_left",
        "beta_right",
        "BetaLaw: (\\x. (\\y. y) x) must be definitionally equal to (\\x. x)",
    );
    assert_def_equal(
        &semantics,
        &typed,
        "eta_left",
        "eta_right",
        "EtaLaw: (\\f. \\x. f x) must be definitionally equal to (\\f. f)",
    );
}

#[test]
fn term_level_opposite_involution_holds_for_hom_categories() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.OpInvolution.TermLevel where

postulate
  C : Cat
  a : C
  b : C^
  h_op : a ->[C^] b

id_double_op (x : C) : x ->[(C^)^] x =
  refl x

id_base (x : C) : x ->[C] x =
  refl x
"#,
    );

    let h_op = Expr::var("h_op");
    let h_op_ty = semantics.infer_term_type(&typed, &h_op).unwrap();
    assert!(
        h_op_ty.to_string().contains("->["),
        "h_op must infer a hom type over the opposite category"
    );

    assert_def_equal(
        &semantics,
        &typed,
        "id_double_op",
        "id_base",
        "((C^)^) must be definitionally equal to C when used in hom typing",
    );
}

#[test]
fn functor_map_identity_with_concrete_functor() {
    let semantics = SemanticEngine::default();
    // Verify judgmental equality: witness for the left map form is reusable at the right form.
    let typed = check_accepts(
        r#"
module Rules.FunctorMapIdentity.ConcreteFunctor where

postulate
  C : Cat

IdObj (x : C) : C =
  x

IdMap (a : C) (b : C) (f : a ->[C] b) : IdObj a ->[C] IdObj b =
  f

map_identity_left (x : C) : IdObj x ->[C] IdObj x =
  IdMap x x (refl x)

map_identity_right (x : C) : IdObj x ->[C] IdObj x =
  refl x

postulate
  Witness : (x : C) -> (u : IdObj x ->[C] IdObj x) -> Prop
  seed : (x : C) -> Witness x (map_identity_left x)

probe (x : C) : Witness x (map_identity_right x) =
  seed x
"#,
    );

    // Verify computational equality: left = right.
    assert_def_equal(
        &semantics,
        &typed,
        "map_identity_left",
        "map_identity_right",
        "MapIdentity: mapped identity must be definitionally equal to identity",
    );
}

#[test]
fn functor_map_composition_with_concrete_functor() {
    let semantics = SemanticEngine::default();
    // Verify judgmental equality: witness for composed-map normal form is reusable
    // at the direct-composition normal form.
    let typed = check_accepts(
        r#"
module Rules.FunctorMapComposition.ConcreteFunctor where

postulate
  C : Cat

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

IdObj (x : C) : C =
  x

IdMap (a : C) (b : C) (f : a ->[C] b) : IdObj a ->[C] IdObj b =
  f

map_composition_left (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : IdObj a ->[C] IdObj c =
  compose_via_j a b c (IdMap a b f) (IdMap b c g)

map_composition_right (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : IdObj a ->[C] IdObj c =
  compose_via_j a b c f g

postulate
  Witness : (a : C) -> (b : C) -> (c : C) -> (u : IdObj a ->[C] IdObj c) -> Prop
  seed : (a : C) -> (b : C) -> (c : C) -> (f : a ->[C] b) -> (g : b ->[C] c) -> Witness a b c (map_composition_left a b c f g)

probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : Witness a b c (map_composition_right a b c f g) =
  seed a b c f g
"#,
    );

    // Verify computational equality: left = right.
    assert_def_equal(
        &semantics,
        &typed,
        "map_composition_left",
        "map_composition_right",
        "MapComposition: mapped composition must be definitionally equal to composed maps",
    );
}

#[test]
fn dinatural_transformations_do_not_compose_in_general() {
    // Paper Section 1.1: "Dinatural transformations do not compose in general".
    check_rejects(
        &[
            r#"
module Rules.DinaturalNonComposition where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (z : C) -> P z z -> Q z z
  gamma : (z : C) -> Q z z -> R z z

compose (z : C) (p : P z z) : R z z =
  gamma z (alpha z p)
"#,
            r#"
module Rules.DinaturalNonComposition.ExplicitIntermediate where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (z : C) -> P z z -> Q z z
  gamma : (z : C) -> Q z z -> R z z

compose (z : C) (p : P z z) : R z z =
  let q = alpha z p in gamma z q
"#,
            r#"
module Rules.DinaturalNonComposition.ReversedDirection where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (z : C) -> Q z z -> P z z
  gamma : (z : C) -> R z z -> Q z z

compose (z : C) (r : R z z) : P z z =
  alpha z (gamma z r)
"#,
        ],
        "TypeTheory",
    );

    // Verify that the rejection is specifically a derive error with TypeTheory diagnostics
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.DinaturalNonComposition.DirectednessCheck where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (z : C) -> P z z -> Q z z
  gamma : (z : C) -> Q z z -> R z z

compose (z : C) (p : P z z) : R z z =
  gamma z (alpha z p)
"#,
    );
    let result = semantics.derive(&typed, &entailment("compose"), InferenceRule::CutNat);
    assert!(
        result.is_err(),
        "dinatural non-composition must be rejected"
    );
    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "dinatural non-composition must be rejected due to TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

#[test]
fn congruence_and_normalization_coherence_hold() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let congruence = semantics
        .derive(&typed, &entailment("congruence"), InferenceRule::Prod)
        .expect("congruence must be derivable");
    let coherence = semantics
        .derive(&typed, &entailment("norm_coherence"), InferenceRule::JRule)
        .expect("normalization coherence must be derivable");

    assert_eq!(
        congruence.rule.paper_rule_id(),
        "Figure11.Prod",
        "congruence_for_all_constructors: derivation root rule must match"
    );
    assert_eq!(
        coherence.rule.paper_rule_id(),
        "Figure11.JRule",
        "normalization_coherence: derivation root rule must match"
    );
}

#[test]
fn coend_intro_elim_iso_and_functoriality_laws_hold() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.EndCoendLaws where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  ObsC : (u : coend (x : C). P x) -> Prop
  ObsE : (u : end (x : C). R x) -> Prop
  ObsK : (u : coend (x : C). R x) -> Prop
  seed_iso : (h : coend (x : C). P x) -> ObsC h
  seed_end : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> ObsE (end (\x. g x (f x ((end^-1 h) x))))
  seed_coend : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> ObsK (coend (\x. g x (f x ((coend^-1 h) x))))

coend_iso_probe (h : coend (x : C). P x) : ObsC (coend (coend^-1 h)) =
  seed_iso h

end_functoriality_probe (h : end (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : ObsE (end (\x. g x ((\y. f y ((end^-1 h) y)) x))) =
  seed_end h f g

coend_functoriality_probe (h : coend (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : ObsK (coend (\x. g x ((\y. f y ((coend^-1 h) y)) x))) =
  seed_coend h f g
"#,
    );

    let coend_iso = semantics.derive(
        &typed,
        &entailment("coend_iso_probe"),
        InferenceRule::CoendIntro,
    );
    let end_functoriality = semantics.derive(
        &typed,
        &entailment("end_functoriality_probe"),
        InferenceRule::EndIntro,
    );
    let coend_functoriality = semantics.derive(
        &typed,
        &entailment("coend_functoriality_probe"),
        InferenceRule::CoendIntro,
    );

    assert!(coend_iso.is_ok(), "CoendIntroElimIso law must be derivable");
    assert!(
        end_functoriality.is_ok(),
        "EndFunctoriality law must be derivable"
    );
    assert!(
        coend_functoriality.is_ok(),
        "CoendFunctoriality law must be derivable"
    );
}

#[test]
fn substitution_preserves_typing_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "substitution_preserves_typing",
        InferenceRule::Var,
        "probe",
        r#"
module Rules.SubstitutionPreservesTyping.Positive where

postulate
  A : Cat
  B : Cat
  f : (x : A) -> B

probe (x : A) : B = (\y. f y) x
"#,
        r#"
module Rules.SubstitutionPreservesTyping.Negative where

postulate
  A : Cat
  B : Cat
  f : (x : A) -> B
  k : (x : A) -> A

probe (x : A) : B = f (k x)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn renaming_preserves_typing_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "renaming_preserves_typing",
        InferenceRule::Var,
        "probe",
        r#"
module Rules.RenamingPreservesTyping.Positive where

postulate
  A : Cat
  B : Cat
  f : (x : A) -> B

probe (x : A) : B = (\renamed. f renamed) x
"#,
        r#"
module Rules.RenamingPreservesTyping.Negative where

postulate
  A : Cat
  B : Cat
  probe : (x : A) -> (y : A) -> B
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn weakening_admissible_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "weakening_admissible",
        InferenceRule::Wk,
        "probe",
        r#"
module Rules.WeakeningAdmissible.Positive where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A = x
"#,
        r#"
module Rules.WeakeningAdmissible.Negative where

postulate
  A : Cat
  B : Cat
  probe : (x : A) -> A
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn exchange_admissible_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "exchange_admissible",
        InferenceRule::Var,
        "probe",
        r#"
module Rules.ExchangeAdmissible.Positive where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : (B * A) = (y, x)
"#,
        r#"
module Rules.ExchangeAdmissible.Negative where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : (A * B) = (x, y)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn op_involution_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "op_involution",
        InferenceRule::Refl,
        "probe",
        r#"
module Rules.OpInvolution.Positive where

postulate
  C : Cat

C_op : Cat = C^
C_op_op : Cat = C_op^

probe (x : C) : x ->[C_op_op] x = refl x
"#,
        r#"
module Rules.OpInvolution.Negative where

postulate
  C : Cat

C_op : Cat = C^

probe (x : C) : x ->[C_op] x = refl x
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn beta_law_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "beta_law",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.BetaLaw.Positive where

postulate
  C : Cat

probe (x : C) : C = (\y. y) x
"#,
        r#"
module Rules.BetaLaw.Negative where

postulate
  C : Cat
  probe : (x : C) -> (y : C) -> C
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn eta_law_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "eta_law",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.EtaLaw.Positive where

postulate
  C : Cat

probe (f : (x : C) -> C) : (x : C) -> C = \x. f x
"#,
        r#"
module Rules.EtaLaw.Negative where

postulate
  C : Cat
  probe : (f : (x : C) -> C) -> (x : C) -> C -> C
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn coend_intro_elim_iso_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "coend_intro_elim_iso",
        InferenceRule::CoendIntro,
        "probe",
        r#"
module Rules.CoendIntroElimIso.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (u : coend (x : C). P x) -> Prop
  seed : (h : coend (x : C). P x) -> Obs h

probe (h : coend (x : C). P x) : Obs (coend (coend^-1 h)) =
  seed h
"#,
        r#"
module Rules.CoendIntroElimIso.Negative where

postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (u : coend (x : C). P x) -> Prop
  probe : (h : coend (x : C). P x) -> Obs (coend (coend^-1 h)) -> Obs h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn end_functoriality_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "end_functoriality",
        InferenceRule::EndIntro,
        "probe",
        r#"
module Rules.EndFunctoriality.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : end (x : C). R x) -> Prop
  seed : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (end (\x. g x (f x ((end^-1 h) x))))

probe (h : end (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (end (\x. g x ((\y. f y ((end^-1 h) y)) x))) =
  seed h f g
"#,
        r#"
module Rules.EndFunctoriality.Negative where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : end (x : C). R x) -> Prop

probe : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (end (\x. g x (f x ((end^-1 h) x)))) -> Obs (end (\x. g x ((\y. f y ((end^-1 h) y)) x)))
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn coend_functoriality_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "coend_functoriality",
        InferenceRule::CoendIntro,
        "probe",
        r#"
module Rules.CoendFunctoriality.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : coend (x : C). R x) -> Prop
  seed : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (coend (\x. g x (f x ((coend^-1 h) x))))

probe (h : coend (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (coend (\x. g x ((\y. f y ((coend^-1 h) y)) x))) =
  seed h f g
"#,
        r#"
module Rules.CoendFunctoriality.Negative where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : coend (x : C). R x) -> Prop

probe : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (coend (\x. g x (f x ((coend^-1 h) x)))) -> Obs (coend (\x. g x ((\y. f y ((coend^-1 h) y)) x)))
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn congruence_for_all_constructors_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "congruence_all_constructors",
        InferenceRule::Prod,
        "probe",
        r#"
module Rules.CongruenceForAllConstructors.Positive where

postulate
  C : Cat
  D : Cat

probe (a : C) (a2 : C) (b : D) (b2 : D) (u : a ->[C] a2) (v : b ->[D] b2) : (a, b) ->[(C * D)] (a2, b2) =
  (u, v)
"#,
        r#"
module Rules.CongruenceForAllConstructors.Negative where

postulate
  C : Cat
  D : Cat
  u : (a : C) -> (a2 : C) -> (a ->[C] a2)
  v : (b : D) -> (b2 : D) -> (b ->[D] b2)

probe : (a : C) -> (a2 : C) -> (b : D) -> (b2 : D) -> ((a2, b2) ->[(C * D)] (a, b)) =
  \a. \a2. \b. \b2. (u a a2, v b b2)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn congruence_for_lambda_constructor_has_semantic_boundary() {
    check_semantic_boundary(
        "congruence_lambda_constructor",
        InferenceRule::Prod,
        "probe",
        r#"
module Rules.CongruenceForAllConstructorsLambda.Positive where

postulate
  C : Cat
  F : (x : C) -> C

probe : (x : C) -> C =
  \x. F x
"#,
        r#"
module Rules.CongruenceForAllConstructorsLambda.Negative where

postulate
  C : Cat
  probe : (f : (x : C) -> C) -> (x : C) -> C -> C
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn congruence_for_application_constructor_has_semantic_boundary() {
    check_semantic_boundary(
        "congruence_application_constructor",
        InferenceRule::Prod,
        "probe",
        r#"
module Rules.CongruenceForAllConstructorsApplication.Positive where

postulate
  C : Cat
  F : (x : C) -> C

probe (x : C) : C =
  F x
"#,
        r#"
module Rules.CongruenceForAllConstructorsApplication.Negative where

postulate
  C : Cat
  probe : (f : (x : C) -> C) -> (x : C) -> C -> C
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn congruence_for_hom_functor_constructors_has_semantic_boundary() {
    check_semantic_boundary(
        "congruence_hom_functor_constructors",
        InferenceRule::Prod,
        "probe",
        r#"
module Rules.CongruenceForAllConstructorsHomFunctor.Positive where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D

probe (x : C) : F x ->[D] F x =
  refl (F x)
"#,
        r#"
module Rules.CongruenceForAllConstructorsHomFunctor.Negative where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  probe : (x : C) -> (y : C) -> (x ->[C] y) -> (F y ->[D] F x)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn congruence_for_let_constructor_has_semantic_boundary() {
    check_accepts(
        r#"
module Rules.CongruenceForAllConstructorsLet.Positive where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  let (u, v) = (x, y) in u
"#,
    );
    check_rejects(
        &[
            r#"
module Rules.CongruenceForAllConstructorsLet.Negative.BadComponent where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  let (u, v) = (x, y) in v
"#,
            r#"
module Rules.CongruenceForAllConstructorsLet.Negative.BadResultShape where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  let (u, v) = (x, y) in (u, v)
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn congruence_for_proj_constructor_has_semantic_boundary() {
    check_accepts(
        r#"
module Rules.CongruenceForAllConstructorsProj.Positive where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  (x, y).1
"#,
    );
    check_rejects(
        &[
            r#"
module Rules.CongruenceForAllConstructorsProj.Negative.BadIndex where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  (x, y).3
"#,
            r#"
module Rules.CongruenceForAllConstructorsProj.Negative.BadProjectedType where

postulate
  A : Cat
  B : Cat

probe (x : A) (y : B) : A =
  (x, y).2
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn congruence_for_top_constructor_has_semantic_boundary() {
    check_accepts(
        r#"
module Rules.CongruenceForAllConstructorsTop.Positive where

probe (u : Top) : Top =
  u
"#,
    );
    check_rejects(
        &[
            r#"
module Rules.CongruenceForAllConstructorsTop.Negative.ReflTop where

probe (u : Top) : Top =
  refl u
"#,
            r#"
module Rules.CongruenceForAllConstructorsTop.Negative.FunctionAsTop where

probe : Top =
  (\x. x)
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn congruence_for_end_intro_constructor_has_semantic_boundary() {
    check_accepts(
        r#"
module Rules.CongruenceForAllConstructorsEndIntro.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop
  lift : (x : C) -> P x

probe : end (x : C). P x =
  end lift
"#,
    );
    check_rejects(
        &[
            r#"
module Rules.CongruenceForAllConstructorsEndIntro.Negative.BadConstructor where

postulate
  C : Cat
  P : (x : C) -> Prop
  lift : (x : C) -> P x

probe : end (x : C). P x =
  coend lift
"#,
            r#"
module Rules.CongruenceForAllConstructorsEndIntro.Negative.BadElimShape where

postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x

probe : end (x : C). P x =
  end^-1 h
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn congruence_for_coend_intro_constructor_has_semantic_boundary() {
    check_accepts(
        r#"
module Rules.CongruenceForAllConstructorsCoendIntro.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop
  lift : (x : C) -> P x

probe : coend (x : C). P x =
  coend lift
"#,
    );
    check_rejects(
        &[
            r#"
module Rules.CongruenceForAllConstructorsCoendIntro.Negative.BadConstructor where

postulate
  C : Cat
  P : (x : C) -> Prop
  lift : (x : C) -> P x

probe : coend (x : C). P x =
  end lift
"#,
            r#"
module Rules.CongruenceForAllConstructorsCoendIntro.Negative.BadElimShape where

postulate
  C : Cat
  P : (x : C) -> Prop
  h : coend (x : C). P x

probe : coend (x : C). P x =
  coend^-1 h
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn normalization_coherence_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "normalization_coherence",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.NormalizationCoherence.Positive where

postulate
  C : Cat

probe (x : C) : C = (\u. u) ((\v. v) x)
"#,
        r#"
module Rules.NormalizationCoherence.Negative where

postulate
  C : Cat
  probe : (x : C) -> (y : C) -> C
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn type_checking_is_deterministic() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();

    // Error path: elaborating an ill-typed module must produce identical diagnostics.
    let bad_source = r#"
module MetaTheory.TypeCheckingDeterminism where
postulate
  C : Cat
  x : C

bad : C =
  refl x
"#;
    let bad_parsed = syntax.parse_module(bad_source).unwrap();

    let first = match semantics.elaborate_module(&bad_parsed) {
        Ok(_) => DiagnosticBundle::default(),
        Err(err) => err.into_diagnostics(),
    };
    let second = match semantics.elaborate_module(&bad_parsed) {
        Ok(_) => DiagnosticBundle::default(),
        Err(err) => err.into_diagnostics(),
    };

    assert_eq!(
        first, second,
        "elaboration diagnostics must be deterministic for identical inputs"
    );

    // Success path: elaborating a valid module must produce identical TypedModule values.
    let good_source = r#"
module MetaTheory.TypeCheckingDeterminism.Valid where
postulate
  C : Cat

id (x : C) : C = x
compose (f : (x : C) -> C) (g : (x : C) -> C) (x : C) : C = f (g x)
"#;
    let good_parsed = syntax.parse_module(good_source).unwrap();
    let typed1 = semantics.elaborate_module(&good_parsed).unwrap();
    let typed2 = semantics.elaborate_module(&good_parsed).unwrap();
    assert_eq!(typed1, typed2, "elaboration must be deterministic");
}

#[test]
fn well_typed_terms_progress() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module MetaTheory.Progress where
postulate
  C : Cat
  a : C

id (x : C) : C =
  x

beta_redex : C =
  (\y. y) a
"#,
    );

    let normal = semantics.normalize_term(&typed, &Expr::var("beta_redex"));
    assert!(
        normal.is_ok(),
        "well-typed reducible terms must make progress by normalizing successfully"
    );

    // The beta redex (\y. y) a must normalize to the same value as a.
    // Verify the normalized form is definitionally equal to the expected value.
    assert_def_equal(
        &semantics,
        &typed,
        "beta_redex",
        "a",
        "normalized form of (\\y. y) a must be definitionally equal to a",
    );
}

#[test]
fn j_computation_equational_law() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let parsed = syntax.parse_module(directed_theory_module()).unwrap();
    let typed = semantics.elaborate_module(&parsed).unwrap();

    // J(h)[refl_C] = h (Figure 11 computation rule)
    let result = semantics.derive(&typed, &entailment("j_comp"), InferenceRule::JRule);
    assert!(
        result.is_ok(),
        "J computation rule J(h)[refl] = h must be derivable"
    );

    // Negative: J applied to non-refl should not satisfy computation rule
    let parsed_neg = syntax
        .parse_module(
            r#"
module Rules.JComputationNeg where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> P z z -> Q z z
  a : C
  b : C
  e : a ->[C] b

bad_j_comp (p : P b a) : Q a b =
  J h [e]
"#,
        )
        .unwrap();
    let typed_neg = semantics.elaborate_module(&parsed_neg).unwrap();

    let result_neg = semantics.derive(&typed_neg, &entailment("bad_j_comp"), InferenceRule::JRule);
    let diagnostics = result_neg.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "J computation non-refl path must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}
