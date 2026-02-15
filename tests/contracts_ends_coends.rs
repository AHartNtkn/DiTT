mod common;

use common::conformance::{check_rejects, check_semantic_boundary, reject_once};
use common::engines::compile_with_engines;
use ditt_lang::api::*;
use ditt_lang::runtime::SyntaxEngine;

#[test]
fn end_and_coend_surface_forms_parse_and_typecheck() {
    let source = r#"
module EndsCoends.Surface where

postulate C : Cat
postulate P : (x : C) -> Prop
mk_end_witness (x : C) : end (u : C). P u = end x
mk_coend_witness (x : C) : coend (u : C). P u = coend x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let end_witness = Expr::var("mk_end_witness");
    let end_ty = semantics.infer_term_type(&typed, &end_witness).unwrap();
    assert!(
        end_ty.to_string().contains("end"),
        "mk_end_witness must infer an end type, got: {}",
        end_ty,
    );

    let coend_witness = Expr::var("mk_coend_witness");
    let coend_ty = semantics.infer_term_type(&typed, &coend_witness).unwrap();
    assert!(
        coend_ty.to_string().contains("coend"),
        "mk_coend_witness must infer a coend type, got: {}",
        coend_ty,
    );
}

#[test]
fn end_coend_terms_normalize_deterministically() {
    let source = r#"
module EndsCoends.Normalize where

postulate C : Cat
postulate P : (x : C) -> Prop
witness (x : C) : end (u : C). P u = end x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let term = Expr::var("witness");
    let n1 = semantics.normalize_term(&typed, &term).unwrap();
    let n2 = semantics.normalize_term(&typed, &term).unwrap();
    assert_eq!(n1, n2);
}

#[test]
fn end_intro_elim_isomorphism_holds_in_both_directions() {
    let source = r#"
module EndsCoends.EndIsoBidirectional where

postulate C : Cat
postulate P : (x : C) -> Prop
postulate f : (x : C) -> P x
postulate h : end (x : C). P x
elim_after_intro : (x : C) -> P x = end^-1 (end f)
intro_after_elim : end (x : C). P x = end (end^-1 h)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let elim_after_intro = Expr::var("elim_after_intro");
    let f = Expr::var("f");
    let intro_after_elim = Expr::var("intro_after_elim");
    let h = Expr::var("h");

    let n_elim_after_intro = semantics.normalize_term(&typed, &elim_after_intro).unwrap();
    let n_f = semantics.normalize_term(&typed, &f).unwrap();
    let n_intro_after_elim = semantics.normalize_term(&typed, &intro_after_elim).unwrap();
    let n_h = semantics.normalize_term(&typed, &h).unwrap();

    assert_eq!(
        n_elim_after_intro, n_f,
        "end_elim(end_intro(f)) must be definitionally equal to f"
    );
    assert_eq!(
        n_intro_after_elim, n_h,
        "end_intro(end_elim(h)) must be definitionally equal to h"
    );
}

#[test]
fn malformed_end_coend_surface_forms_report_diagnostics() {
    let syntax = SyntaxEngine::default();
    let source = r#"
module EndsCoends.Bad where

postulate C : Cat
postulate P : (x : C) -> Prop
bad (x : C) : end (u : C P u = x
"#;
    let err = syntax.parse_module(source).unwrap_err();
    let bundle = err.into_diagnostics();
    assert!(!bundle.diagnostics.is_empty());
    for diagnostic in bundle.diagnostics {
        assert_eq!(diagnostic.severity, Severity::Error);
        assert!(!diagnostic.category.is_empty());
        assert!(!diagnostic.message.is_empty());
    }
}

#[test]
fn end_coend_variable_shadowing_is_rejected() {
    check_rejects(
        &[
            r#"
module EndsCoends.Shadowing.End where
postulate
  C : Cat
  P : (x : C) -> Prop
bad : Prop = end (x : C). (end (x : C). P x)
"#,
            r#"
module EndsCoends.Shadowing.Coend where
postulate
  C : Cat
  P : (x : C) -> Prop
bad : Prop = coend (x : C). (coend (x : C). P x)
"#,
            r#"
module EndsCoends.Shadowing.CrossQuantifier where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
bad : Prop = end (x : C). (coend (x : C). P x x)
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn yoneda_equational_law_has_semantic_boundary() {
    check_semantic_boundary(
        "yoneda",
        InferenceRule::EndElim,
        "probe",
        r#"
module EndsCoends.Yoneda.Positive where
postulate
  C : Cat
  F : (x : C) -> Prop
probe (x : C) : ((y : C) -> (x ->[C] y) -> F y) -> F x =
  \h. h x (refl x)
"#,
        r#"
module EndsCoends.Yoneda.Negative where
postulate
  C : Cat
  F : (x : C) -> Prop
probe : (x : C) -> ((y : C) -> (x ->[C] y) -> F y) -> F x -> F x
"#,
        Some("TypeTheory"),
    );
    reject_once(
        r#"
module EndsCoends.Yoneda.DiagnosticNegative where
postulate
  C : Cat
  F : (x : C) -> Prop
probe (x : C) : ((y : C) -> (x ->[C] y) -> F y) -> F x =
  \h. h x x
"#,
        "TypeTheory",
    );
}

#[test]
fn coyoneda_equational_law_has_semantic_boundary() {
    check_semantic_boundary(
        "CoYoneda",
        InferenceRule::CoendElim,
        "probe",
        r#"
module EndsCoends.CoYoneda.Positive where
postulate
  C : Cat
  F : (x : C) -> Prop
  lift : (x : C) -> F x
probe : coend (x : C). F x = coend lift
"#,
        r#"
module EndsCoends.CoYoneda.Negative where
postulate
  C : Cat
  F : (x : C) -> Prop
  lift : (x : C) -> F x
probe : (x : C) -> F x = coend lift
"#,
        Some("TypeTheory"),
    );
    reject_once(
        r#"
module EndsCoends.CoYoneda.DiagnosticNegative where
postulate
  C : Cat
  F : (x : C) -> Prop
  lift : (x : C) -> F x
probe : coend (x : C). F x = coend^-1 lift
"#,
        "TypeTheory",
    );
}

#[test]
fn fubini_exchange_equational_law_has_semantic_boundary() {
    check_semantic_boundary(
        "fubini_exchange",
        InferenceRule::EndIntro,
        "probe",
        r#"
module EndsCoends.Fubini.Positive where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  witness : end (x : C). end (y : C). P x y
probe : end (y : C). end (x : C). P x y = witness
"#,
        r#"
module EndsCoends.Fubini.Negative where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  witness : end (x : C). end (y : C). P x y
probe : end (y : C). end (x : C). P y x = witness
"#,
        Some("TypeTheory"),
    );
    reject_once(
        r#"
module EndsCoends.Fubini.DiagnosticNegative where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  witness : end (x : C). end (y : C). P x y
probe : end (y : C). end (x : C). P x y = end^-1 witness
"#,
        "TypeTheory",
    );
}

#[test]
fn end_and_coend_eliminators_reject_cross_contaminated_bindings() {
    check_rejects(
        &[
            r#"
module EndsCoends.CrossContamination.BadCoendElim where
postulate
  C : Cat
  P : (x : C) -> Prop
  h_end : end (x : C). P x
probe (a : C) : P a = (coend^-1 h_end) a
"#,
            r#"
module EndsCoends.CrossContamination.BadEndElim where
postulate
  C : Cat
  P : (x : C) -> Prop
  h_coend : coend (x : C). P x
probe (a : C) : P a = (end^-1 h_coend) a
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn figure16_end_nat_l_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_end_nat_l",
        InferenceRule::EndElim,
        "probe",
        r#"
module EndsCoends.Figure16.EndNatL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. t x ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. (\u. t x u) ((end^-1 h) x))) =
  seed t h
"#,
        r#"
module EndsCoends.Figure16.EndNatL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. t x ((end^-1 h) x)))
  opaque : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> end (x : C). Q x
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (opaque t h) =
  seed t h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_end_din_l_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_end_din_l",
        InferenceRule::EndElim,
        "probe",
        r#"
module EndsCoends.Figure16.EndDinL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((end^-1 h) x))
probe (x : C) (h : end (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x ((\u. t x u) ((end^-1 h) x)) =
  seed x h t
"#,
        r#"
module EndsCoends.Figure16.EndDinL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((end^-1 h) x))
  opaque : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Q x
probe (x : C) (h : end (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x (opaque x h t) =
  seed x h t
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_end_din_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_end_din_r",
        InferenceRule::EndElim,
        "probe",
        r#"
module EndsCoends.Figure16.EndDinR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (end (\x. t x (k x)))
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (end (\x. (\u. t x u) (k x))) =
  seed k t
"#,
        r#"
module EndsCoends.Figure16.EndDinR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (end (\x. t x (k x)))
  opaque : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> end (x : C). Q x
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (opaque k t) =
  seed k t
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_end_nat_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_end_nat_r",
        InferenceRule::EndIntro,
        "probe",
        r#"
module EndsCoends.Figure16.EndNatR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. (\u. t x u) ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed t h
"#,
        r#"
module EndsCoends.Figure16.EndNatR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. (\u. t x u) ((end^-1 h) x)))
  opaque : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> end (x : C). Q x
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (opaque t h) =
  seed t h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_end_iso_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_end_iso_r",
        InferenceRule::EndIntro,
        "probe",
        r#"
module EndsCoends.Figure16.EndIsoR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
probe (h : end (x : C). P x) : Obs (end (end^-1 h)) =
  seed h
"#,
        r#"
module EndsCoends.Figure16.EndIsoR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
  opaque : (h : end (x : C). P x) -> end (x : C). P x
probe (h : end (x : C). P x) : Obs (opaque h) =
  seed h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_iso_l_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_iso_l",
        InferenceRule::CoendElim,
        "probe",
        r#"
module EndsCoends.Figure16.CoendIsoL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
probe (k : (x : C) -> P x) : Obs (coend^-1 (coend k)) =
  seed k
"#,
        r#"
module EndsCoends.Figure16.CoendIsoL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
  opaque : ((x : C) -> P x) -> ((x : C) -> P x)
probe (k : (x : C) -> P x) : Obs (opaque k) =
  seed k
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_iso_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_iso_r",
        InferenceRule::CoendIntro,
        "probe",
        r#"
module EndsCoends.Figure16.CoendIsoR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : coend (x : C). P x) -> Prop
  seed : (h : coend (x : C). P x) -> Obs h
probe (h : coend (x : C). P x) : Obs (coend (coend^-1 h)) =
  seed h
"#,
        r#"
module EndsCoends.Figure16.CoendIsoR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : coend (x : C). P x) -> Prop
  seed : (h : coend (x : C). P x) -> Obs h
  opaque : (h : coend (x : C). P x) -> coend (x : C). P x
probe (h : coend (x : C). P x) : Obs (opaque h) =
  seed h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_nat_l_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_nat_l",
        InferenceRule::CoendElim,
        "probe",
        r#"
module EndsCoends.Figure16.CoendNatL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> Obs (coend (\x. t x ((coend^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : coend (x : C). P x) : Obs (coend (\x. (\u. t x u) ((coend^-1 h) x))) =
  seed t h
"#,
        r#"
module EndsCoends.Figure16.CoendNatL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> Obs (coend (\x. t x ((coend^-1 h) x)))
  opaque : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> coend (x : C). Q x
probe (t : (x : C) -> P x -> Q x) (h : coend (x : C). P x) : Obs (opaque t h) =
  seed t h
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_din_l_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_din_l",
        InferenceRule::CoendElim,
        "probe",
        r#"
module EndsCoends.Figure16.CoendDinL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : coend (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((coend^-1 h) x))
probe (x : C) (h : coend (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x ((\u. t x u) ((coend^-1 h) x)) =
  seed x h t
"#,
        r#"
module EndsCoends.Figure16.CoendDinL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : coend (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((coend^-1 h) x))
  opaque : (x : C) -> (h : coend (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Q x
probe (x : C) (h : coend (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x (opaque x h t) =
  seed x h t
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_din_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_din_r",
        InferenceRule::CoendElim,
        "probe",
        r#"
module EndsCoends.Figure16.CoendDinR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (coend (\x. t x (k x)))
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (coend (\x. (\u. t x u) (k x))) =
  seed k t
"#,
        r#"
module EndsCoends.Figure16.CoendDinR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (coend (\x. t x (k x)))
  opaque : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> coend (x : C). Q x
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (opaque k t) =
  seed k t
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn figure16_coend_nat_r_rule_has_semantic_boundary_in_ends_coends_suite() {
    check_semantic_boundary(
        "figure16_coend_nat_r",
        InferenceRule::CoendIntro,
        "probe",
        r#"
module EndsCoends.Figure16.CoendNatR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> Obs (coend (\x. (\u. t x u) ((coend^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : coend (x : C). P x) : Obs (coend (\x. t x ((coend^-1 h) x))) =
  seed t h
"#,
        r#"
module EndsCoends.Figure16.CoendNatR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : coend (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> Obs (coend (\x. (\u. t x u) ((coend^-1 h) x)))
  opaque : (t : (x : C) -> P x -> Q x) -> (h : coend (x : C). P x) -> coend (x : C). Q x
probe (t : (x : C) -> P x -> Q x) (h : coend (x : C). P x) : Obs (opaque t h) =
  seed t h
"#,
        Some("TypeTheory"),
    );
}
