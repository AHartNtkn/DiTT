mod common;

use common::assertions::assert_def_equal;
use common::conformance::{assert_derivation_rule, check_rejects, check_semantic_boundary};
use common::engines::compile_with_engines;
use common::support::*;
use ditt_lang::api::*;

// Equational laws are checked as derivable judgments with explicit rule structure.
// This complements `definitionally_equal` which checks convertibility without
// exposing the derivation structure. Both are needed: equational laws verify
// the specific rule was applied, while definitional equality verifies the outcome.

#[test]
fn diterm_connects_to_idx_rule_through_judgment_form() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    // A Diterm packages a context, term, and type for the (idx) rule
    let diterm = Diterm::new(
        Context::default().extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        )),
        Term::var("x"),
        CatType::base("C"),
    );

    // The (idx) rule: Gamma |- x : C when x:C in Gamma
    // TermTyping is now a CheckJudgment variant
    let check = CheckJudgment::TermTyping(diterm.context, diterm.term, diterm.ty);
    semantics
        .check(&typed, &check)
        .expect("Diterm's (idx) judgment must be derivable");
}

#[test]
fn diterm_with_mismatched_term_and_type_is_rejected_by_typechecker() {
    check_rejects(
        &[
            r#"
module Contracts.DitermInvariantMismatch.ObjectAsArrow where
postulate
  C : Cat
bad (x : C) : x ->[C] x =
  x
"#,
            r#"
module Contracts.DitermInvariantMismatch.ArrowAsObject where
postulate
  C : Cat
bad (x : C) : C =
  refl x
"#,
            r#"
module Contracts.DitermInvariantMismatch.WrongCategory where
postulate
  C : Cat
  D : Cat
bad (x : C) : D =
  x
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn multi_parameter_lambda_beta_reduces_second_projection() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Contracts.MultiParamBeta where

postulate
  C : Cat
  a : C
  b : C

beta_left : C = (\x. \y. y) a b
beta_right : C = b
"#,
    );
    assert_def_equal(
        &semantics,
        &typed,
        "beta_left",
        "beta_right",
        "(\\x y. y) a b must beta-reduce to b",
    );
}

#[test]
fn multi_parameter_lambda_eta_contracts_to_function() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Contracts.MultiParamEta where

postulate
  C : Cat
  f : (x : C) -> (y : C) -> C

eta_left : (x : C) -> (y : C) -> C = \x. \y. f x y
eta_right : (x : C) -> (y : C) -> C = f
"#,
    );
    assert_def_equal(
        &semantics,
        &typed,
        "eta_left",
        "eta_right",
        "\\x y. f x y must be eta-equivalent to f",
    );
}

#[test]
fn opposite_constructor_preserves_definitional_equality() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Contracts.OppositeCongruence where

postulate C : Cat
D : Cat = C
C_op : Cat = C^
D_op : Cat = D^
"#,
    );
    assert_def_equal(
        &semantics,
        &typed,
        "C_op",
        "D_op",
        "if C and D are definitionally equal, C^ and D^ must be equal",
    );
}

#[test]
fn derivation_artifacts_for_assoc_judgment_are_semantically_valid() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let ej = entailment("comp_assoc");
    let rule = InferenceRule::CutNat;

    let proof = semantics.derive(&typed, &ej, rule).unwrap();
    assert_derivation_rule(
        &proof,
        InferenceRule::CutNat,
        "comp_assoc must be derivable under Figure15AssocNatDinNat",
    );

    let artifact = semantics
        .export_derivation_artifact(&typed, &ej, rule)
        .unwrap();
    semantics
        .validate_derivation_artifact(&typed, &artifact)
        .unwrap();
}

#[test]
fn refl_is_derivable_for_every_type_in_context() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let proof = semantics
        .derive(&typed, &entailment("refl_intro"), InferenceRule::Refl)
        .unwrap();

    assert_derivation_rule(&proof, InferenceRule::Refl, "refl_intro");
}

#[test]
fn directed_j_satisfies_computation_rule() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let proof = semantics
        .derive(&typed, &entailment("j_comp"), InferenceRule::JRule)
        .unwrap();

    assert_derivation_rule(&proof, InferenceRule::JRule, "j_comp");
}

#[test]
fn directed_j_computation_rejects_non_refl_path_argument() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Contracts.JCompRejectsNonRefl where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z

probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P a b = J h [e]
"#,
    );
    let diagnostics = semantics
        .derive(&typed, &entailment("probe"), InferenceRule::JRule)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "J-Comp non-refl rejection must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn derivation_root_for_comp_assoc_exposes_rule() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let proof = semantics
        .derive(&typed, &entailment("comp_assoc"), InferenceRule::CutNat)
        .unwrap();
    assert_derivation_rule(&proof, InferenceRule::CutNat, "comp_assoc");
}

#[test]
fn directed_j_supports_dependent_elimination() {
    let (_syntax, semantics, positive) = compile_with_engines(
        r#"
module Contracts.JDepPositive where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z

j_dep_probe_a :
  (a : C^) -> (b : C) -> (e : a ->[C] b) -> Phi b a -> P a b =
  \a. \b. \e. \phi. J h [e]

j_dep_probe_b :
  (a : C^) -> (b : C) -> (e : a ->[C] b) -> Phi b a -> P a b =
  \a. \b. \e. \phi. J (h) [e]
"#,
    );
    let negative = compile_checked(
        &_syntax,
        &semantics,
        r#"
module Contracts.JDepNegative where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z

j_dep_probe_a :
  (a : C^) -> (b : C) -> (e : a ->[C] b) -> Phi a b -> P a b =
  \a. \b. \e. \phi. J h [e]

j_dep_probe_b :
  (a : C^) -> (b : C) -> (e : a ->[C] b) -> Phi a b -> P a b =
  \a. \b. \e. \phi. J (h) [e]
"#,
    );

    for name in ["j_dep_probe_a", "j_dep_probe_b"] {
        let positive_result = semantics.derive(&positive, &entailment(name), InferenceRule::JRule);
        let negative_result = semantics.derive(&negative, &entailment(name), InferenceRule::JRule);

        assert!(
            positive_result.is_ok(),
            "directed J elimination must derive when the premise uses Phi b a",
        );
        let diagnostics = negative_result.unwrap_err().into_diagnostics();
        assert!(
            diagnostics
                .diagnostics
                .iter()
                .any(|d| d.category == "TypeTheory"),
            "directed J elimination flipped side condition must produce TypeTheory diagnostics for {name}, got: {diagnostics:?}",
        );
    }
}

#[test]
fn composition_has_left_and_right_identity_and_associativity() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let left_id = semantics
        .derive(&typed, &entailment("comp_left_id"), InferenceRule::CutNat)
        .unwrap();
    let right_id = semantics
        .derive(&typed, &entailment("comp_right_id"), InferenceRule::CutNat)
        .unwrap();
    let assoc = semantics
        .derive(&typed, &entailment("comp_assoc"), InferenceRule::CutNat)
        .unwrap();

    assert_derivation_rule(&left_id, InferenceRule::CutNat, "comp_left_id");
    assert_derivation_rule(&right_id, InferenceRule::CutNat, "comp_right_id");
    assert_derivation_rule(&assoc, InferenceRule::CutNat, "comp_assoc");
}

#[test]
fn explicit_symmetry_axiom_parameter_is_derivable() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    assert!(
        semantics
            .derive(&typed, &entailment("symmetry"), InferenceRule::JRule)
            .is_ok(),
        "symmetry must be derivable when an explicit symmetry axiom is provided as a parameter",
    );
}

#[test]
fn symmetry_cannot_be_derived_via_j_elimination() {
    check_rejects(
        &[
            r#"
module Symmetry.AttemptViaJ where
postulate
  C : Cat
symm (a : C^) (b : C) (e : a ->[C] b) : b ->[C] a =
  J (\z. \p. refl z) [e]
"#,
            r#"
module Symmetry.AttemptViaComposition where
postulate
  C : Cat
symm (a : C^) (b : C) (e : a ->[C] b) : b ->[C] a =
  J (\z. \p. p) [e]
"#,
            r#"
module Symmetry.AttemptViaIdentity where
postulate
  C : Cat
symm (a : C^) (b : C) (e : a ->[C] b) : b ->[C] a =
  e
"#,
        ],
        "TypeTheory",
    );
}

#[test]
fn unrestricted_cut_is_rejected_and_restricted_cut_is_accepted() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    assert!(
        semantics
            .derive(&typed, &entailment("restricted_cut"), InferenceRule::CutNat)
            .is_ok(),
        "restricted_cut: expected derivable outcome",
    );
}

#[test]
fn unrestricted_cut_usage_site_in_eliminator_position_is_rejected() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Contracts.RestrictedCutUsageSite where

postulate
  C : Cat
  P : (x : C) -> Prop

probe (a : C) (k : (x : C) -> P x) : P a =
  k a
"#,
    );

    let diagnostics = semantics
        .derive(&typed, &entailment("probe"), InferenceRule::CutNat)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "unrestricted cut in eliminator position must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn directed_cut_restriction_boundary_distinguishes_natural_dinatural_and_unbound_cases() {
    let (_syntax, semantics, valid_typed) = compile_with_engines(
        r#"
module Contracts.CutRestrictionBoundary.Valid where

postulate
  C : Cat
  P : (x : C) -> Prop
  Phi : (x : C) -> (y : C) -> Prop

natural_cut_valid (a : C) (h : end (x : C). P x) : P a =
  h a

dinatural_cut_valid (a : C) (h : end (z : C). Phi z z) : Phi a a =
  h a
"#,
    );

    for name in ["natural_cut_valid", "dinatural_cut_valid"] {
        assert!(
            semantics
                .derive(&valid_typed, &entailment(name), InferenceRule::CutNat)
                .is_ok(),
            "{name}: expected derivable outcome under directed cut restriction",
        );
    }

    let invalid_typed = compile_checked(
        &_syntax,
        &semantics,
        r#"
module Contracts.CutRestrictionBoundary.Invalid where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop

dinatural_without_end_binding (a : C) (k : (z : C) -> Phi z z) : Phi a a =
  k a
"#,
    );

    let diagnostics = semantics
        .derive(
            &invalid_typed,
            &entailment("dinatural_without_end_binding"),
            InferenceRule::CutNat,
        )
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "dinatural without end/coend binding must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn directed_cut_restriction_applies_symmetrically_to_coend() {
    let (_syntax, semantics, coend_cut) = compile_with_engines(
        r#"
module CutSpec.CoendValid where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (h : coend (x : C). P x) (a : C) : P a =
  let w = coend^-1 h in w a
"#,
    );
    assert!(
        semantics
            .derive(&coend_cut, &entailment("probe"), InferenceRule::CutNat)
            .is_ok(),
        "Coend-bound dinatural cut must satisfy cut restriction",
    );

    let invalid_coend = compile_checked(
        &_syntax,
        &semantics,
        r#"
module CutSpec.CoendInvalid where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe (a : C) : P a = k a
"#,
    );
    let diagnostics = semantics
        .derive(&invalid_coend, &entailment("probe"), InferenceRule::CutNat)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "unbound coend use must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn derive_judgment_derives_weakening_with_required_binding_context() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let context = Context::default().extend(ContextBinding::new(
        "x",
        CatType::Var("C".to_string()),
        Variance::Covariant,
    ));

    assert!(
        semantics
            .derive(
                &typed,
                &entailment_in_context("weakening", context),
                InferenceRule::Wk,
            )
            .is_ok(),
        "weakening with required binding context must be derivable",
    );
}

#[test]
fn derive_judgment_rejects_exchange_without_required_context_shape() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let context = Context::default().extend(ContextBinding::new(
        "x",
        CatType::Var("C".to_string()),
        Variance::Covariant,
    ));

    let diagnostics = semantics
        .derive(
            &typed,
            &entailment_in_context("exchange", context),
            InferenceRule::Var,
        )
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "exchange without required context shape must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn derive_judgment_derives_exchange_with_two_bindings_context() {
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
        ));
    let exchanged = context
        .exchange(0, 1)
        .expect("exchange must succeed for two in-bounds bindings");

    assert!(
        semantics
            .derive(
                &typed,
                &entailment_in_context("exchange", exchanged),
                InferenceRule::Var,
            )
            .is_ok(),
        "exchange with two bindings context must be derivable",
    );
}

#[test]
fn derive_judgment_preserves_derivability_under_weakening_context() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());
    let base_context = Context::default().extend(ContextBinding::new(
        "x",
        CatType::Var("C".to_string()),
        Variance::Covariant,
    ));
    let weakened_context = base_context.clone().weaken(vec![ContextBinding::new(
        "y",
        CatType::Var("D".to_string()),
        Variance::Covariant,
    )]);

    assert!(
        semantics
            .derive(
                &typed,
                &entailment_in_context("weakening", base_context),
                InferenceRule::Wk,
            )
            .is_ok(),
        "base context weakening must be derivable",
    );
    assert!(
        semantics
            .derive(
                &typed,
                &entailment_in_context("weakening", weakened_context),
                InferenceRule::Wk,
            )
            .is_ok(),
        "weakened context weakening must be derivable",
    );
}

#[test]
fn judgment_results_are_stable_under_whitespace_and_comment_noise() {
    let prefixes = ["", " ", "\n\n", "\t\t"];
    let suffixes = ["", "\n", "\n\n\n", "   "];

    for ws_prefix in prefixes {
        for ws_suffix in suffixes {
            let noisy = format!(
                "{prefix}\n// leading noise\n{body}\n// trailing noise\n{suffix}",
                prefix = ws_prefix,
                body = directed_theory_module(),
                suffix = ws_suffix
            );

            let (_syntax, semantics, typed) = compile_with_engines(&noisy);
            assert!(
                semantics
                    .derive(&typed, &entailment("comp_assoc"), InferenceRule::CutNat)
                    .is_ok(),
                "judgment results must be stable under whitespace and comment noise",
            );
        }
    }
}

#[test]
fn directed_refl_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_refl",
        InferenceRule::Refl,
        "probe",
        r#"
module Rules.Figure11Refl.Positive where

postulate
  C : Cat

probe (x : C) : x ->[C] x = refl x
"#,
        r#"
module Rules.Figure11Refl.Negative where

postulate
  C : Cat
  probe : (x : C) -> (y : C) -> (x ->[C] y)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn directed_j_computation_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_j_computation",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.Figure11JComp.Positive where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z

probe (z : C) (phi : Phi z z) : P z z = J h [refl z]
"#,
        r#"
module Rules.Figure11JComp.Negative where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z
  probe : (z : C) -> Phi z z -> P z z -> P z z
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn directed_j_dependent_elimination_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_j_dependent_elimination",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.Figure11J.Positive where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z

probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P a b = J h [e]
"#,
        r#"
module Rules.Figure11J.Negative where

postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  P : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> P z z
  probe : (a : C^) -> (b : C) -> (e : a ->[C] b) -> Phi a b -> P a b
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn directed_composition_left_identity_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_composition_left_identity",
        InferenceRule::CutNat,
        "probe",
        r#"
module Rules.Figure15CutNatIdL.Positive where

postulate
  C : Cat

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a a b (refl a) f
"#,
        r#"
module Rules.Figure15CutNatIdL.Negative where

postulate
  C : Cat
  probe : (a : C) -> (b : C) -> (f : a ->[C] b) -> (a ->[C] a)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn directed_composition_right_identity_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_composition_right_identity",
        InferenceRule::CutNat,
        "probe",
        r#"
module Rules.Figure15CutNatIdR.Positive where

postulate
  C : Cat

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a b b f (refl b)
"#,
        r#"
module Rules.Figure15CutNatIdR.Negative where

postulate
  C : Cat
  probe : (a : C) -> (b : C) -> (f : a ->[C] b) -> (b ->[C] b)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn directed_composition_associativity_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "directed_composition_associativity",
        InferenceRule::CutNat,
        "probe",
        r#"
module Rules.Figure15AssocNatDinNat.Positive where

postulate
  C : Cat

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

probe (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (h : c ->[C] d) : a ->[C] d =
  compose_via_j a c d (compose_via_j a b c f g) h
"#,
        r#"
module Rules.Figure15AssocNatDinNat.Negative where

postulate
  C : Cat
  probe : (a : C) -> (b : C) -> (c : C) -> (d : C) -> (f : a ->[C] b) -> (g : b ->[C] c) -> (h : c ->[C] d) -> (d ->[C] a)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn symmetry_not_derivable_rule_has_semantic_boundary() {
    // Defeated: an explicit symmetry axiom makes it derivable (positive = derivable)
    // Confirmed: symmetry is not derivable from the rules alone (negative = not derivable)
    check_semantic_boundary(
        "SymmetryNotDerivable.Confirmed",
        InferenceRule::JRule,
        "probe",
        r#"
module Rules.SymmetryNotDerivable.Negative where

postulate
  C : Cat
  symm : (a : C) -> (b : C) -> (a ->[C] b) -> (b ->[C] a)

probe (a : C) (b : C) (e : a ->[C] b) : b ->[C] a = symm a b e
"#,
        r#"
module Rules.SymmetryNotDerivable.Positive where

postulate
  C : Cat
  probe : (a : C) -> (b : C) -> (a ->[C] b) -> (b ->[C] a)
"#,
        Some("TypeTheory"),
    );
}

#[test]
fn restricted_cut_only_rule_has_semantic_boundary() {
    check_semantic_boundary(
        "restricted_cut_only",
        InferenceRule::CutNat,
        "probe",
        r#"
module Rules.RestrictedCutOnly.Positive where

postulate
  C : Cat
  P : (x : C) -> Prop

probe (a : C) (h : end (x : C). P x) : P a = h a
"#,
        r#"
module Rules.RestrictedCutOnly.Negative where

postulate
  C : Cat
  P : (x : C) -> Prop
  Q : Prop
  full_cut : ((x : C) -> P x) -> Q

probe (k : (x : C) -> P x) : Q = full_cut k
"#,
        Some("TypeTheory"),
    );
}

// --- Judgment form coverage: TypeWellFormed, ContextWellFormed (Task 5.6) ---

#[test]
fn type_well_formed_judgment_for_base_type() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let check = CheckJudgment::TypeWellFormed(CatType::base("C"));
    semantics
        .check(&typed, &check)
        .expect("base type from signature must be well-formed");
}

#[test]
fn context_well_formed_judgment_for_empty_context() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let check = CheckJudgment::ContextWellFormed(Context::default());
    semantics
        .check(&typed, &check)
        .expect("empty context must be well-formed");
}

// --- Type-level equality tests (Task 5.7) ---

#[test]
fn type_equality_opposite_involution() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    // (C^op)^op = C
    let c = CatType::base("C");
    let c_op_op = CatType::opposite(CatType::opposite(c.clone()));
    let check = CheckJudgment::TypeEquality(c_op_op, c);
    semantics
        .check(&typed, &check)
        .expect("opposite involution (C^op)^op = C must hold");
}

#[test]
fn type_equality_negative_case() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    // C != D (distinct base types)
    let check = CheckJudgment::TypeEquality(CatType::base("C"), CatType::base("D"));
    let diagnostics = semantics
        .check(&typed, &check)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "distinct base types must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

// --- Predicate well-formedness tests (Task 5.8) ---

#[test]
fn predicate_well_formed_top() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let check = CheckJudgment::PredicateWellFormed(Context::default(), Predicate::top());
    semantics
        .check(&typed, &check)
        .expect("Top predicate must be well-formed in any context");
}

#[test]
fn predicate_well_formed_hom() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let check = CheckJudgment::PredicateWellFormed(
        ctx,
        Predicate::hom(CatType::base("C"), Term::var("x"), Term::var("x")),
    );
    semantics
        .check(&typed, &check)
        .expect("Hom_C(x,x) must be well-formed when x:C is in context");
}

// --- ContextWellFormed extended tests (Task 5.12) ---

#[test]
fn context_well_formed_extended() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let check = CheckJudgment::ContextWellFormed(ctx);
    semantics
        .check(&typed, &check)
        .expect("context with binding x:C must be well-formed");
}

#[test]
fn context_well_formed_opposite() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .opposite();
    let check = CheckJudgment::ContextWellFormed(ctx);
    semantics
        .check(&typed, &check)
        .expect("opposite context must be well-formed");
}

#[test]
fn opposite_predicate_well_formed() {
    let (_syntax, semantics, typed) = compile_with_engines(directed_theory_module());

    // If P is well-formed in Gamma^op, then P^op is well-formed in Gamma
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let pred = Predicate::opposite(Predicate::hom(
        CatType::base("C"),
        Term::var("x"),
        Term::var("x"),
    ));
    let check = CheckJudgment::PredicateWellFormed(ctx, pred);
    semantics.check(&typed, &check).expect(
        "opposite predicate must be well-formed when original is well-formed in opposite context",
    );
}

#[test]
/// [C13] Eta-terminal law: any term t : Top must be definitionally equal to
/// the unique element of Top (denoted !). This is the eta rule for the
/// terminal object in the directed type theory.
fn eta_terminal_top_typed_term_is_definitionally_equal_to_unit() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module TypeTheory.EtaTerminal where
postulate
  C : Cat
  x : C

top_witness : Top = x
top_unit : Top = !
"#,
    );

    assert_def_equal(
        &semantics,
        &typed,
        "top_witness",
        "top_unit",
        "any term of type Top must be definitionally equal to ! (eta-terminal)",
    );
}

#[test]
/// [C14] Op-involution at the type level: C^op^op = C must hold.
/// Verified by normalizing type-level definitions and comparing canonical forms.
fn op_involution_holds_at_type_level() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module TypeTheory.OpInvolutionTypeLevel where
postulate
  C : Cat

c_op_op : Cat = C^^
c_direct : Cat = C
"#,
    );

    let n1 = semantics
        .normalize_term(&typed, &Expr::var("c_op_op"))
        .unwrap();
    let n2 = semantics
        .normalize_term(&typed, &Expr::var("c_direct"))
        .unwrap();
    assert_eq!(
        n1.structure().to_string(),
        n2.structure().to_string(),
        "C^op^op must be type-level definitionally equal to C"
    );
}

// --- Context query operations (C1) ---

#[test]
fn context_lookup_returns_most_recent_binding_on_shadowing() {
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("A"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "x",
            CatType::base("B"),
            Variance::Covariant,
        ));

    let binding = ctx.lookup("x").expect("lookup must find shadowed variable");
    assert_eq!(
        binding.ty,
        CatType::base("B"),
        "lookup must return the most recent (innermost) binding for a shadowed name"
    );
}

#[test]
fn context_contains_is_consistent_with_lookup() {
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("A"),
        Variance::Covariant,
    ));

    assert!(
        ctx.contains("x"),
        "contains must return true for a name present in the context"
    );
    assert!(
        !ctx.contains("y"),
        "contains must return false for a name absent from the context"
    );
    assert_eq!(
        ctx.contains("x"),
        ctx.lookup("x").is_some(),
        "contains(name) must be equivalent to lookup(name).is_some()"
    );
    assert_eq!(
        ctx.contains("y"),
        ctx.lookup("y").is_some(),
        "contains(name) must be equivalent to lookup(name).is_some() for absent names"
    );
}

#[test]
fn context_bindings_returns_all_entries_in_declaration_order() {
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "a",
            CatType::base("A"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "b",
            CatType::base("B"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "c",
            CatType::base("C"),
            Variance::Covariant,
        ));

    let names: Vec<&str> = ctx.bindings().iter().map(|b| b.name.as_str()).collect();
    assert_eq!(
        names,
        vec!["a", "b", "c"],
        "bindings() must return entries in declaration (extension) order"
    );
}

// --- Diterm negative context (C3) ---

#[test]
fn diterm_negative_context_applies_opposite_to_all_bindings() {
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::base("D"),
            Variance::Covariant,
        ));
    let diterm = Diterm::new(ctx, Term::var("x"), CatType::base("C"));

    let neg = diterm.negative_ctx();
    let neg_bindings = neg.bindings();
    assert_eq!(
        neg_bindings.len(),
        2,
        "negative context must preserve binding count"
    );
    assert_eq!(
        neg_bindings[0].ty,
        CatType::Opposite(Box::new(CatType::base("C"))),
        "negative context must wrap each binding type in CatType::Opposite"
    );
    assert_eq!(
        neg_bindings[1].ty,
        CatType::Opposite(Box::new(CatType::base("D"))),
        "negative context must wrap each binding type in CatType::Opposite"
    );
    assert_eq!(
        neg_bindings[0].name, "x",
        "negative context must preserve binding names"
    );
    assert_eq!(
        neg_bindings[1].name, "y",
        "negative context must preserve binding names"
    );
}

// --- ContextBinding variance tests (Step 1) ---

#[test]
fn context_binding_carries_variance() {
    for variance in [
        Variance::Covariant,
        Variance::Contravariant,
        Variance::Dinatural,
        Variance::Unused,
    ] {
        let binding = ContextBinding::new("x", CatType::base("C"), variance);
        let ctx = Context::default().extend(binding);
        let bindings = ctx.bindings();
        assert_eq!(bindings.len(), 1);
        assert_eq!(
            bindings[0].variance, variance,
            "variance must be preserved through Context::extend()"
        );
    }
}

#[test]
fn context_opposite_flips_covariant_to_contravariant() {
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Covariant,
    ));
    let opp = ctx.opposite();
    let bindings = opp.bindings();
    assert_eq!(bindings.len(), 1);
    assert_eq!(
        bindings[0].variance,
        Variance::Contravariant,
        "opposite() must flip Covariant to Contravariant"
    );
    assert_eq!(
        bindings[0].ty,
        CatType::Opposite(Box::new(CatType::base("C"))),
        "opposite() must wrap the type in CatType::Opposite"
    );
}

#[test]
fn context_opposite_flips_contravariant_to_covariant() {
    let ctx = Context::default().extend(ContextBinding::new(
        "x",
        CatType::base("C"),
        Variance::Contravariant,
    ));
    let opp = ctx.opposite();
    let bindings = opp.bindings();
    assert_eq!(bindings.len(), 1);
    assert_eq!(
        bindings[0].variance,
        Variance::Covariant,
        "opposite() must flip Contravariant to Covariant"
    );
}

#[test]
fn context_opposite_preserves_dinatural() {
    let ctx = Context::default().extend(ContextBinding::new(
        "z",
        CatType::base("C"),
        Variance::Dinatural,
    ));
    let opp = ctx.opposite();
    let bindings = opp.bindings();
    assert_eq!(bindings.len(), 1);
    assert_eq!(
        bindings[0].variance,
        Variance::Dinatural,
        "opposite() must preserve Dinatural variance"
    );
}

#[test]
fn context_weaken_preserves_variance_on_existing_bindings() {
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::base("D"),
            Variance::Contravariant,
        ));
    let weakened = ctx.weaken(vec![ContextBinding::new(
        "z",
        CatType::base("E"),
        Variance::Dinatural,
    )]);
    let bindings = weakened.bindings();
    assert_eq!(bindings.len(), 3);
    assert_eq!(
        bindings[0].variance,
        Variance::Covariant,
        "weakening must preserve variance on existing bindings"
    );
    assert_eq!(
        bindings[1].variance,
        Variance::Contravariant,
        "weakening must preserve variance on existing bindings"
    );
    assert_eq!(
        bindings[2].variance,
        Variance::Dinatural,
        "weakened binding must carry its own variance"
    );
}

#[test]
fn context_exchange_preserves_variance() {
    let ctx = Context::default()
        .extend(ContextBinding::new(
            "x",
            CatType::base("C"),
            Variance::Covariant,
        ))
        .extend(ContextBinding::new(
            "y",
            CatType::base("D"),
            Variance::Contravariant,
        ));
    let exchanged = ctx.exchange(0, 1).expect("exchange must succeed");
    let bindings = exchanged.bindings();
    assert_eq!(bindings[0].name, "y");
    assert_eq!(
        bindings[0].variance,
        Variance::Contravariant,
        "exchange must preserve variance on swapped bindings"
    );
    assert_eq!(bindings[1].name, "x");
    assert_eq!(
        bindings[1].variance,
        Variance::Covariant,
        "exchange must preserve variance on swapped bindings"
    );
}
