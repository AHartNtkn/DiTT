mod common;

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use common::conformance::{check_accepts, check_rejects, parse_csv};

#[test]
/// Appendix registry contract: all appendix examples are present, unique, and linked to executable tests.
fn appendix_examples_registry_is_complete_unique_and_linked() {
    let (header, rows) = parse_csv("conformance/semantics/paper_appendix_examples.csv");
    assert_eq!(header, vec!["id", "name", "contract_id", "expected"]);
    assert_eq!(rows.len(), 11);

    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    let mut expected_ids = BTreeSet::new();
    for id in [
        "ExB_1ContractibilityOfSingletons",
        "ExB_2InternalNaturalityForNaturals",
        "ExB_3IdentityNaturalTransformation",
        "ExB_4CompositionOfNaturalTransformations",
        "ExB_5DirectedEqualityInOppositeCategories",
        "ExC_1EliminationForCoends",
        "ExC_2IntroductionForCoendsWithTerm",
        "ExC_3IntroductionForCoendsWithDinaturalVariable",
        "ExD_1PointwiseFormulaForLeftKan",
        "ExD_2RightLiftsInProfunctors",
        "ExD_3AssociativityOfProfunctorComposition",
    ] {
        expected_ids.insert(id.to_string());
    }

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for row in rows {
        assert_eq!(row.len(), 4);
        assert!(ids.insert(row[0].clone()));
        assert!(names.insert(row[1].clone()));
        assert_eq!(row[3], "Derivable");

        let (path, symbol) = row[2].split_once("::").unwrap();
        let body = fs::read_to_string(root.join(path)).unwrap();
        assert!(
            body.contains(&format!("fn {symbol}")),
            "missing contract symbol: {}",
            row[2]
        );
    }

    assert_eq!(ids, expected_ids);
}

#[test]
/// ExB.1: contractibility/singleton witness requires correct coend elimination shape.
fn exb_1_contractibility_of_singletons_contract() {
    check_accepts(
        r#"
module Paper.ExB_1 where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
singleton : coend (x : C). P x =
  coend k
exb_1_contractibility_of_singletons (x : C) : P x =
  (coend^-1 singleton) x
"#,
    );
    let neg = r#"
module Paper.ExB_1.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
singleton : coend (x : C). P x =
  coend k
exb_1_contractibility_of_singletons (x : C) : P x =
  coend^-1 (singleton x)
"#;
    let neg_bad_head = neg.replacen(
        "coend^-1 (singleton x)",
        "(coend^-1 singleton) singleton",
        1,
    );
    let neg_treat_as_function = neg.replacen("coend^-1 (singleton x)", "singleton x", 1);
    check_rejects(&[neg, &neg_bad_head, &neg_treat_as_function], "TypeTheory");
}

#[test]
/// ExB.2: internal naturality uses `J` with correctly oriented edge and component family.
fn exb_2_internal_naturality_for_naturals_contract() {
    check_accepts(
        r#"
module Paper.ExB_2 where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  G : (x : C) -> D
diag (z : C) : (F z ->[D] G z) -> (F z ->[D] G z) =
  \m. m
exb_2_internal_naturality_for_naturals (a : C^) (b : C) (f : a ->[C] b) (eta : F b ->[D] G b) : F a ->[D] G b =
  (J diag [f]) eta
"#,
    );
    let neg = r#"
module Paper.ExB_2.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  G : (x : C) -> D
diag (z : C) : (F z ->[D] G z) -> (F z ->[D] G z) =
  \m. m
exb_2_internal_naturality_for_naturals (a : C^) (b : C) (f : a ->[C] b) (eta : F a ->[D] G b) : F a ->[D] G b =
  (J diag [f]) eta
"#;
    let neg_wrong_j_application = neg.replacen("(J diag [f]) eta", "J diag [f]", 1);
    let neg_wrong_edge = neg.replacen("J diag [f]", "J diag [eta]", 1);
    check_rejects(
        &[neg, &neg_wrong_j_application, &neg_wrong_edge],
        "TypeTheory",
    );
}

#[test]
/// ExB.3: identity natural transformation is the end of pointwise identities over `F`.
fn exb_3_identity_natural_transformation_contract() {
    check_accepts(
        r#"
module Paper.ExB_3 where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
exb_3_identity_natural_transformation : end (x : C). F x ->[D] F x =
  end (\x. refl (F x))
"#,
    );
    let neg = r#"
module Paper.ExB_3.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
exb_3_identity_natural_transformation : end (x : C). F x ->[D] F x =
  end (\x. refl x)
"#;
    let neg_bad_result = neg.replacen("end (\\x. refl x)", "end^-1 (end (\\x. refl x))", 1);
    let neg_bad_hom = neg.replacen("refl x", "x", 1);
    check_rejects(&[neg, &neg_bad_result, &neg_bad_hom], "TypeTheory");
}

#[test]
/// ExB.4: composition of natural transformations preserves pointwise order of components.
fn exb_4_composition_of_natural_transformations_contract() {
    check_accepts(
        r#"
module Paper.ExB_4 where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  G : (x : C) -> D
  H : (x : C) -> D
  composeD : (u : D) -> (v : D) -> (w : D) -> (u ->[D] v) -> (v ->[D] w) -> (u ->[D] w)
exb_4_composition_of_natural_transformations
  (l : end (x : C). F x ->[D] G x)
  (r : end (x : C). G x ->[D] H x)
  : end (x : C). F x ->[D] H x =
  end (\x. composeD (F x) (G x) (H x) ((end^-1 l) x) ((end^-1 r) x))
"#,
    );
    let neg = r#"
module Paper.ExB_4.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  G : (x : C) -> D
  H : (x : C) -> D
  composeD : (u : D) -> (v : D) -> (w : D) -> (u ->[D] v) -> (v ->[D] w) -> (u ->[D] w)
exb_4_composition_of_natural_transformations
  (l : end (x : C). F x ->[D] G x)
  (r : end (x : C). G x ->[D] H x)
  : end (x : C). F x ->[D] H x =
  end (\x. composeD (F x) (G x) (H x) ((end^-1 r) x) ((end^-1 l) x))
"#;
    let neg_bad_component = neg.replacen("((end^-1 l) x)", "r", 1);
    let neg_bad_result = neg.replacen(
        "end (\\x. composeD (F x) (G x) (H x) ((end^-1 r) x) ((end^-1 l) x))",
        "composeD (F x) (G x) (H x) ((end^-1 r) x) ((end^-1 l) x)",
        1,
    );
    check_rejects(&[neg, &neg_bad_component, &neg_bad_result], "TypeTheory");
}

#[test]
/// ExB.5: directed equality in opposite categories preserves edge orientation in the result hom.
fn exb_5_directed_equality_in_opposite_categories_contract() {
    check_accepts(
        r#"
module Paper.ExB_5 where
postulate
  C : Cat
diag (z : C) : z ->[C] z =
  refl z
exb_5_directed_equality_in_opposite_categories (x : C^) (y : C) (f : x ->[C] y) : x ->[C] y =
  J (\z. \k. k) [f]
"#,
    );
    let neg = r#"
module Paper.ExB_5.Negative where
postulate
  C : Cat
diag (z : C) : z ->[C] z =
  refl z
exb_5_directed_equality_in_opposite_categories (x : C^) (y : C) (f : x ->[C] y) : y ->[C] x =
  J (\z. \k. k) [f]
"#;
    let neg_bad_edge = neg.replacen("J (\\z. \\k. k) [f]", "J (\\z. \\k. k) [y]", 1);
    let neg_bad_body = neg.replacen("J (\\z. \\k. k) [f]", "(J (\\z. \\k. k) [f]) f", 1);
    check_rejects(&[neg, &neg_bad_edge, &neg_bad_body], "TypeTheory");
}

#[test]
/// ExC.1: coend elimination must unpack a coend before feeding the eliminator `h`.
fn exc_1_elimination_for_coends_contract() {
    check_accepts(
        r#"
module Paper.ExC_1 where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : Prop
  choose : C
  h : (z : C) -> P z -> Q
ex_c_1_elim (u : coend (x : C). P x) : Q =
  h choose ((coend^-1 u) choose)
"#,
    );
    let neg = r#"
module Paper.ExC_1.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : Prop
  choose : C
  h : (z : C) -> P z -> Q
ex_c_1_elim (u : coend (x : C). P x) : Q =
  h choose (coend u)
"#;
    let neg_bad_arg = neg.replacen("h choose (coend u)", "h choose ((coend^-1 u) u)", 1);
    let neg_bad_head = neg.replacen("h choose (coend u)", "coend^-1 u", 1);
    check_rejects(&[neg, &neg_bad_arg, &neg_bad_head], "TypeTheory");
}

#[test]
/// ExC.2: coend introduction with term argument must use `coend`, not its eliminator.
fn exc_2_introduction_for_coends_with_term_contract() {
    check_accepts(
        r#"
module Paper.ExC_2 where
postulate
  C : Cat
  Delta : Cat
  Q : (x : C) -> (d : Delta) -> Prop
ex_c_2_intro (q : (d : Delta) -> (x : C) -> Q x d) : (d : Delta) -> coend (x : C). Q x d =
  \d. coend (\x. q d x)
"#,
    );
    let neg = r#"
module Paper.ExC_2.Negative where
postulate
  C : Cat
  Delta : Cat
  Q : (x : C) -> (d : Delta) -> Prop
ex_c_2_intro (q : (d : Delta) -> (x : C) -> Q x d) : (d : Delta) -> coend (x : C). Q x d =
  \d. coend^-1 (\x. q d x)
"#;
    let neg_bad_quantifier = neg.replacen("coend^-1 (\\x. q d x)", "coend (\\d. q d d)", 1);
    let neg_bad_body = neg.replacen("coend^-1 (\\x. q d x)", "(\\x. q d x)", 1);
    check_rejects(&[neg, &neg_bad_quantifier, &neg_bad_body], "TypeTheory");
}

#[test]
/// ExC.3: coend introduction with diagonal/dinatural variable must keep `Q z z` indexing.
fn exc_3_introduction_for_coends_with_dinatural_variable_contract() {
    check_accepts(
        r#"
module Paper.ExC_3 where
postulate
  C : Cat
  Q : (x : C) -> (y : C) -> Prop
ex_c_3_intro (q : (x : C) -> Q x x) : coend (z : C). Q z z =
  coend q
"#,
    );
    let neg = r#"
module Paper.ExC_3.Negative where
postulate
  C : Cat
  Q : (x : C) -> (y : C) -> Prop
ex_c_3_intro (q : (x : C) -> Q x x) : coend (z : C). Q z z =
  coend^-1 q
"#;
    let neg_bad_diagonal = neg.replacen("coend^-1 q", "coend (\\z. q)", 1);
    let neg_bad_result = neg.replacen("coend^-1 q", "q", 1);
    check_rejects(&[neg, &neg_bad_diagonal, &neg_bad_result], "TypeTheory");
}

#[test]
/// ExD.1: pointwise left-Kan coend packs hom and payload in the stated component order.
fn exd_1_pointwise_formula_for_left_kan_contract() {
    check_accepts(
        r#"
module Paper.ExD_1 where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  P : (x : C) -> Prop
  h : (x : C) -> (y : D) -> F x ->[D] y
  p : (x : C) -> P x
exd_1_pointwise_formula_for_left_kan (y : D) : coend (x : C). (F x ->[D] y) * P x =
  coend (\x. (h x y, p x))
"#,
    );
    let neg = r#"
module Paper.ExD_1.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  P : (x : C) -> Prop
  h : (x : C) -> (y : D) -> F x ->[D] y
  p : (x : C) -> P x
exd_1_pointwise_formula_for_left_kan (y : D) : coend (x : C). (F x ->[D] y) * P x =
  coend (\x. (p x, h x y))
"#;
    let neg_bad_pair = neg.replacen("(p x, h x y)", "(h x y, h x y)", 1);
    let neg_bad_head = neg.replacen("coend (\\x. (p x, h x y))", "\\x. (p x, h x y)", 1);
    check_rejects(&[neg, &neg_bad_pair, &neg_bad_head], "TypeTheory");
}

#[test]
/// ExD.2: right lifts in profunctors are expressed with `end`, not `coend`.
fn exd_2_right_lifts_in_profunctors_contract() {
    check_accepts(
        r#"
module Paper.ExD_2 where
postulate
  A : Cat
  C : Cat
  D : Cat
  P : (x : C) -> (y : A) -> Prop
  Phi : (x : C) -> (z : D) -> Prop
  g : (x : C) -> (y : A) -> (z : D) -> (P x y -> Phi x z)
exd_2_right_lifts_in_profunctors (y : A) (z : D) : end (x : C). P x y -> Phi x z =
  end (\x. g x y z)
"#,
    );
    let neg = r#"
module Paper.ExD_2.Negative where
postulate
  A : Cat
  C : Cat
  D : Cat
  P : (x : C) -> (y : A) -> Prop
  Phi : (x : C) -> (z : D) -> Prop
  g : (x : C) -> (y : A) -> (z : D) -> (P x y -> Phi x z)
exd_2_right_lifts_in_profunctors (y : A) (z : D) : end (x : C). P x y -> Phi x z =
  coend (\x. g x y z)
"#;
    let neg_bad_family = neg.replacen("coend (\\x. g x y z)", "end (\\x. g y x z)", 1);
    let neg_bad_head = neg.replacen("coend (\\x. g x y z)", "g", 1);
    check_rejects(&[neg, &neg_bad_family, &neg_bad_head], "TypeTheory");
}

#[test]
/// ExD.3: profunctor composition associativity depends on correct nesting/order of inner and outer coends.
fn exd_3_associativity_of_profunctor_composition_contract() {
    check_accepts(
        r#"
module Paper.ExD_3 where
postulate
  B : Cat
  C : Cat
  D : Cat
  P : (b : B) -> Prop
  Q : (b : B) -> (c : C) -> Prop
  R : (c : C) -> (d : D) -> Prop
  p : (b : B) -> P b
  q : (b : B) -> (c : C) -> Q b c
  r : (c : C) -> (d : D) -> R c d
exd_3_associativity_of_profunctor_composition (d : D) : coend (c : C). ((coend (b : B). (P b * Q b c)) * R c d) =
  coend (\c. (coend (\b. (p b, q b c)), r c d))
"#,
    );
    let neg = r#"
module Paper.ExD_3.Negative where
postulate
  B : Cat
  C : Cat
  D : Cat
  P : (b : B) -> Prop
  Q : (b : B) -> (c : C) -> Prop
  R : (c : C) -> (d : D) -> Prop
  p : (b : B) -> P b
  q : (b : B) -> (c : C) -> Q b c
  r : (c : C) -> (d : D) -> R c d
exd_3_associativity_of_profunctor_composition (d : D) : coend (c : C). ((coend (b : B). (P b * Q b c)) * R c d) =
  coend (\c. (r c d, coend (\b. (p b, q b c))))
"#;
    let neg_bad_inner = neg.replacen("(p b, q b c)", "(q b c, p b)", 1);
    let neg_bad_head = neg.replacen(
        "coend (\\c. (r c d, coend (\\b. (p b, q b c))))",
        "coend^-1 (coend (\\c. (r c d, coend (\\b. (p b, q b c)))))",
        1,
    );
    check_rejects(&[neg, &neg_bad_inner, &neg_bad_head], "TypeTheory");
}
