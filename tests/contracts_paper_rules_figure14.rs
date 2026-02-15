mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;

rule_contract!(
    // Figure 14 `CovTop`: covariance into `Top` should remain trivial and not reintroduce directed dependence.
    figure14_cov_top_rule_contract,
    positive: r#"
module Rules.Figure14.CovTop.Positive where
postulate
  C : Cat
P (x : C) : Prop =
  Top
probe (x : C) (u : P x) : P x =
  u
"#,
    negatives: [
        r#"
module Rules.Figure14.CovTop.Negative where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : D) -> (x ->[D] y)
probe (x : C) : P x =
  \y. refl y
"#,
        r#"
module Rules.Figure14.CovTop.Negative.BadResult where
postulate
  C : Cat
P (x : C) : Prop =
  Top
probe (x : C) : P x =
  refl x
"#,
        r#"
module Rules.Figure14.CovTop.Negative.BadCategory where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : C) -> (y ->[D] y)
probe (x : C) : P x =
  \y. \u. u
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 14 `CovProd`: product covariance requires each component to preserve directed polarity.
    figure14_cov_prod_rule_contract,
    positive: r#"
module Rules.Figure14.CovProd.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
probe (x : C) : P x * Q x =
  ((\y. \u. u), refl x)
"#,
    negatives: [
        r#"
module Rules.Figure14.CovProd.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
probe (x : C) : P x * Q x =
  ((\y. \u. u), (\y. \u. u))
"#,
        r#"
module Rules.Figure14.CovProd.Negative.BadSecondComponent where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
probe (x : C) : P x * Q x =
  ((\y. \u. u), (\y. \u. u))
"#,
        r#"
module Rules.Figure14.CovProd.Negative.SwappedProduct where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
probe (x : C) : Q x * P x =
  ((\y. \u. u), refl x)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 14 `CovExp`: exponential covariance must keep premise `y → F x` oriented toward `F x`.
    figure14_cov_exp_rule_contract,
    positive: r#"
module Rules.Figure14.CovExp.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe (x : C) : (y : D) -> ((y ->[D] F x) -> P x) =
  \y. \u. refl x
"#,
    negatives: [
        r#"
module Rules.Figure14.CovExp.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe (x : C) : (y : D) -> ((F x ->[D] y) -> P x) =
  \y. \u. refl x
"#,
        r#"
module Rules.Figure14.CovExp.Negative.BadWitness where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe (x : C) : (y : D) -> ((y ->[D] F x) -> P x) =
  \y. \u. u
"#,
        r#"
module Rules.Figure14.CovExp.Negative.BadBinderCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe (x : C) : (y : C) -> ((y ->[D] F x) -> P x) =
  \y. \u. refl x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 14 `CovHom`: codomain hom shape must stay exactly `y -> F x`.
    figure14_cov_hom_rule_contract,
    positive: r#"
module Rules.Figure14.CovHom.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) (y : D) (u : y ->[D] F x) : y ->[D] F x =
  u
"#,
    negatives: [
        r#"
module Rules.Figure14.CovHom.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) (y : D) (u : y ->[D] F x) : F x ->[D] y =
  u
"#,
        r#"
module Rules.Figure14.CovHom.Negative.BadWitness where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) (y : D) (u : y ->[D] F x) : y ->[D] F x =
  refl x
"#,
        r#"
module Rules.Figure14.CovHom.Negative.BadDomainCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) (y : C) (u : y ->[D] F x) : y ->[D] F x =
  u
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 14 `CovQuant`: quantifier elimination for ends must pass through `end^-1` at the index.
    figure14_cov_quantifier_rule_contract,
    positive: r#"
module Rules.Figure14.CovQuant.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe : (x : C) -> P x =
  \x. (end^-1 h) x
"#,
    negatives: [
        r#"
module Rules.Figure14.CovQuant.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe : (x : C) -> P x =
  \x. end^-1 (h x)
"#,
        r#"
module Rules.Figure14.CovQuant.Negative.TreatEndAsFunction where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe : (x : C) -> P x =
  \x. h x
"#,
        r#"
module Rules.Figure14.CovQuant.Negative.BadElimArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe : (x : C) -> P x =
  \x. (end^-1 h) h
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 14 `Contra`: contravariant premise must point from `y` to `F x`, not vice versa.
    figure14_contra_rule_contract,
    positive: r#"
module Rules.Figure14.Contra.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> ((y ->[D] F x) -> (x ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \u. refl x
"#,
    negatives: [
        r#"
module Rules.Figure14.Contra.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> ((F x ->[D] y) -> (x ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \u. refl x
"#,
        r#"
module Rules.Figure14.Contra.Negative.BadBody where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> ((y ->[D] F x) -> (x ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure14.Contra.Negative.BadBinderCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : C) -> ((y ->[D] F x) -> (x ->[C] x))
probe : (x : C) -> P x =
  \x. \y. \u. refl x
"#,
    ],
    category: "TypeTheory"
);

#[test]
fn figure14_end_contravariant_rule_contract() {
    let source = r#"
module Rules.EndContravariant where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop

end_contra : Prop = end (x : C). P x x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    // end introduces a contravariant quantifier: the bound variable must appear contravariantly
    let analysis = semantics.all_variances(&typed, "P").unwrap();
    let x_var = analysis
        .iter()
        .find(|a| a.variable == "x")
        .expect("x must have variance");
    assert_eq!(
        x_var.variance,
        Variance::Contravariant,
        "variable under end must be exactly contravariant"
    );
}

#[test]
fn figure14_coend_covariant_rule_contract() {
    let source = r#"
module Rules.CoendCovariant where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop

coend_cov : Prop = coend (x : C). P x x
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let analysis = semantics.all_variances(&typed, "P").unwrap();
    let x_var = analysis
        .iter()
        .find(|a| a.variable == "x")
        .expect("x must have variance");
    assert_eq!(
        x_var.variance,
        Variance::Covariant,
        "variable under coend must be exactly covariant"
    );
}
