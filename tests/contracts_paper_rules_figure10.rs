mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;

fn compute_rule_variance(source: &str, predicate: &str, variable: &str) -> Variance {
    let (_syntax, semantics, typed) = compile_with_engines(source);
    semantics
        .compute_variance_at_position(&typed, predicate, &[], variable)
        .unwrap()
}

fn compute_rule_variance_analysis(
    source: &str,
    predicate: &str,
    variable: &str,
) -> VarianceAnalysis {
    let (_syntax, semantics, typed) = compile_with_engines(source);
    let analyses = semantics.all_variances(&typed, predicate).unwrap();
    analyses
        .into_iter()
        .find(|analysis| analysis.variable == variable)
        .unwrap_or_else(|| {
            panic!(
                "missing variance analysis row for variable '{variable}' in predicate '{predicate}'"
            )
        })
}

fn assert_judgment_is_not_derivable(
    source: &str,
    probe_name: &str,
    rule: InferenceRule,
    context: &str,
) {
    let (syntax, semantics, _typed) = compile_with_engines(source);
    let parsed = syntax.parse_module(source).unwrap();
    match semantics.elaborate_module(&parsed) {
        Err(err) => {
            let diagnostics = err.into_diagnostics();
            assert!(
                diagnostics
                    .diagnostics
                    .iter()
                    .any(|d| d.category == "TypeTheory"),
                "{context}: elaboration rejection must produce TypeTheory diagnostics, got: {diagnostics:?}"
            );
        }
        Ok(typed) => {
            let judgment = common::support::entailment(probe_name);
            let diagnostics = semantics
                .derive(&typed, &judgment, rule)
                .unwrap_err()
                .into_diagnostics();
            assert!(
                diagnostics
                    .diagnostics
                    .iter()
                    .any(|d| d.category == "TypeTheory"),
                "{context}: derivation rejection must produce TypeTheory diagnostics, got: {diagnostics:?}"
            );
        }
    }
}

rule_contract!(
    // Figure 10 `CovHom`: covariant use of `x` appears only in codomain position `y → F x`;
    // negatives target polarity reversal, object-category mismatch, and witness/body mismatch.
    figure10_cov_hom_rule_contract,
    positive: r#"
module Rules.Figure10.CovHom.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
    negatives: [
        r#"
module Rules.Figure10.CovHom.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.CovHom.Negative.ObjectCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : C) -> (y ->[D] F x)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.CovHom.Negative.BadWitness where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
probe : (x : C) -> P x =
  \x. \y. \u. refl x
"#,
    ],
    category: "TypeTheory"
);

#[test]
/// Dinatural usage must be rejected when checked against a covariant-only Figure 10 judgment.
fn figure10_dinatural_variable_is_rejected_in_covariant_only_context() {
    assert_judgment_is_not_derivable(
        r#"
module Rules.Figure10.DinaturalRejectedByCovariantJudgment where
postulate
  C : Cat

P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))

probe (x : C) : P x =
  \y. \k. k
"#,
        "probe",
        InferenceRule::Var,
        "dinatural variables must be rejected when the requested judgment requires covariance",
    );
}

#[test]
/// Dinatural usage must be rejected under Figure 10 covariance when mixed variance appears in product components.
fn figure10_dinatural_variable_is_rejected_in_covariant_product_context() {
    assert_judgment_is_not_derivable(
        r#"
module Rules.Figure10.DinaturalRejectedByCovariantProductJudgment where
postulate
  C : Cat

P (x : C) : Prop =
  ((y : C) -> (y ->[C] x)) * ((y : C) -> (x ->[C] y))

probe (x : C) : P x =
  ((\y. \u. u), (\y. \u. u))
"#,
        "probe",
        InferenceRule::Var,
        "dinatural variable in mixed product components must be rejected by covariant product judgment",
    );
}

#[test]
/// Dinatural usage must be rejected under Figure 10 covariance when exponential domains contain mixed variance.
fn figure10_dinatural_variable_is_rejected_in_covariant_exponential_domain() {
    assert_judgment_is_not_derivable(
        r#"
module Rules.Figure10.DinaturalRejectedByCovariantExponentialDomain where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  P : (x : C) -> Prop
  witness : (x : C) -> P x

probe (x : C) : (y : D) -> (((y ->[D] F x) * (F x ->[D] y)) -> P x) =
  \x. \y. \pair. witness x
"#,
        "probe",
        InferenceRule::Var,
        "dinatural variable in mixed exponential domain must be rejected by covariant exponential judgment",
    );
}

#[test]
/// Dinatural usage must be rejected under Figure 10 covariance when mixed variance is nested across compositions.
fn figure10_dinatural_variable_is_rejected_in_nested_mixed_variance_context() {
    assert_judgment_is_not_derivable(
        r#"
module Rules.Figure10.DinaturalRejectedByNestedComposition where
postulate
  C : Cat

P (x : C) : Prop =
  (y : C) -> ((y ->[C] x) -> ((x ->[C] y) -> (y ->[C] x)))

probe (x : C) : P x =
  \y. \left. \right. left
"#,
        "probe",
        InferenceRule::Var,
        "nested mixed-variance composition must be rejected by covariant-only judgment",
    );
}

rule_contract!(
    // Covariant polarity enforcement: a variable declared in positive/covariant position must be rejected when moved into contravariant source position.
    figure10_covariant_variable_used_contravariantly_is_rejected,
    positive: r#"
module Rules.Figure10.PolarityEnforcement.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
    negatives: [
        r#"
module Rules.Figure10.PolarityEnforcement.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.PolarityEnforcement.Negative.BothSides where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  left : (x : C) -> (y : D) -> (F x ->[D] y)
  right : (x : C) -> (y : D) -> (y ->[D] F x)
P (x : C) : Prop =
  (y : D) -> ((F x ->[D] y) * (y ->[D] F x))
probe : (x : C) -> P x =
  \x. \y. (left x y, right x y)
"#,
        r#"
module Rules.Figure10.PolarityEnforcement.Negative.OppositeContravariant where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (x ->[C^] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Polarity enforcement for opposite-category binders: a variable bound negatively (`x : C^`)
    // must be rejected when used in covariant target position.
    figure10_negative_polarity_variable_used_covariantly_is_rejected,
    positive: r#"
module Rules.Figure10.PolarityEnforcement.NegativeBinder.Positive where
postulate
  C : Cat
P (x : C^) : Prop =
  (y : C) -> (x ->[C] y)
probe : (x : C^) -> P x =
  \x. \y. \u. u
"#,
    negatives: [
        r#"
module Rules.Figure10.PolarityEnforcement.NegativeBinder.Negative where
postulate
  C : Cat
P (x : C^) : Prop =
  (y : C) -> (y ->[C] x)
probe : (x : C^) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.PolarityEnforcement.NegativeBinder.Negative.BothSides where
postulate
  C : Cat
  left : (x : C^) -> (y : C) -> (y ->[C] x)
  right : (x : C^) -> (y : C) -> (x ->[C] y)
P (x : C^) : Prop =
  (y : C) -> ((y ->[C] x) * (x ->[C] y))
probe : (x : C^) -> P x =
  \x. \y. (left x y, right x y)
"#,
        r#"
module Rules.Figure10.PolarityEnforcement.NegativeBinder.Negative.OppositeCovariant where
postulate
  C : Cat
P (x : C^) : Prop =
  (y : C) -> (x ->[C^] y)
probe : (x : C^) -> P x =
  \x. \y. \u. u
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 10 `CovProd`: covariance must be preserved componentwise through products;
    // negatives target contravariant contamination, bad second component witness, and swapped product order.
    figure10_cov_prod_rule_contract,
    positive: r#"
module Rules.Figure10.CovProd.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
R (x : C) : Prop =
  P x * Q x
probe : (x : C) -> R x =
  \x. ((\y. \u. u), refl x)
"#,
    negatives: [
        r#"
module Rules.Figure10.CovProd.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
R (x : C) : Prop =
  P x * Q x
probe : (x : C) -> R x =
  \x. ((\y. \u. u), (\y. \u. u))
"#,
        r#"
module Rules.Figure10.CovProd.Negative.BadSecondComponent where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
R (x : C) : Prop =
  P x * Q x
probe : (x : C) -> R x =
  \x. ((\y. \u. u), (\y. \u. u))
"#,
        r#"
module Rules.Figure10.CovProd.Negative.SwappedProduct where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
R (x : C) : Prop =
  Q x * P x
probe : (x : C) -> R x =
  \x. ((\y. \u. u), refl x)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 10 `CovExp`: covariance through exponentials uses `(y → F x) -> P x`;
    // negatives target reversed arrow, invalid witness extraction, and domain/category mismatch.
    figure10_cov_exp_rule_contract,
    positive: r#"
module Rules.Figure10.CovExp.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe : (x : C) -> (y : D) -> ((y ->[D] F x) -> P x) =
  \x. \y. \u. refl x
"#,
    negatives: [
        r#"
module Rules.Figure10.CovExp.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe : (x : C) -> (y : D) -> ((F x ->[D] y) -> P x) =
  \x. \y. \u. refl x
"#,
        r#"
module Rules.Figure10.CovExp.Negative.BadBody where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe : (x : C) -> (y : D) -> ((y ->[D] F x) -> P x) =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.CovExp.Negative.BadBinderCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
probe : (x : C) -> (y : C) -> ((y ->[D] F x) -> P x) =
  \x. \y. \u. refl x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 10 `Contra`: contravariant rule keeps `x` in source position through a function space;
    // negatives target polarity inversion, invalid body witness, and binder-category mismatch.
    figure10_contra_rule_contract,
    positive: r#"
module Rules.Figure10.Contra.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
contra_shape : Prop =
  (x : C) -> (y : D) -> ((y ->[D] F x) -> Top)
probe : contra_shape =
  \x. \y. \u. !
"#,
    negatives: [
        r#"
module Rules.Figure10.Contra.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
contra_shape : Prop =
  (x : C) -> (y : D) -> ((F x ->[D] y) -> P x)
probe : contra_shape =
  \x. \y. \u. refl x
"#,
        r#"
module Rules.Figure10.Contra.Negative.BadBody where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
contra_shape : Prop =
  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)
probe : contra_shape =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.Contra.Negative.BadBinderCategory where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
contra_shape : Prop =
  (x : C) -> (y : C) -> ((y ->[D] F x) -> P x)
probe : contra_shape =
  \x. \y. \u. refl x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 10 `Unused`: the rule exercises irrelevance of an unused variable in the family;
    // negatives force illegal dependence on `x`, wrong witness shape, or wrong quantified category.
    figure10_unused_rule_contract,
    positive: r#"
module Rules.Figure10.Unused.Positive where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : D) -> (y ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
    negatives: [
        r#"
module Rules.Figure10.Unused.Negative where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : D) -> (x ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
        r#"
module Rules.Figure10.Unused.Negative.BadBody where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : D) -> (y ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. refl x
"#,
        r#"
module Rules.Figure10.Unused.Negative.BadBinderCategory where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : C) -> (y ->[D] y)
probe : (x : C) -> P x =
  \x. \y. \u. u
"#,
    ],
    category: "TypeTheory"
);

#[test]
/// Figure 10 rule probes must expose their intended variance polarity through the variance API.
fn figure10_rules_compute_expected_variance() {
    let cov_hom = compute_rule_variance(
        r#"
module Rules.Figure10.CovHom.Variance where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
"#,
        "P",
        "x",
    );
    assert_eq!(cov_hom, Variance::Covariant);

    let cov_prod = compute_rule_variance(
        r#"
module Rules.Figure10.CovProd.Variance where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
Q (x : C) : Prop =
  x ->[C] x
R (x : C) : Prop =
  P x * Q x
"#,
        "R",
        "x",
    );
    assert_eq!(cov_prod, Variance::Covariant);

    let cov_exp = compute_rule_variance(
        r#"
module Rules.Figure10.CovExp.Variance where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
Probe (x : C) : Prop =
  (y : D) -> ((y ->[D] F x) -> P x)
"#,
        "Probe",
        "x",
    );
    assert_eq!(cov_exp, Variance::Covariant);

    let contra = compute_rule_variance(
        r#"
module Rules.Figure10.Contra.Variance where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  x ->[C] x
contra_shape : Prop =
  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)
"#,
        "contra_shape",
        "x",
    );
    assert_eq!(contra, Variance::Contravariant);

    let dinatural = compute_rule_variance(
        r#"
module Rules.Figure10.Dinatural.Variance where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> ((x ->[C] y) -> (y ->[C] x))
"#,
        "P",
        "x",
    );
    assert_eq!(dinatural, Variance::Dinatural);

    let unused = compute_rule_variance_analysis(
        r#"
module Rules.Figure10.Unused.Variance where
postulate
  C : Cat
  D : Cat
P (x : C) : Prop =
  (y : D) -> (y ->[D] y)
"#,
        "P",
        "x",
    );
    assert!(
        unused.is_unused(),
        "unused variable classification must be exposed outside of the Variance enum"
    );
}

#[test]
/// CovProd with mixed variance: one component covariant, the other contravariant, yields Mixed.
fn figure10_cov_prod_mixed_variance_yields_mixed() {
    let mixed_prod = compute_rule_variance(
        r#"
module Rules.Figure10.CovProd.MixedVariance where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
CovComponent (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
ContraComponent (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
R (x : C) : Prop =
  CovComponent x * ContraComponent x
"#,
        "R",
        "x",
    );
    assert_eq!(
        mixed_prod,
        Variance::Dinatural,
        "product with one covariant and one contravariant component must be Dinatural"
    );
}

#[test]
/// Variance classification must cover binder, product, and opposite-category hom contexts.
fn figure10_variance_covers_binder_product_and_opposite_contexts() {
    let binder_positive = compute_rule_variance(
        r#"
module Rules.Figure10.Polarity.BinderPositive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (y ->[D] F x)
"#,
        "P",
        "x",
    );
    assert_eq!(binder_positive, Variance::Covariant);

    let binder_negative = compute_rule_variance(
        r#"
module Rules.Figure10.Polarity.BinderNegative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
P (x : C) : Prop =
  (y : D) -> (F x ->[D] y)
"#,
        "P",
        "x",
    );
    assert_eq!(binder_negative, Variance::Contravariant);

    let product_both = compute_rule_variance(
        r#"
module Rules.Figure10.Polarity.ProductBoth where
postulate
  C : Cat
P (x : C) : Prop =
  ((y : C) -> (x ->[C] y)) * ((y : C) -> (y ->[C] x))
"#,
        "P",
        "x",
    );
    assert_eq!(product_both, Variance::Dinatural);

    let opposite_negative = compute_rule_variance(
        r#"
module Rules.Figure10.Polarity.OppositeNegative where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (y ->[C^] x)
"#,
        "P",
        "x",
    );
    assert_eq!(opposite_negative, Variance::Contravariant);

    let opposite_positive = compute_rule_variance(
        r#"
module Rules.Figure10.Polarity.OppositePositive where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (x ->[C^] y)
"#,
        "P",
        "x",
    );
    assert_eq!(opposite_positive, Variance::Covariant);
}

#[test]
fn variance_flips_through_opposite_category() {
    let variance = compute_rule_variance(
        r#"
module Rules.Figure10.OppositeFlip where
postulate
  C : Cat
P (x : C) : Prop =
  (y : C) -> (y ->[C^] x)
"#,
        "P",
        "x",
    );
    // x appears in the target position of a hom in C^op,
    // which flips from covariant to contravariant.
    assert_eq!(
        variance,
        Variance::Contravariant,
        "Variable in target position of opposite hom must be contravariant"
    );
}
