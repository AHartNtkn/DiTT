mod common;

use common::engines::compile_with_engines;
use ditt_lang::api::*;

rule_contract!(
    // Figure 13 `UnusedVar≠`: result should be indexed only by `y : D`, never by unused `x : C`.
    figure13_unused_var_neq_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedVarNeq.Positive where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D] y =
  refl y
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedVarNeq.Negative where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D] y =
  refl x
"#,
        r#"
module Rules.Figure13.UnusedVarNeq.Negative.WrongCodomain where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : x ->[D] x =
  refl y
"#,
        r#"
module Rules.Figure13.UnusedVarNeq.Negative.ReturnObject where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D] y =
  y
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedTop`: `Top` witness cannot be replaced by unrelated object terms.
    figure13_unused_top_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedTop.Positive where
postulate
  C : Cat
probe (x : C) (u : Top) : Top =
  u
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedTop.Negative where
postulate
  C : Cat
probe (x : C) (u : Top) : Top =
  x
"#,
        r#"
module Rules.Figure13.UnusedTop.Negative.ReflOnTop where
postulate
  C : Cat
probe (x : C) (u : Top) : Top =
  refl u
"#,
        r#"
module Rules.Figure13.UnusedTop.Negative.UnboundTop where
postulate
  C : Cat
probe (x : C) (u : Top) : Top =
  v
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedApp`: application argument must stay in the `D` index expected by `f`.
    figure13_unused_app_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedApp.Positive where
postulate
  C : Cat
  D : Cat
probe (x : C) (f : (z : D) -> z ->[D] z) (z : D) : z ->[D] z =
  f z
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedApp.Negative where
postulate
  C : Cat
  D : Cat
probe (x : C) (f : (z : D) -> z ->[D] z) (z : D) : z ->[D] z =
  f x
"#,
        r#"
module Rules.Figure13.UnusedApp.Negative.BadResultType where
postulate
  C : Cat
  D : Cat
probe (x : C) (f : (z : D) -> z ->[D] z) (z : D) : z ->[D] z =
  f z z
"#,
        r#"
module Rules.Figure13.UnusedApp.Negative.BadLambdaDomain where
postulate
  C : Cat
  D : Cat
probe (x : C) (f : (z : D) -> z ->[D] z) (z : D) : z ->[D] z =
  (\w : C. f z) x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedPair`: each pair component must match the same `y`-indexed hom family.
    figure13_unused_pair_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedPair.Positive where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  (refl y, refl y)
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedPair.Negative where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  (refl y, refl x)
"#,
        r#"
module Rules.Figure13.UnusedPair.Negative.SwappedCategory where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  (refl x, refl y)
"#,
        r#"
module Rules.Figure13.UnusedPair.Negative.NotAPair where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  refl y
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedProj`: projections are limited to `.1/.2` and must preserve `y`-indexed type.
    figure13_unused_proj_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedProj.Positive where
postulate
  C : Cat
  D : Cat
pair (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  (refl y, refl y)
probe (x : C) (y : D) : y ->[D] y =
  (pair x y).1
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedProj.Negative where
postulate
  C : Cat
  D : Cat
pair (x : C) (y : D) : (y ->[D] y) * (y ->[D] y) =
  (refl y, refl y)
probe (x : C) (y : D) : y ->[D] y =
  (pair x y).3
"#,
        r#"
module Rules.Figure13.UnusedProj.Negative.WrongProjection where
postulate
  C : Cat
  D : Cat
pair (x : C) (y : D) : (y ->[D] y) * (x ->[C] x) =
  (refl y, refl x)
probe (x : C) (y : D) : y ->[D] y =
  (pair x y).2
"#,
        r#"
module Rules.Figure13.UnusedProj.Negative.ProjectFromNonPair where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D] y =
  (refl y).1
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedLambda`: lambda body must stay indexed by bound `z : D`, not unused `x`.
    figure13_unused_lambda_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedLambda.Positive where
postulate
  C : Cat
  D : Cat
probe (x : C) : (z : D) -> z ->[D] z =
  \z. refl z
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedLambda.Negative where
postulate
  C : Cat
  D : Cat
probe (x : C) : (z : D) -> z ->[D] z =
  \z. refl x
"#,
        r#"
module Rules.Figure13.UnusedLambda.Negative.BadBinderUse where
postulate
  C : Cat
  D : Cat
probe (x : C) : (z : D) -> z ->[D] z =
  \z. z
"#,
        r#"
module Rules.Figure13.UnusedLambda.Negative.BadCodomain where
postulate
  C : Cat
  D : Cat
probe (x : C) : (z : D) -> z ->[D] z =
  \z. refl (refl z)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 13 `UnusedOp`: opposite-hom witness still requires endpoints from `D`, not unused `x`.
    figure13_unused_op_rule_contract,
    positive: r#"
module Rules.Figure13.UnusedOp.Positive where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D^] y =
  refl y
"#,
    negatives: [
        r#"
module Rules.Figure13.UnusedOp.Negative where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D^] y =
  refl x
"#,
        r#"
module Rules.Figure13.UnusedOp.Negative.WrongCategory where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[C^] y =
  refl y
"#,
        r#"
module Rules.Figure13.UnusedOp.Negative.ReturnObject where
postulate
  C : Cat
  D : Cat
probe (x : C) (y : D) : y ->[D^] y =
  y
"#,
    ],
    category: "TypeTheory"
);

#[test]
/// Figure 13 rules are all `Unused` variants: each family-level index variable `x`
/// must be reported as `unused` by variance analysis.
fn figure13_rules_mark_unused_flag_for_each_unused_variant() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.Figure13.UnusedFlagAnalysis where
postulate
  C : Cat
  D : Cat

unused_var_neq (x : C) : Prop =
  (y : D) -> (y ->[D] y)

unused_top (x : C) : Prop =
  Top

unused_app (x : C) : Prop =
  (f : (z : D) -> z ->[D] z) -> (z : D) -> z ->[D] z

unused_pair (x : C) : Prop =
  (y : D) -> ((y ->[D] y) * (y ->[D] y))

unused_proj (x : C) : Prop =
  (y : D) -> y ->[D] y

unused_lambda (x : C) : Prop =
  (z : D) -> z ->[D] z

unused_op (x : C) : Prop =
  (y : D) -> y ->[D^] y
"#,
    );

    for predicate in [
        "unused_var_neq",
        "unused_top",
        "unused_app",
        "unused_pair",
        "unused_proj",
        "unused_lambda",
        "unused_op",
    ] {
        let analyses = semantics.all_variances(&typed, predicate).unwrap();
        let x_analysis = analyses
            .iter()
            .find(|analysis| analysis.variable == "x")
            .unwrap_or_else(|| panic!("missing analysis row for x in predicate '{predicate}'"));
        assert!(
            x_analysis.is_unused(),
            "Figure 13 rule '{predicate}' must mark the index variable as unused"
        );
    }
}

#[test]
fn figure13_variable_that_appears_in_body_is_not_marked_unused() {
    let (_syntax, semantics, typed) = compile_with_engines(
        r#"
module Rules.Figure13.UnusedSoundness where
postulate
  C : Cat

appears (x : C) : Prop =
  x ->[C] x
"#,
    );

    let analyses = semantics.all_variances(&typed, "appears").unwrap();
    let x_row = analyses
        .iter()
        .find(|analysis| analysis.variable == "x")
        .unwrap_or_else(|| panic!("missing variance analysis row for variable x"));
    assert!(
        !x_row.is_unused(),
        "variables that appear in a predicate body must not be classified as unused"
    );
}
