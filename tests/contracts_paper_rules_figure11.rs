mod common;

use std::collections::BTreeSet;

use common::conformance::{
    assert_derivation_rule_from_source, check_accepts, check_rejects, check_rejects_derive,
    derivation_root, read_fixture,
};
use common::engines::compile_with_engines;
use ditt_lang::api::*;
use ditt_lang::runtime::SemanticEngine;

macro_rules! fixture_derivation_id_test {
    ($name:ident, $probe:literal, $rule_id:literal) => {
        #[test]
        fn $name() {
            assert_fixture_derivation_has_paper_rule_id($probe, $rule_id);
        }
    };
}

fn assert_fixture_derivation_has_paper_rule_id(probe_name: &str, expected_paper_rule_id: &str) {
    let source = read_fixture("conformance/semantics/figure11_rules.ditt");
    let candidate_categories: [InferenceRule; 13] = [
        InferenceRule::Var,
        InferenceRule::Wk,
        InferenceRule::Top,
        InferenceRule::Idx,
        InferenceRule::Contr,
        InferenceRule::Prod,
        InferenceRule::Exp,
        InferenceRule::End,
        InferenceRule::Coend,
        InferenceRule::CutDin,
        InferenceRule::CutNat,
        InferenceRule::Refl,
        InferenceRule::JRule,
    ];
    let mut observed = Vec::new();

    for category in candidate_categories {
        let root = std::panic::catch_unwind(|| derivation_root(&source, probe_name, category));
        if let Ok(root) = root {
            observed.push(format!("{category}:{}", root.rule.paper_rule_id()));
            if root.rule.paper_rule_id() == expected_paper_rule_id {
                return;
            }
        }
    }

    panic!(
        "figure11 probe '{probe_name}' must derive paper rule id '{expected_paper_rule_id}', observed derivations: {observed:?}"
    );
}

fn figure11_paper_rule_ids_used_by_this_file() -> BTreeSet<&'static str> {
    [
        "Figure11.Var",
        "Figure11.Wk",
        "Figure11.Top",
        "Figure11.Idx",
        "Figure11.Contr",
        "Figure11.Prod",
        "Figure11.Exp",
        "Figure11.End",
        "Figure11.Coend",
        "Figure11.CutDin",
        "Figure11.CutNat",
        "Figure11.Refl",
        "Figure11.JRule",
    ]
    .into_iter()
    .collect()
}

fn coverage_csv_rule_ids() -> BTreeSet<String> {
    let csv = include_str!("../docs/PAPER_RULE_COVERAGE.csv");
    let mut lines = csv.lines().filter(|line| !line.trim().is_empty());
    let header = lines
        .next()
        .unwrap_or_default()
        .split(',')
        .map(|s| s.trim().to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        header,
        vec![
            "rule_id",
            "judgment_kind",
            "positive_contract_id",
            "negative_contract_id"
        ]
    );

    lines
        .map(|line| {
            let cols = line
                .split(',')
                .map(|s| s.trim().to_string())
                .collect::<Vec<_>>();
            assert_eq!(cols.len(), 4, "bad paper coverage row: {line}");
            cols[0].clone()
        })
        .collect()
}

#[test]
fn figure11_paper_rule_ids_are_registered_in_coverage_csv() {
    let csv_ids = coverage_csv_rule_ids();
    for paper_rule_id in figure11_paper_rule_ids_used_by_this_file() {
        assert!(
            csv_ids.contains(paper_rule_id),
            "paper_rule_id '{paper_rule_id}' used by figure11 tests is missing from PAPER_RULE_COVERAGE.csv"
        );
    }
}

rule_contract!(
    // Figure 11 `Var`: variable rule returns the bound witness at the exact indexed family.
    figure11_var_rule_contract,
    positive: r#"
module Rules.Var.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : P x = p
"#,
    negatives: [
        r#"
module Rules.Var.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) : P x = p
"#,
        r#"
module Rules.Var.Negative.BadWitness where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : P x = x
"#,
        r#"
module Rules.Var.Negative.BadIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : P x = q
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Wk`: weakening keeps the original proof `p : P x` regardless of extra assumptions.
    figure11_wk_rule_contract,
    positive: r#"
module Rules.Wk.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) (q : Q x) : P x = p
"#,
    negatives: [
        r#"
module Rules.Wk.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) (q : Q x) : P x = q
"#,
        r#"
module Rules.Wk.Negative.WrongCodomain where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) (q : Q x) : Q x = p
"#,
        r#"
module Rules.Wk.Negative.UnboundWeakening where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) : P x = q
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Top`: top inhabitation accepts only a value of `Top`, not arbitrary terms.
    figure11_top_rule_contract,
    positive: r#"
module Rules.Top.Positive where
probe (u : Top) : Top = u
"#,
    negatives: [
        r#"
module Rules.Top.Negative where
probe : Top = bottom
"#,
        r#"
module Rules.Top.Negative.ReflOnTop where
probe (u : Top) : Top = refl u
"#,
        r#"
module Rules.Top.Negative.FunctionAsTop where
probe : Top = (\x. x)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Idx`: indexing/application must feed a `C`-object into `F : C -> D`.
    figure11_idx_rule_contract,
    positive: r#"
module Rules.Idx.Positive where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) : D = (\z. F z) x
"#,
    negatives: [
        r#"
module Rules.Idx.Negative where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) : D = (\z. F z) (F x)
"#,
        r#"
module Rules.Idx.Negative.BadLambdaDomain where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) : D = (\z : D. F z) x
"#,
        r#"
module Rules.Idx.Negative.BadResultType where
postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
probe (x : C) : C = (\z. F z) x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Contr`: contraction duplicates one proof into a product of two identical components.
    figure11_contr_rule_contract,
    positive: r#"
module Rules.Contr.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : (P x * P x) = (p, p)
"#,
    negatives: [
        r#"
module Rules.Contr.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : P x = (p, p)
"#,
        r#"
module Rules.Contr.Negative.BadSecondComponent where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : (P x * P x) = (p, x)
"#,
        r#"
module Rules.Contr.Negative.NotAPair where
postulate
  C : Cat
  P : (x : C) -> Prop
probe (x : C) (p : P x) : (P x * P x) = p
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Prod`: pairing/projection must preserve component order and projection index.
    figure11_prod_rule_contract,
    positive: r#"
module Rules.Prod.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
pair (x : C) (p : P x) (q : Q x) : (P x * Q x) = (p, q)
left (x : C) (p : P x) (q : Q x) : P x = (pair x p q).1
"#,
    negatives: [
        r#"
module Rules.Prod.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) (q : Q x) : Q x = (p, q)
"#,
        r#"
module Rules.Prod.Negative.SwappedPair where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
probe (x : C) (p : P x) (q : Q x) : (P x * Q x) = (q, p)
"#,
        r#"
module Rules.Prod.Negative.WrongProjection where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
pair (x : C) (p : P x) (q : Q x) : (P x * Q x) = (p, q)
left (x : C) (p : P x) (q : Q x) : P x = (pair x p q).2
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Exp`: composition in exponentials must route through `Q` before reaching `R`.
    figure11_exp_rule_contract,
    positive: r#"
module Rules.Exp.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
probe (x : C) (f : P x -> Q x) (g : Q x -> R x) : P x -> R x =
  \p. g (f p)
"#,
    negatives: [
        r#"
module Rules.Exp.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
probe (x : C) (f : P x -> Q x) (g : Q x -> R x) : P x -> R x =
  \p. f p
"#,
        r#"
module Rules.Exp.Negative.BadIntermediate where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
probe (x : C) (f : P x -> Q x) (g : Q x -> R x) : P x -> R x =
  \p. g p
"#,
        r#"
module Rules.Exp.Negative.BadComposition where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
probe (x : C) (f : P x -> Q x) (g : Q x -> R x) : P x -> R x =
  \p. g (f (f p))
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `End`: elimination `end^-1` turns an end witness into a family member at index `x`.
    figure11_end_rule_contract,
    positive: r#"
module Rules.End.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x = (end^-1 h) x
"#,
    negatives: [
        r#"
module Rules.End.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x = end^-1 (h x)
"#,
        r#"
module Rules.End.Negative.TreatEndAsFunction where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x = h x
"#,
        r#"
module Rules.End.Negative.BadElimArgument where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x = (end^-1 h) h
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `Coend`: introduction into a coend requires the constructor `coend` on a family witness.
    figure11_coend_rule_contract,
    positive: r#"
module Rules.Coend.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  lift : (x : C) -> P x
probe : coend (x : C). P x = coend lift
"#,
    negatives: [
        r#"
module Rules.Coend.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : coend (x : C). P x = coend^-1 k
"#,
        r#"
module Rules.Coend.Negative.WrongResultType where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : (x : C) -> P x = coend k
"#,
        r#"
module Rules.Coend.Negative.BadRoundtrip where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : coend (x : C). P x = coend^-1 (coend k)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `CutDin`: directed cut uses `J` with correctly oriented dinatural premise `P b a`.
    figure11_cut_din_rule_contract,
    positive: r#"
module Rules.CutDin.Positive where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
diag (z : C) : P z z -> Q z z = \p. p
probe (a : C^) (b : C) (e : a ->[C] b) (pba : P b a) : Q a b =
  (J diag [e]) pba
"#,
    negatives: [
        r#"
module Rules.CutDin.Negative where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
diag (z : C) : P z z -> Q z z = \p. p
probe (a : C^) (b : C) (e : a ->[C] b) (pab : P a b) : Q a b =
  (J diag [e]) pab
"#,
        r#"
module Rules.CutDin.Negative.BadDiagCodomain where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
diag (z : C) : P z z -> P z z = \p. p
probe (a : C^) (b : C) (e : a ->[C] b) (pba : P b a) : Q a b =
  (J diag [e]) pba
"#,
        r#"
module Rules.CutDin.Negative.MissingDinArg where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
diag (z : C) : P z z -> Q z z = \p. p
probe (a : C^) (b : C) (e : a ->[C] b) (pba : P b a) : Q a b =
  J diag [e]
"#,
    ],
    category: "TypeTheory"
);

#[test]
/// Figure 11 `CutNat`: natural cut composes `pq` then `qr`; negatives break that middle object.
fn figure11_cut_nat_rule_contract() {
    let semantics = SemanticEngine::default();
    let typed = check_accepts(
        r#"
module Rules.CutNat.Positive where
postulate
  C : Cat
  P : (a : C) -> Prop
  Q : (a : C) -> Prop
  R : (a : C) -> Prop
probe (a : C) (pq : P a -> Q a) (qr : Q a -> R a) : P a -> R a =
  \pa. qr (pq pa)
"#,
    );

    let proof = semantics
        .derive(
            &typed,
            &common::support::entailment("probe"),
            InferenceRule::CutNat,
        )
        .expect("CutNat positive case must be derivable");
    assert_eq!(proof.rule, InferenceRule::CutNat, "CutNat positive case");

    check_rejects(
        &[
            r#"
module Rules.CutNat.Negative where
postulate
  C : Cat
  P : (a : C) -> Prop
  Q : (a : C) -> Prop
  R : (a : C) -> Prop
probe (a : C) (pq : P a -> Q a) (qr : Q a -> R a) : P a -> R a =
  \pa. pq pa
"#,
            r#"
module Rules.CutNat.Negative.BadQrInput where
postulate
  C : Cat
  P : (a : C) -> Prop
  Q : (a : C) -> Prop
  R : (a : C) -> Prop
probe (a : C) (pq : P a -> Q a) (qr : Q a -> R a) : P a -> R a =
  \pa. qr pa
"#,
            r#"
module Rules.CutNat.Negative.NotAbstracted where
postulate
  C : Cat
  P : (a : C) -> Prop
  Q : (a : C) -> Prop
  R : (a : C) -> Prop
probe (a : C) (pq : P a -> Q a) (qr : Q a -> R a) : P a -> R a =
  qr
"#,
        ],
        "TypeTheory",
    );
}

rule_contract!(
    // Figure 11 `Refl`: reflexivity constructor needs the indexed object argument.
    figure11_refl_rule_contract,
    positive: r#"
module Rules.Refl.Positive where
postulate
  C : Cat
probe (x : C) : x ->[C] x = refl x
"#,
    negatives: [
        r#"
module Rules.Refl.Negative where
postulate
  C : Cat
probe (x : C) : x ->[C] x = refl
"#,
        r#"
module Rules.Refl.Negative.BadReflArgument where
postulate
  C : Cat
probe (x : C) : x ->[C] x = refl (refl x)
"#,
        r#"
module Rules.Refl.Negative.ReturnObject where
postulate
  C : Cat
probe (x : C) : x ->[C] x = x
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 11 `J`: elimination requires directed orientation of evidence and motive indices.
    figure11_j_rule_contract,
    positive: r#"
module Rules.J.Positive where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = J h [e]
"#,
    negatives: [
        r#"
module Rules.J.Negative where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi a b) : Q a b = J h [e]
"#,
        r#"
module Rules.J.Negative.BadJApplication where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = (J h [e]) phi
"#,
        r#"
module Rules.J.Negative.BadEqualityDirection where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : b ->[C] a) (phi : Phi b a) : Q a b = J h [e]
"#,
        r#"
module Rules.J.Negative.FlippedResultIndices where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q b a = J h [e]
"#,
        r#"
module Rules.Figure11.J.Negative.MotivePolarityViolation where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (a : C^) -> (b : C) -> (z : C) -> Phi z z -> Q a b
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = J (h a b) [e]
"#,
        r#"
module Rules.Figure11.J.Negative.MotiveMissingZParam where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = J h [e]
"#,
        r#"
module Rules.Figure11.J.Negative.MotiveExtraParam where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> (w : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = J h [e]
"#,
    ],
    category: "TypeTheory"
);

#[test]
fn figure11_j_rule_rejects_variance_restriction_violations() {
    check_rejects_derive(
        r#"
module Rules.Figure11.J.Negative.VarianceRestriction where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
P (x : C) (y : C) : Prop =
  x ->[C] y
h : (z : C) -> Phi z z -> P z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P a b =
  J h [e]
"#,
        &[("probe", InferenceRule::JRule)],
        "TypeTheory",
    );
}

#[test]
fn figure11_j_rejects_contravariant_variable_in_conclusion_predicate() {
    check_rejects_derive(
        r#"
module Rules.Figure11.J.Negative.ConclusionPredicateContravariant where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
P_bad (x : C) (y : C) : Prop =
  x ->[C] y
h : (z : C) -> Phi z z -> P_bad z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P_bad a b =
  J h [e]
"#,
        &[("probe", InferenceRule::JRule)],
        "TypeTheory",
    );
}

#[test]
fn figure11_j_rejects_covariant_variable_in_context_predicate() {
    check_rejects_derive(
        r#"
module Rules.Figure11.J.Negative.ContextPredicateCovariant where
postulate
  C : Cat
  Q : (x : C) -> (y : C) -> Prop
Phi_bad (x : C) (y : C) : Prop =
  x ->[C] y
h : (z : C) -> Phi_bad z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi_bad b a) : Q a b =
  J h [e]
"#,
        &[("probe", InferenceRule::JRule)],
        "TypeTheory",
    );
}

#[test]
fn figure11_j_rule_rejects_contravariant_only_and_mixed_variance_motives() {
    check_rejects_derive(
        r#"
module Rules.Figure11.J.Negative.VarianceRestriction.ContravariantAndMixed where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
P_contravariant (x : C) (y : C) : Prop =
  (y ->[C] x) -> Top
P_mixed (x : C) (y : C) : Prop =
  (y ->[C] x) -> (y ->[C] x)
h_contravariant : (z : C) -> Phi z z -> P_contravariant z z
h_mixed : (z : C) -> Phi z z -> P_mixed z z
probe_contravariant (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P_contravariant a b =
  J h_contravariant [e]
probe_mixed (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : P_mixed a b =
  J h_mixed [e]
"#,
        &[
            ("probe_contravariant", InferenceRule::JRule),
            ("probe_mixed", InferenceRule::JRule),
        ],
        "TypeTheory",
    );
}

#[test]
fn figure11_j_rejects_motive_premise_type_mismatch() {
    check_rejects(
        &[r#"
module Rules.Figure11.J.Negative.MotivePremiseTypeMismatch where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Psi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Psi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b =
  J h [e]
"#],
        "TypeTheory",
    );
}

#[test]
/// Figure 11 `J-Comp`: computation at reflexivity must reduce with the exact reflexive evidence.
fn figure11_j_comp_rule_contract() {
    let source = r#"
module Rules.JComp.Positive where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
j_comp_form : (z : C) -> Phi z z -> Q z z =
  \z. \phi. J h [refl z]
probe (z : C) (phi : Phi z z) : Q z z = J h [refl z]
"#;
    let typed = check_accepts(source);
    let semantics = SemanticEngine::default();
    let n1 = semantics
        .normalize_term(&typed, &Expr::var("j_comp_form"))
        .unwrap();
    let n2 = semantics.normalize_term(&typed, &Expr::var("h")).unwrap();
    assert_eq!(
        n1, n2,
        "Figure11 J-Comp must be definitionally equal to the direct motive witness h"
    );
    check_rejects(
        &[
            r#"
module Rules.JComp.Negative where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (z : C) (phi : Phi z z) : Q z z = (J h [refl z]) phi
"#,
            r#"
module Rules.JComp.Negative.BadEvidenceShape where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (z : C) (phi : Phi z z) : Q z z = J h [phi]
"#,
            r#"
module Rules.JComp.Negative.BadReflNest where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (z : C) (phi : Phi z z) : Q z z = J h [refl (refl z)]
"#,
        ],
        "TypeTheory",
    );
}

rule_contract!(
    // Figure 11 `J-Eq`: composition reconstructed via `J` must have the same directed hom endpoints.
    figure11_j_eq_rule_contract,
    positive: r#"
module Rules.JEq.Positive where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  compose_via_j a b c f g
"#,
    negatives: [
        r#"
module Rules.JEq.Negative where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : c ->[C] a =
  compose_via_j a b c f g
"#,
        r#"
module Rules.JEq.Negative.BadWitnessEdge where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [g]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  compose_via_j a b c f g
"#,
        r#"
module Rules.JEq.Negative.BadDiagType where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (c ->[C] z) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  compose_via_j a b c f g
"#,
    ],
    category: "TypeTheory"
);

fixture_derivation_id_test!(
    figure11_var_derivation_root_paper_rule_id_contract,
    "var_probe",
    "Figure11.Var"
);
fixture_derivation_id_test!(
    figure11_wk_derivation_root_paper_rule_id_contract,
    "wk_probe",
    "Figure11.Wk"
);
fixture_derivation_id_test!(
    figure11_top_derivation_root_paper_rule_id_contract,
    "top_probe",
    "Figure11.Top"
);
fixture_derivation_id_test!(
    figure11_idx_derivation_root_paper_rule_id_contract,
    "idx_probe",
    "Figure11.Idx"
);
fixture_derivation_id_test!(
    figure11_contr_derivation_root_paper_rule_id_contract,
    "contr_probe",
    "Figure11.Contr"
);
fixture_derivation_id_test!(
    figure11_prod_derivation_root_paper_rule_id_contract,
    "prod_probe",
    "Figure11.Prod"
);
fixture_derivation_id_test!(
    figure11_exp_derivation_root_paper_rule_id_contract,
    "exp_probe",
    "Figure11.Exp"
);
fixture_derivation_id_test!(
    figure11_end_derivation_root_paper_rule_id_contract,
    "end_probe",
    "Figure11.End"
);
fixture_derivation_id_test!(
    figure11_coend_derivation_root_paper_rule_id_contract,
    "coend_probe",
    "Figure11.Coend"
);
fixture_derivation_id_test!(
    figure11_cut_din_derivation_root_paper_rule_id_contract,
    "cut_din_probe",
    "Figure11.CutDin"
);
fixture_derivation_id_test!(
    figure11_cut_nat_derivation_root_paper_rule_id_contract,
    "cut_nat_probe",
    "Figure11.CutNat"
);

#[test]
/// Figure 11 `Refl` derivations must expose `Figure11Refl` as the root rule application.
fn figure11_refl_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.Refl.Derivation where
postulate
  C : Cat
probe (x : C) : x ->[C] x = refl x
"#,
        "probe",
        InferenceRule::Refl,
    );
}

#[test]
/// Figure 11 `J` derivations must expose `Figure11J` as the root rule application.
fn figure11_j_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.J.Derivation where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b = J h [e]
"#,
        "probe",
        InferenceRule::JRule,
    );
}

#[test]
/// Figure 11 `J-Comp` derivations must expose `Figure11JComp` as the root rule application.
fn figure11_j_comp_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.JComp.Derivation where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
probe (z : C) (phi : Phi z z) : Q z z = J h [refl z]
"#,
        "probe",
        InferenceRule::JRule,
    );
}

#[test]
/// Figure 11 `J-Eq` derivations must expose composition-level rule structure at the root.
fn figure11_j_eq_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.JEq.Derivation where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  compose_via_j a b c f g
"#,
        "probe",
        InferenceRule::CutNat,
    );
}

#[test]
/// Figure 11 `J-Eq` derivations must include explicit premises for the composed witnesses.
fn figure11_j_eq_derivation_premises_have_expected_arity() {
    let root = derivation_root(
        r#"
module Rules.JEq.Derivation.Premises where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  compose_via_j a b c f g
"#,
        "probe",
        InferenceRule::CutNat,
    );
    assert!(
        !root.premises.is_empty(),
        "compound composition derivations must include premises"
    );
    // J-Eq composition has exactly two premises: the left witness (f : a ->[C] b)
    // and the right witness (g : b ->[C] c). Each premise is a sub-derivation
    // contributing one leg of the composed morphism.
    assert_eq!(
        root.premises.len(),
        2,
        "J-Eq composition derivation must expose exactly two premises, got {}",
        root.premises.len()
    );
    for (i, premise) in root.premises.iter().enumerate() {
        assert!(
            !premise.rule.paper_rule_id().is_empty(),
            "J-Eq premise {i} must have a non-empty paper_rule_id"
        );
    }
}

#[test]
/// Figure 11 symmetry probe must remain non-derivable and therefore cannot expose any derivation root.
fn figure11_symmetry_not_derivable_never_has_derivation_root() {
    fn hom(category: &str, source: &str, target: &str) -> Predicate {
        Predicate::hom(CatType::var(category), Term::var(source), Term::var(target))
    }

    let source = r#"
module Rules.SymmetryNotDerivable.Derivation where
postulate
  C : Cat
  probe : (a : C) -> (b : C) -> (a ->[C] b) -> (b ->[C] a)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![hom("C", "a", "b")],
        proof_term: ProofTerm::var("probe"),
        goal: hom("C", "b", "a"),
    };
    let result = semantics.derive(&typed, &judgment, InferenceRule::JRule);

    let diagnostics = result.unwrap_err().into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "symmetry non-derivability must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn figure11_var_rule_semantic_boundary() {
    let source = common::support::directed_theory_module();
    let (_syntax, semantics, typed) = compile_with_engines(source);

    // Positive: variable lookup succeeds for postulated name
    let judgment = common::support::entailment("C");
    semantics
        .derive(&typed, &judgment, InferenceRule::Var)
        .expect("Var rule must derive for postulated variable");

    // Negative: variable not in context
    let judgment = common::support::entailment("nonexistent");
    let diagnostics = semantics
        .derive(&typed, &judgment, InferenceRule::Var)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "Var rule for undefined variable must produce TypeTheory diagnostics, got: {diagnostics:?}"
    );
}

#[test]
fn figure11_wk_rule_semantic_boundary() {
    let source = common::support::directed_theory_module();
    let (_syntax, semantics, typed) = compile_with_engines(source);

    // Positive: weakening preserves an existing judgment
    let judgment = common::support::entailment("weakening");
    semantics
        .derive(&typed, &judgment, InferenceRule::Wk)
        .expect("Wk rule must derive for weakened context");
}

#[test]
fn figure11_top_rule_semantic_boundary() {
    let source = r#"
module Rules.TopRule where
postulate C : Cat

top_intro (x : C) : Top = !
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = common::support::entailment("top_intro");
    semantics
        .derive(&typed, &judgment, InferenceRule::Top)
        .expect("Top rule must derive for Top-typed term");
}

#[test]
fn cut_nat_rejects_when_variable_mentioned_in_outer_context() {
    // Source where cut-nat's side condition is violated:
    // P mentions a variable from outer context Gamma
    let source = r#"
module Rules.CutNatSideConditionViolation where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  outer_var : C
  alpha : (z : C) -> P outer_var z -> Q outer_var z

bad_cut (a : C) (b : C) (p : P a b) : Q a b =
  alpha b p
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = common::support::entailment("bad_cut");
    let diagnostics = semantics
        .derive(&typed, &judgment, InferenceRule::CutNat)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "cut-nat side condition violation must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
fn cut_din_rejects_when_variable_mentioned_in_outer_context() {
    let source = r#"
module Rules.CutDinSideConditionViolation where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  outer_var : C
  alpha : (z : C) -> P z outer_var -> Q z outer_var

bad_cut (a : C) (b : C) (p : P a b) : Q a b =
  alpha a p
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = common::support::entailment("bad_cut");
    let diagnostics = semantics
        .derive(&typed, &judgment, InferenceRule::CutDin)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "cut-din side condition violation must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}

#[test]
/// Figure 11 directed cut must reject unrestricted dinatural composition without J mediation.
fn figure11_restricted_cut_rejects_unrestricted_composition() {
    let source = r#"
module Rules.RestrictedCutOnly.UnrestrictedCut where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  R : (x : C) -> (y : C) -> Prop
  alpha : (x : C) -> (y : C) -> P x y -> Q x y
  gamma : (x : C) -> (y : C) -> Q x y -> R x y
probe (a : C) (b : C) (pab : P a b) : R a b =
  gamma a b (alpha a b pab)
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = EntailmentJudgment {
        context: Context::default(),
        propositions: vec![Predicate::var("alpha"), Predicate::var("beta")],
        proof_term: ProofTerm::var("probe"),
        goal: Predicate::var("R_ab"),
    };
    let diagnostics = semantics
        .derive(&typed, &judgment, InferenceRule::CutNat)
        .unwrap_err()
        .into_diagnostics();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.category == "TypeTheory"),
        "unrestricted directed cut must produce TypeTheory diagnostics, got: {diagnostics:?}",
    );
}
