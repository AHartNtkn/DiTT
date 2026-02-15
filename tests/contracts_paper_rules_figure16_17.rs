mod common;

use common::conformance::check_accepts;
use ditt_lang::api::*;
use ditt_lang::runtime::SemanticEngine;

// Figure 16/17 equations are enforced as judgmental convertibility.
// There is no user-facing equality proposition in DiTT.

rule_contract!(
    // Figure 16 `EndIntro`: introduction uses `end k` from a full family, not an eliminator form.
    figure16_end_intro_rule_contract,
    positive: r#"
module Rules.Figure16.EndIntro.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : end (x : C). P x =
  end k
"#,
    negatives: [
        r#"
module Rules.Figure16.EndIntro.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : end (x : C). P x =
  end^-1 k
"#,
        r#"
module Rules.Figure16.EndIntro.Negative.BadResultType where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : (x : C) -> P x =
  end k
"#,
        r#"
module Rules.Figure16.EndIntro.Negative.BadWitness where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : end (x : C). P x =
  k
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndElim`: elimination requires `end^-1 h` before applying an index.
    figure16_end_elim_rule_contract,
    positive: r#"
module Rules.Figure16.EndElim.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x =
  (end^-1 h) x
"#,
    negatives: [
        r#"
module Rules.Figure16.EndElim.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x =
  end^-1 (h x)
"#,
        r#"
module Rules.Figure16.EndElim.Negative.TreatEndAsFunction where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x =
  h x
"#,
        r#"
module Rules.Figure16.EndElim.Negative.BadElimArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : end (x : C). P x
probe (x : C) : P x =
  (end^-1 h) h
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `CoendIntro`: introduction uses `coend k` from a full family, not an eliminator/opaque form.
    figure16_coend_intro_rule_contract,
    positive: r#"
module Rules.Figure16.CoendIntro.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : coend (x : C). P x =
  coend k
"#,
    negatives: [
        r#"
module Rules.Figure16.CoendIntro.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : coend (x : C). P x =
  coend^-1 k
"#,
        r#"
module Rules.Figure16.CoendIntro.Negative.BadResultType where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : (x : C) -> P x =
  coend k
"#,
        r#"
module Rules.Figure16.CoendIntro.Negative.OpaqueHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
  opaque : ((x : C) -> P x) -> coend (x : C). P x
probe : coend (x : C). P x =
  opaque k
"#,
        r#"
module Rules.Figure16.CoendIntro.Negative.BadWitnessArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x
probe : coend (x : C). P x =
  coend (\x. k)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `CoendElim`: elimination requires `coend^-1 h` before applying an index.
    figure16_coend_elim_rule_contract,
    positive: r#"
module Rules.Figure16.CoendElim.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : coend (x : C). P x
probe (x : C) : P x =
  (coend^-1 h) x
"#,
    negatives: [
        r#"
module Rules.Figure16.CoendElim.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : coend (x : C). P x
probe (x : C) : P x =
  coend^-1 (h x)
"#,
        r#"
module Rules.Figure16.CoendElim.Negative.TreatCoendAsFunction where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : coend (x : C). P x
probe (x : C) : P x =
  h x
"#,
        r#"
module Rules.Figure16.CoendElim.Negative.BadElimArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  h : coend (x : C). P x
probe (x : C) : P x =
  (coend^-1 h) h
"#,
        r#"
module Rules.Figure16.CoendElim.Negative.PolarityMismatch where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  h : coend (x : C). P x x
probe (a : C^) (b : C) : P b a = (coend^-1 h) a
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndIsoLeft`: `end^-1 (end k)` must be interchangeable with `k`.
    figure16_end_iso_left_rule_contract,
    positive: r#"
module Rules.Figure16.EndIsoLeft.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
probe (k : (x : C) -> P x) : Obs (end^-1 (end k)) =
  seed k
"#,
    negatives: [
        r#"
module Rules.Figure16.EndIsoLeft.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
  opaque : ((x : C) -> P x) -> ((x : C) -> P x)
probe (k : (x : C) -> P x) : Obs (opaque k) =
  seed k
"#,
        r#"
module Rules.Figure16.EndIsoLeft.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
probe (k : (x : C) -> P x) : Obs k =
  seed (k k)
"#,
        r#"
module Rules.Figure16.EndIsoLeft.Negative.BadWitnessHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : ((x : C) -> P x) -> Prop
  seed : (k : (x : C) -> P x) -> Obs k
probe (k : (x : C) -> P x) : Obs (end^-1 (end k)) =
  seed (end^-1 k)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndIsoRight`: `end (end^-1 h)` must be interchangeable with `h`.
    figure16_end_iso_right_rule_contract,
    positive: r#"
module Rules.Figure16.EndIsoRight.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
probe (h : end (x : C). P x) : Obs (end (end^-1 h)) =
  seed h
"#,
    negatives: [
        r#"
module Rules.Figure16.EndIsoRight.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
  opaque : (h : end (x : C). P x) -> end (x : C). P x
probe (h : end (x : C). P x) : Obs (opaque h) =
  seed h
"#,
        r#"
module Rules.Figure16.EndIsoRight.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
probe (h : end (x : C). P x) : Obs h =
  seed (end^-1 h)
"#,
        r#"
module Rules.Figure16.EndIsoRight.Negative.BadWitnessHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Obs : (h : end (x : C). P x) -> Prop
  seed : (h : end (x : C). P x) -> Obs h
probe (h : end (x : C). P x) : Obs (end (end^-1 h)) =
  seed (end^-1 h)
"#,
    ],
    category: "TypeTheory"
);

#[test]
fn figure16_end_roundtrip_is_definitionally_equal_to_original_witness() {
    let source = r#"
module Rules.Figure16.EndIso.RoundTrip.DefinitionalEquality where
postulate
  C : Cat
  P : (x : C) -> Prop
  k : (x : C) -> P x

round_trip : (x : C) -> P x =
  end^-1 (end (end^-1 (end k)))

direct : (x : C) -> P x =
  k
"#;
    let typed = check_accepts(source);
    let semantics = SemanticEngine::default();
    let n1 = semantics
        .normalize_term(&typed, &Expr::var("round_trip"))
        .unwrap();
    let n2 = semantics
        .normalize_term(&typed, &Expr::var("direct"))
        .unwrap();
    assert_eq!(
        n1, n2,
        "end^-1(end(end^-1(end k))) must be definitionally equal to k"
    );
}

rule_contract!(
    // Figure 16 `EndNatLeft`: natural map under `end` must keep the same judgmental transformed end.
    figure16_end_nat_left_rule_contract,
    positive: r#"
module Rules.Figure16.EndNatLeft.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. t x ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. (\u. t x u) ((end^-1 h) x))) =
  seed t h
"#,
    negatives: [
        r#"
module Rules.Figure16.EndNatLeft.Negative where
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
        r#"
module Rules.Figure16.EndNatLeft.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. t x ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed t (end^-1 h)
"#,
        r#"
module Rules.Figure16.EndNatLeft.Negative.BadHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. t x ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed (\x. \p. p) h
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndDinLeft`: dinatural left form must preserve same indexed `Obs x (...)` witness.
    figure16_end_din_left_rule_contract,
    positive: r#"
module Rules.Figure16.EndDinLeft.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((end^-1 h) x))
probe (x : C) (h : end (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x ((\u. t x u) ((end^-1 h) x)) =
  seed x h t
"#,
    negatives: [
        r#"
module Rules.Figure16.EndDinLeft.Negative where
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
        r#"
module Rules.Figure16.EndDinLeft.Negative.BadIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((end^-1 h) x))
probe (x : C) (h : end (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x (t x ((end^-1 h) x)) =
  seed ((end^-1 h) x) h t
"#,
        r#"
module Rules.Figure16.EndDinLeft.Negative.BadHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (x : C) -> Q x -> Prop
  seed : (x : C) -> (h : end (x : C). P x) -> (t : (x : C) -> P x -> Q x) -> Obs x (t x ((end^-1 h) x))
probe (x : C) (h : end (x : C). P x) (t : (x : C) -> P x -> Q x) : Obs x (t x ((end^-1 h) x)) =
  seed x h (\x. \p. p)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndDinRight`: dinatural right form under `end` must preserve exact constructed head.
    figure16_end_din_right_rule_contract,
    positive: r#"
module Rules.Figure16.EndDinRight.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (end (\x. t x (k x)))
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (end (\x. (\u. t x u) (k x))) =
  seed k t
"#,
    negatives: [
        r#"
module Rules.Figure16.EndDinRight.Negative where
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
        r#"
module Rules.Figure16.EndDinRight.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (end (\x. t x (k x)))
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (end (\x. t x (k x))) =
  seed k (\x. \p. p)
"#,
        r#"
module Rules.Figure16.EndDinRight.Negative.BadFamilyArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (k : (x : C) -> P x) -> (t : (x : C) -> P x -> Q x) -> Obs (end (\x. t x (k x)))
probe (k : (x : C) -> P x) (t : (x : C) -> P x -> Q x) : Obs (end (\x. t x (k x))) =
  seed (end^-1 (end k)) t
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 16 `EndNatRight`: natural-right form must preserve judgmental equality of the transformed `end`.
    figure16_end_nat_right_rule_contract,
    positive: r#"
module Rules.Figure16.EndNatRight.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. (\u. t x u) ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed t h
"#,
    negatives: [
        r#"
module Rules.Figure16.EndNatRight.Negative where
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
        r#"
module Rules.Figure16.EndNatRight.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. (\u. t x u) ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed (\x. \p. p) h
"#,
        r#"
module Rules.Figure16.EndNatRight.Negative.BadHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Obs : (u : end (x : C). Q x) -> Prop
  seed : (t : (x : C) -> P x -> Q x) -> (h : end (x : C). P x) -> Obs (end (\x. (\u. t x u) ((end^-1 h) x)))
probe (t : (x : C) -> P x -> Q x) (h : end (x : C). P x) : Obs (end (\x. t x ((end^-1 h) x))) =
  seed t (end^-1 h)
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 17 `EndFunctoriality`: composed end-maps must preserve same final `end` witness by judgmental equality.
    figure17_end_functoriality_rule_contract,
    positive: r#"
module Rules.Figure17.EndFunctoriality.Positive where
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
    negatives: [
        r#"
module Rules.Figure17.EndFunctoriality.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : end (x : C). R x) -> Prop
  seed : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (end (\x. g x (f x ((end^-1 h) x))))
  opaque : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> end (x : C). R x
probe (h : end (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (opaque h f g) =
  seed h f g
"#,
        r#"
module Rules.Figure17.EndFunctoriality.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : end (x : C). R x) -> Prop
  seed : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (end (\x. g x (f x ((end^-1 h) x))))
probe (h : end (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (end (\x. g x ((\y. f y ((end^-1 h) y)) x))) =
  seed h f (\x. \q. q)
"#,
        r#"
module Rules.Figure17.EndFunctoriality.Negative.BadHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : end (x : C). R x) -> Prop
  seed : (h : end (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (end (\x. g x (f x ((end^-1 h) x))))
probe (h : end (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (end (\x. g x ((\y. f y ((end^-1 h) y)) x))) =
  seed (end^-1 h) f g
"#,
        r#"
module Rules.Figure17.EndFunctoriality.Negative.TypeMismatch where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  h : end (x : C). P x
  f : (x : C) -> P x -> Q x
  g : (x : C) -> R x -> Q x
probe : end (x : C). Q x = end (\x. g x ((end^-1 h) x))
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 17 `CoendFunctoriality`: composed coend-maps must preserve the same final `coend` witness by judgmental equality.
    figure17_coend_functoriality_rule_contract,
    positive: r#"
module Rules.Figure17.CoendFunctoriality.Positive where
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
    negatives: [
        r#"
module Rules.Figure17.CoendFunctoriality.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : coend (x : C). R x) -> Prop
  seed : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (coend (\x. g x (f x ((coend^-1 h) x))))
  opaque : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> coend (x : C). R x
probe (h : coend (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (opaque h f g) =
  seed h f g
"#,
        r#"
module Rules.Figure17.CoendFunctoriality.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : coend (x : C). R x) -> Prop
  seed : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (coend (\x. g x (f x ((coend^-1 h) x))))
probe (h : coend (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (coend (\x. g x ((\y. f y ((coend^-1 h) y)) x))) =
  seed h f (\x. \q. q)
"#,
        r#"
module Rules.Figure17.CoendFunctoriality.Negative.BadHead where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Obs : (u : coend (x : C). R x) -> Prop
  seed : (h : coend (x : C). P x) -> (f : (x : C) -> P x -> Q x) -> (g : (x : C) -> Q x -> R x) -> Obs (coend (\x. g x (f x ((coend^-1 h) x))))
probe (h : coend (x : C). P x) (f : (x : C) -> P x -> Q x) (g : (x : C) -> Q x -> R x) : Obs (coend (\x. g x ((\y. f y ((coend^-1 h) y)) x))) =
  seed (coend^-1 h) f g
"#,
    ],
    category: "TypeTheory"
);
