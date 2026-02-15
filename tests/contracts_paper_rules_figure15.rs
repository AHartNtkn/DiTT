mod common;

use common::conformance::{assert_derivation_rule_from_source, check_accepts, derivation_root};
use common::engines::compile_with_engines;
use ditt_lang::api::{Expr, InferenceRule, Normalizer, TypeChecker};
use ditt_lang::runtime::SemanticEngine;

// Figure 15 is equational in the paper, but DiTT has no user-facing equality proposition.
// These tests enforce those equations as judgmental convertibility:
// a witness indexed by one cut form must be reusable at a convertible cut form.
//
// Equational laws are checked as derivable judgments with explicit rule structure.
// This complements `definitionally_equal` which checks convertibility without
// exposing the derivation structure. Both are needed: equational laws verify
// the specific rule was applied, while definitional equality verifies the outcome.

rule_contract!(
    // Figure 15 `AssocNatDinNat`: two cut-associated normal forms must be judgmentally interchangeable.
    figure15_assoc_nat_din_nat_rule_contract,
    positive: r#"
module Rules.Figure15.AssocNatDinNat.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Witness : (x : C) -> R x -> Prop

left (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  qr (pq p)

right (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  (\q. qr q) ((\u. pq u) p)

postulate
  seed : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> Witness x (left x pq qr p)

probe (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : Witness x (right x pq qr p) =
  seed x pq qr p
"#,
    negatives: [
        r#"
module Rules.Figure15.AssocNatDinNat.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Witness : (x : C) -> R x -> Prop
  opaque : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> R x

left (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  qr (pq p)

postulate
  seed : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> Witness x (left x pq qr p)

probe (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : Witness x (opaque x pq qr p) =
  seed x pq qr p
"#,
        r#"
module Rules.Figure15.AssocNatDinNat.Negative.BadResultIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Witness : (x : C) -> R x -> Prop

left (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  qr (pq p)

postulate
  seed : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> Witness x (left x pq qr p)

probe (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : Witness x (left x pq qr p) =
  seed x pq qr (pq p)
"#,
        r#"
module Rules.Figure15.AssocNatDinNat.Negative.WrongWitnessFamily where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Witness : (x : C) -> R x -> Prop
  opaque : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> R x

left (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  qr (pq p)

postulate
  seed : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> Witness x (left x pq qr p)

probe (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : Witness x (opaque x pq qr p) =
  seed x pq qr (opaque x pq qr p)
"#,
        r#"
module Rules.Figure15.AssocNatDinNat.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  R : (x : C) -> Prop
  Witness : (x : C) -> R x -> Prop
  opaque : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> R x

left (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  qr (pq p)

distinct (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : R x =
  opaque x pq qr p

postulate
  seed : (x : C) -> (pq : P x -> Q x) -> (qr : Q x -> R x) -> (p : P x) -> Witness x (left x pq qr p)

probe (x : C) (pq : P x -> Q x) (qr : Q x -> R x) (p : P x) : Witness x (distinct x pq qr p) =
  seed x pq qr p
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 15 `CutCoherence`: natural and dinatural-cut presentations must collapse to one judgmental form.
    figure15_cut_coherence_rule_contract,
    positive: r#"
module Rules.Figure15.CutCoherence.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

nat_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

din_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  (\u. f u) p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (nat_cut x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (din_cut x f p) =
  seed x f p
"#,
    negatives: [
        r#"
module Rules.Figure15.CutCoherence.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop
  opaque : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Q x

nat_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (nat_cut x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (opaque x f p) =
  seed x f p
"#,
        r#"
module Rules.Figure15.CutCoherence.Negative.BadArgument where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

nat_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (nat_cut x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (nat_cut x f p) =
  seed x f (f p)
"#,
        r#"
module Rules.Figure15.CutCoherence.Negative.WrongIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

nat_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (nat_cut x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (nat_cut x f p) =
  seed (f p) f p
"#,
        r#"
module Rules.Figure15.CutCoherence.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop
  opaque : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Q x

nat_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

distinct_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  opaque x f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (nat_cut x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (distinct_cut x f p) =
  seed x f p
"#,
    ],
    category: "TypeTheory"
);

#[test]
fn figure15_cut_coherence_associativity_via_j_parenthesizations_match() {
    check_accepts(
        r#"
module Rules.Figure15.CutCoherence.AssociativityViaJ where
postulate
  C : Cat
  Witness : (a : C) -> (d : C) -> (u : a ->[C] d) -> Prop

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

left_assoc (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (h : c ->[C] d) : a ->[C] d =
  compose_via_j a c d (compose_via_j a b c f g) h

right_assoc (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (h : c ->[C] d) : a ->[C] d =
  compose_via_j a b d f (compose_via_j b c d g h)

postulate
  seed : (a : C) -> (b : C) -> (c : C) -> (d : C) -> (f : a ->[C] b) -> (g : b ->[C] c) -> (h : c ->[C] d) -> Witness a d (left_assoc a b c d f g h)

probe (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (h : c ->[C] d) : Witness a d (right_assoc a b c d f g h) =
  seed a b c d f g h
"#,
    );
}

rule_contract!(
    // Figure 15 `CutNatIdL`: left identity of natural cut should be judgmentally transparent.
    figure15_cut_nat_id_l_rule_contract,
    positive: r#"
module Rules.Figure15.CutNatIdL.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Witness : (x : C) -> P x -> Prop

id_l_cut (x : C) (p : P x) : P x =
  (\u. u) p

postulate
  seed : (x : C) -> (p : P x) -> Witness x p

probe (x : C) (p : P x) : Witness x (id_l_cut x p) =
  seed x p
"#,
    negatives: [
        r#"
module Rules.Figure15.CutNatIdL.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Witness : (x : C) -> P x -> Prop
  opaque : (x : C) -> P x -> P x
  seed : (x : C) -> (p : P x) -> Witness x p

probe (x : C) (p : P x) : Witness x (opaque x p) =
  seed x p
"#,
        r#"
module Rules.Figure15.CutNatIdL.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Witness : (x : C) -> P x -> Prop
  seed : (x : C) -> (p : P x) -> Witness x p

probe (x : C) (p : P x) : Witness x p =
  seed x x
"#,
        r#"
module Rules.Figure15.CutNatIdL.Negative.WrongWitnessIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
  Witness : (x : C) -> P x -> Prop
  seed : (x : C) -> (p : P x) -> Witness x p

probe (x : C) (p : P x) : Witness x p =
  seed p p
"#,
        r#"
module Rules.Figure15.CutNatIdL.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  P : (x : C) -> Prop
  Witness : (x : C) -> P x -> Prop
  opaque : (x : C) -> P x -> P x

id_l_cut (x : C) (p : P x) : P x =
  (\u. u) p

distinct_cut (x : C) (p : P x) : P x =
  opaque x p

postulate
  seed : (x : C) -> (p : P x) -> Witness x (id_l_cut x p)

probe (x : C) (p : P x) : Witness x (distinct_cut x p) =
  seed x p
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 15 `CutNatIdR`: right identity of natural cut should not change the witnessed normal form.
    figure15_cut_nat_id_r_rule_contract,
    positive: r#"
module Rules.Figure15.CutNatIdR.Positive where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

cut_id_r (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f ((\u. u) p)

direct (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (direct x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (cut_id_r x f p) =
  seed x f p
"#,
    negatives: [
        r#"
module Rules.Figure15.CutNatIdR.Negative where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop
  opaque : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Q x

direct (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (direct x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (opaque x f p) =
  seed x f p
"#,
        r#"
module Rules.Figure15.CutNatIdR.Negative.BadSeedArg where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

direct (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (direct x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (direct x f p) =
  seed x f (f p)
"#,
        r#"
module Rules.Figure15.CutNatIdR.Negative.WrongIndex where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop

direct (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (direct x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (direct x f p) =
  seed (f p) f p
"#,
        r#"
module Rules.Figure15.CutNatIdR.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  P : (x : C) -> Prop
  Q : (x : C) -> Prop
  Witness : (x : C) -> Q x -> Prop
  opaque : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Q x

direct (x : C) (f : P x -> Q x) (p : P x) : Q x =
  f p

distinct_cut (x : C) (f : P x -> Q x) (p : P x) : Q x =
  opaque x f p

postulate
  seed : (x : C) -> (f : P x -> Q x) -> (p : P x) -> Witness x (direct x f p)

probe (x : C) (f : P x -> Q x) (p : P x) : Witness x (distinct_cut x f p) =
  seed x f p
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 15 `CutDinIdL`: left identity for directed/dinatural cut must preserve diagonal witness.
    figure15_cut_din_id_l_rule_contract,
    positive: r#"
module Rules.Figure15.CutDinIdL.Positive where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop

id_din_l (z : C) (phi : Phi z z) : Phi z z =
  (J (\w. \p. p) [refl z]) phi

postulate
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z (id_din_l z phi) =
  seed z phi
"#,
    negatives: [
        r#"
module Rules.Figure15.CutDinIdL.Negative where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  opaque : (z : C) -> Phi z z -> Phi z z
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z (opaque z phi) =
  seed z phi
"#,
        r#"
module Rules.Figure15.CutDinIdL.Negative.BadSeedArg where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z phi =
  seed z z
"#,
        r#"
module Rules.Figure15.CutDinIdL.Negative.BadIndex where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z phi =
  seed phi phi
"#,
        r#"
module Rules.Figure15.CutDinIdL.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  opaque : (z : C) -> Phi z z -> Phi z z

id_din_l (z : C) (phi : Phi z z) : Phi z z =
  (J (\w. \p. p) [refl z]) phi

distinct_cut (z : C) (phi : Phi z z) : Phi z z =
  opaque z phi

postulate
  seed : (z : C) -> (phi : Phi z z) -> Witness z (id_din_l z phi)

probe (z : C) (phi : Phi z z) : Witness z (distinct_cut z phi) =
  seed z phi
"#,
    ],
    category: "TypeTheory"
);

rule_contract!(
    // Figure 15 `CutDinIdR`: right identity for directed/dinatural cut must remain judgmentally equal.
    figure15_cut_din_id_r_rule_contract,
    positive: r#"
module Rules.Figure15.CutDinIdR.Positive where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop

id_din_r (z : C) (phi : Phi z z) : Phi z z =
  (\u. u) ((J (\w. \p. p) [refl z]) phi)

postulate
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z (id_din_r z phi) =
  seed z phi
"#,
    negatives: [
        r#"
module Rules.Figure15.CutDinIdR.Negative where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  opaque : (z : C) -> Phi z z -> Phi z z
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z (opaque z phi) =
  seed z phi
"#,
        r#"
module Rules.Figure15.CutDinIdR.Negative.BadSeedArg where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z phi =
  seed z z
"#,
        r#"
module Rules.Figure15.CutDinIdR.Negative.BadIndex where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  seed : (z : C) -> (phi : Phi z z) -> Witness z phi

probe (z : C) (phi : Phi z z) : Witness z phi =
  seed phi phi
"#,
        r#"
module Rules.Figure15.CutDinIdR.Negative.NonEquivalentTermsRemainDistinct where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop
  Witness : (z : C) -> Phi z z -> Prop
  opaque : (z : C) -> Phi z z -> Phi z z

id_din_r (z : C) (phi : Phi z z) : Phi z z =
  (\u. u) ((J (\w. \p. p) [refl z]) phi)

distinct_cut (z : C) (phi : Phi z z) : Phi z z =
  opaque z phi

postulate
  seed : (z : C) -> (phi : Phi z z) -> Witness z (id_din_r z phi)

probe (z : C) (phi : Phi z z) : Witness z (distinct_cut z phi) =
  seed z phi
"#,
    ],
    category: "TypeTheory"
);

#[test]
fn figure15_cut_din_id_l_and_id_r_are_definitionally_equal_to_identity() {
    let semantics = SemanticEngine::default();
    let typed = check_accepts(
        r#"
module Rules.Figure15.CutDinIdentity.Definitional where
postulate
  C : Cat
  Phi : (x : C) -> (y : C) -> Prop

id_din_l : (z : C) -> Phi z z -> Phi z z =
  \z. \phi. (J (\w. \p. p) [refl z]) phi

id_din_r : (z : C) -> Phi z z -> Phi z z =
  \z. \phi. (\u. u) ((J (\w. \p. p) [refl z]) phi)

direct : (z : C) -> Phi z z -> Phi z z =
  \z. \phi. phi
"#,
    );

    let n_id_l = semantics
        .normalize_term(&typed, &Expr::var("id_din_l"))
        .unwrap();
    let n_id_r = semantics
        .normalize_term(&typed, &Expr::var("id_din_r"))
        .unwrap();
    let n_direct = semantics
        .normalize_term(&typed, &Expr::var("direct"))
        .unwrap();

    assert_eq!(
        n_id_l, n_direct,
        "cut-din-id_l must be judgmentally equal to identity"
    );
    assert_eq!(
        n_id_r, n_direct,
        "cut-din-id_r must be judgmentally equal to identity"
    );
}

#[test]
fn figure15_cut_din_identity_left() {
    let source = r#"
module Rules.CutDinIdL where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  a : C

cut_din_id_l (alpha : P a a) : P a a =
  alpha
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = common::support::entailment("cut_din_id_l");
    semantics
        .derive(&typed, &judgment, InferenceRule::CutDin)
        .expect("cut-din left identity must be derivable");
}

#[test]
fn figure15_cut_din_identity_right() {
    let source = r#"
module Rules.CutDinIdR where
postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop
  a : C

cut_din_id_r (alpha : P a a) : P a a =
  alpha
"#;
    let (_syntax, semantics, typed) = compile_with_engines(source);

    let judgment = common::support::entailment("cut_din_id_r");
    semantics
        .derive(&typed, &judgment, InferenceRule::CutDin)
        .expect("cut-din right identity must be derivable");
}

#[test]
/// Figure 15 `CutNatIdL` derivations must expose `Figure15CutNatIdL` at the root.
fn figure15_left_identity_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.Figure15CutNatIdL.Derivation where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a a b (refl a) f
"#,
        "probe",
        InferenceRule::CutNat,
    );
}

#[test]
/// Figure 15 `CutNatIdL` derivations must expose identity and witness premises.
fn figure15_left_identity_derivation_premises_have_expected_arity() {
    let root = derivation_root(
        r#"
module Rules.Figure15CutNatIdL.Derivation.Premises where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a a b (refl a) f
"#,
        "probe",
        InferenceRule::CutNat,
    );
    assert!(
        !root.premises.is_empty(),
        "left-identity derivations must include premises"
    );
    // Left identity: compose_via_j a a b (refl a) f has two premises:
    // (1) the identity morphism (refl a) and (2) the retained witness f.
    assert_eq!(
        root.premises.len(),
        2,
        "left-identity derivation must expose two premises (identity and retained witness)"
    );
    for (i, premise) in root.premises.iter().enumerate() {
        assert!(
            !premise.rule.paper_rule_id().is_empty(),
            "left-identity premise {i} must have a non-empty paper_rule_id"
        );
    }
}

#[test]
/// Figure 15 `CutNatIdR` derivations must expose `Figure15CutNatIdR` at the root.
fn figure15_right_identity_derivation_root_rule_contract() {
    assert_derivation_rule_from_source(
        r#"
module Rules.Figure15CutNatIdR.Derivation where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a b b f (refl b)
"#,
        "probe",
        InferenceRule::CutNat,
    );
}

#[test]
/// Figure 15 `CutNatIdR` derivations must expose witness and identity premises.
fn figure15_right_identity_derivation_premises_have_expected_arity() {
    let root = derivation_root(
        r#"
module Rules.Figure15CutNatIdR.Derivation.Premises where
postulate
  C : Cat
diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k
compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g
probe (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a b b f (refl b)
"#,
        "probe",
        InferenceRule::CutNat,
    );
    assert!(
        !root.premises.is_empty(),
        "right-identity derivations must include premises"
    );
    // Right identity: compose_via_j a b b f (refl b) has two premises:
    // (1) the retained witness f and (2) the identity morphism (refl b).
    assert_eq!(
        root.premises.len(),
        2,
        "right-identity derivation must expose two premises (retained witness and identity)"
    );
    for (i, premise) in root.premises.iter().enumerate() {
        assert!(
            !premise.rule.paper_rule_id().is_empty(),
            "right-identity premise {i} must have a non-empty paper_rule_id"
        );
    }
}
