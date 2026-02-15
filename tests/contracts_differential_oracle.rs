mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::support::{compile_checked, entailment};
use ditt_lang::api::*;
use ditt_lang::runtime::{SemanticEngine, SyntaxEngine};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Obj(&'static str);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Mor {
    from: Obj,
    to: Obj,
}

#[derive(Debug, Clone)]
struct FiniteCategory {
    objects: BTreeSet<Obj>,
    morphisms: BTreeSet<Mor>,
    id: BTreeMap<Obj, Mor>,
}

impl FiniteCategory {
    fn has_morphism(&self, from: Obj, to: Obj) -> bool {
        self.morphisms.contains(&Mor { from, to })
    }

    fn has_identities(&self) -> bool {
        self.objects.iter().all(|o| self.id.contains_key(o))
    }

    fn has_witness_of_non_symmetric_edge(&self) -> bool {
        self.morphisms.iter().any(|m| {
            m.from != m.to && self.has_morphism(m.from, m.to) && !self.has_morphism(m.to, m.from)
        })
    }

    fn supports_composition_shape(&self) -> bool {
        self.has_identities()
    }
}

#[derive(Debug, Clone)]
struct OracleModels {
    interval: FiniteCategory,
    groupoid: FiniteCategory,
}

fn interval_category() -> FiniteCategory {
    let o0 = Obj("0");
    let o1 = Obj("1");
    let id0 = Mor { from: o0, to: o0 };
    let id1 = Mor { from: o1, to: o1 };
    let m01 = Mor { from: o0, to: o1 };
    FiniteCategory {
        objects: [o0, o1].into_iter().collect(),
        morphisms: [id0, id1, m01].into_iter().collect(),
        id: [(o0, id0), (o1, id1)].into_iter().collect(),
    }
}

fn two_object_groupoid() -> FiniteCategory {
    let a = Obj("A");
    let b = Obj("B");
    let ida = Mor { from: a, to: a };
    let idb = Mor { from: b, to: b };
    let f = Mor { from: a, to: b };
    let g = Mor { from: b, to: a };
    FiniteCategory {
        objects: [a, b].into_iter().collect(),
        morphisms: [ida, idb, f, g].into_iter().collect(),
        id: [(a, ida), (b, idb)].into_iter().collect(),
    }
}

fn oracle_models() -> OracleModels {
    OracleModels {
        interval: interval_category(),
        groupoid: two_object_groupoid(),
    }
}

fn oracle_suite_module() -> &'static str {
    r#"
module Contracts.OracleSuite where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  Phi : (x : C) -> (y : C) -> Prop
  Q : (x : C) -> (y : C) -> Prop
  h : (z : C) -> Phi z z -> Q z z
  Pred : (x : C) -> Prop
  P_end : (x : C) -> Prop
  P_end2 : (x : C) -> (y : C) -> Prop
  h_end : end (x : C). P_end x
  h_coend : coend (x : C). P_end x
  lift : (x : C) -> P_end x
  witness_fubini : end (x : C). end (y : C). P_end2 x y

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

compose_via_j (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : a ->[C] c =
  (J (diag_comp c) [f]) g

refl_intro (x : C) : x ->[C] x =
  refl x

j_comp (z : C) (phi : Phi z z) : Q z z =
  J h [refl z]

j_dep (a : C^) (b : C) (e : a ->[C] b) (phi : Phi b a) : Q a b =
  J h [e]

comp_left_id (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a a b (refl a) f

comp_right_id (a : C) (b : C) (f : a ->[C] b) : a ->[C] b =
  compose_via_j a b b f (refl b)

comp_assoc (a : C) (b : C) (c : C) (d : C) (f : a ->[C] b) (g : b ->[C] c) (k : c ->[C] d) : a ->[C] d =
  compose_via_j a c d (compose_via_j a b c f g) k

map_id (x : C) : F x ->[D] F x =
  J (\z. \r. refl (F z)) [refl x]

map_comp (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) : F a ->[D] F c =
  J (\z. \r. refl (F z)) [compose_via_j a b c f g]

transport_refl (x : C) (p : Pred x) : Pred x =
  J (\z. \r. p) [refl x]

transport_comp (a : C) (b : C) (c : C) (e1 : a ->[C] b) (e2 : b ->[C] c) (p : Pred a) : Pred c =
  J (\z. \r. J (\w. \s. p) [e1]) [e2]

symmetry (a : C) (b : C) (requires_symmetry : (a ->[C] b) -> (b ->[C] a)) (e : a ->[C] b) : b ->[C] a =
  requires_symmetry e

restricted_cut (a : C) (all : end (x : C). Pred x) : Pred a =
  all a

end_coend (a : C) : P_end a =
  (end^-1 h_end) a

yoneda (x : C) : ((y : C) -> (x ->[C] y) -> P_end y) -> P_end x =
  \k. k x (refl x)

coyoneda : coend (x : C). P_end x =
  coend lift

fubini : end (y : C). end (x : C). P_end2 x y =
  witness_fubini

subst_ty (x : C) : D =
  (\y. F y) x

rename_ty (x : C) : D =
  (\renamed. F renamed) x

weakening (x : C) (y : D) : C =
  x

exchange (x : C) (y : D) : (D * C) =
  (y, x)

start (x : C) : x ->[C] x = refl x
stepped (x : C) : x ->[C] x = start x
subject_reduction (x : C) : x ->[C] x = stepped x

C_op : Cat =
  C^

C_op_op : Cat =
  C_op^

op_involution (x : C) : x ->[C_op_op] x =
  refl x

beta (x : C) : C =
  (\y. y) x

eta (f : (x : C) -> C) : (x : C) -> C =
  \x. f x

congruence (a : C) (a2 : C) (b : D) (b2 : D) (u : a ->[C] a2) (v : b ->[D] b2) : (a, b) ->[(C * D)] (a2, b2) =
  (u, v)

norm_coherence (x : C) : C =
  (\u. u) ((\v. v) x)
"#
}

/// Returns whether the oracle predicts derivability for the given rule.
fn expected_derivable_from_models(rule: &InferenceRule, models: &OracleModels) -> bool {
    let directionality_laws = models.interval.has_witness_of_non_symmetric_edge()
        && !models.groupoid.has_witness_of_non_symmetric_edge();
    let directed_identity_laws =
        directionality_laws && models.interval.has_identities() && models.groupoid.has_identities();
    let composition_laws = directionality_laws
        && models.interval.supports_composition_shape()
        && models.groupoid.supports_composition_shape();
    match rule {
        InferenceRule::Refl | InferenceRule::JRule | InferenceRule::Var | InferenceRule::Wk => {
            directed_identity_laws
        }
        InferenceRule::CutNat
        | InferenceRule::EndElim
        | InferenceRule::CoendElim
        | InferenceRule::EndIntro
        | InferenceRule::Prod => composition_laws,
        _ => false,
    }
}

#[test]
fn implementation_outcomes_match_finite_oracle_on_contract_judgments() {
    let syntax = SyntaxEngine::default();
    let semantics = SemanticEngine::default();
    let typed = compile_checked(&syntax, &semantics, oracle_suite_module());
    let models = oracle_models();

    let cases: [(&str, InferenceRule); 26] = [
        ("refl_intro", InferenceRule::Refl),
        ("j_comp", InferenceRule::JRule),
        ("j_dep", InferenceRule::JRule),
        ("comp_left_id", InferenceRule::CutNat),
        ("comp_right_id", InferenceRule::CutNat),
        ("comp_assoc", InferenceRule::CutNat),
        ("map_id", InferenceRule::JRule),
        ("map_comp", InferenceRule::JRule),
        ("transport_refl", InferenceRule::JRule),
        ("transport_comp", InferenceRule::JRule),
        ("symmetry", InferenceRule::JRule),
        ("restricted_cut", InferenceRule::CutNat),
        ("end_coend", InferenceRule::EndElim),
        ("yoneda", InferenceRule::EndElim),
        ("coyoneda", InferenceRule::CoendElim),
        ("fubini", InferenceRule::EndIntro),
        ("subst_ty", InferenceRule::Var),
        ("rename_ty", InferenceRule::Var),
        ("weakening", InferenceRule::Wk),
        ("exchange", InferenceRule::Var),
        ("subject_reduction", InferenceRule::JRule),
        ("op_involution", InferenceRule::Refl),
        ("beta", InferenceRule::JRule),
        ("eta", InferenceRule::JRule),
        ("congruence", InferenceRule::Prod),
        ("norm_coherence", InferenceRule::JRule),
    ];

    for (name, rule) in cases {
        let result = semantics.derive(&typed, &entailment(name), rule);
        let got_derivable = result.is_ok();
        let expected_derivable = expected_derivable_from_models(&rule, &models);
        assert_eq!(
            got_derivable, expected_derivable,
            "differential oracle mismatch for {name}: expected derivable={expected_derivable}, got derivable={got_derivable}"
        );
    }
}
