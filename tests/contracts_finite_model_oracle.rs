use std::collections::{BTreeMap, BTreeSet};

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
    compose: BTreeMap<(Mor, Mor), Mor>,
}

impl FiniteCategory {
    fn has_morphism(&self, from: Obj, to: Obj) -> bool {
        self.morphisms.contains(&Mor { from, to })
    }

    fn symmetric_for(&self, from: Obj, to: Obj) -> bool {
        if !self.has_morphism(from, to) {
            return true;
        }
        self.has_morphism(to, from)
    }

    fn all_have_identities(&self) -> bool {
        self.objects.iter().all(|o| self.id.contains_key(o))
    }

    fn has_left_and_right_identity_laws(&self) -> bool {
        if !self.all_have_identities() {
            return false;
        }
        for &mor in &self.morphisms {
            let id_target = self.id[&mor.to];
            let id_source = self.id[&mor.from];
            // Left identity: id_B . f = f
            match self.compose.get(&(id_target, mor)) {
                Some(&result) if result == mor => {}
                _ => return false,
            }
            // Right identity: f . id_A = f
            match self.compose.get(&(mor, id_source)) {
                Some(&result) if result == mor => {}
                _ => return false,
            }
        }
        true
    }
}

fn interval_category() -> FiniteCategory {
    let o0 = Obj("0");
    let o1 = Obj("1");
    let id0 = Mor { from: o0, to: o0 };
    let id1 = Mor { from: o1, to: o1 };
    let m01 = Mor { from: o0, to: o1 };
    let mut compose = BTreeMap::new();
    // id_0 . id_0 = id_0
    compose.insert((id0, id0), id0);
    // id_1 . id_1 = id_1
    compose.insert((id1, id1), id1);
    // id_1 . m01 = m01  (left identity)
    compose.insert((id1, m01), m01);
    // m01 . id_0 = m01  (right identity)
    compose.insert((m01, id0), m01);
    FiniteCategory {
        objects: [o0, o1].into_iter().collect(),
        morphisms: [id0, id1, m01].into_iter().collect(),
        id: [(o0, id0), (o1, id1)].into_iter().collect(),
        compose,
    }
}

fn two_object_groupoid() -> FiniteCategory {
    let a = Obj("A");
    let b = Obj("B");
    let ida = Mor { from: a, to: a };
    let idb = Mor { from: b, to: b };
    let f = Mor { from: a, to: b };
    let g = Mor { from: b, to: a };
    let mut compose = BTreeMap::new();
    // id . id = id
    compose.insert((ida, ida), ida);
    compose.insert((idb, idb), idb);
    // id_B . f = f,  f . id_A = f
    compose.insert((idb, f), f);
    compose.insert((f, ida), f);
    // id_A . g = g,  g . id_B = g
    compose.insert((ida, g), g);
    compose.insert((g, idb), g);
    // g . f = id_A,  f . g = id_B  (groupoid inverses)
    compose.insert((g, f), ida);
    compose.insert((f, g), idb);
    FiniteCategory {
        objects: [a, b].into_iter().collect(),
        morphisms: [ida, idb, f, g].into_iter().collect(),
        id: [(a, ida), (b, idb)].into_iter().collect(),
        compose,
    }
}

#[test]
fn oracle_countermodel_shows_symmetry_not_generally_derivable() {
    let i = interval_category();
    assert!(i.has_morphism(Obj("0"), Obj("1")));
    assert!(!i.symmetric_for(Obj("0"), Obj("1")));
}

#[test]
fn oracle_groupoid_model_shows_symmetry_can_hold_in_special_models() {
    let g = two_object_groupoid();
    assert!(g.symmetric_for(Obj("A"), Obj("B")));
    assert!(g.symmetric_for(Obj("B"), Obj("A")));
}

#[test]
fn oracle_identity_laws_hold_in_reference_models() {
    let i = interval_category();
    let g = two_object_groupoid();
    assert!(i.has_left_and_right_identity_laws());
    assert!(g.has_left_and_right_identity_laws());
}
