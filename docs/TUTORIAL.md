# DiTT Tutorial

This tutorial introduces the DiTT (Directed Type Theory) programming language, based on the first-order directed type theory from:

> Andrea Laretto, Fosco Loregian, Niccolo Veltri, *Di- is for Directed: First-Order Directed Type Theory via Dinaturality* (POPL 2026).

DiTT is a proof-oriented language where types are categories and equality proofs are directed morphisms. Unlike Homotopy Type Theory (HoTT), where paths between types are always invertible, DiTT's morphisms go in one direction only. This asymmetry captures the mathematical reality of categories, where a morphism from A to B does not imply a morphism from B to A.

The tutorial progresses from basic concepts to advanced constructions. Each section builds on the previous ones. All code examples are complete, valid DiTT programs. Every construction demonstrated here appears in the standard library (`stdlib/`).


## 1. Categories and Objects

In DiTT, the basic sorts are *categories*. A category is not something you construct inside the language; it is introduced as a postulate in a fixed signature. Think of it as declaring "there exists a category C" for the rest of the module to use.

```ditt
module Tutorial.Categories where

postulate C : Cat
```

The `postulate` keyword introduces an assumption. Here, `C` is assumed to be a category. You can group multiple postulates in a block:

```ditt
module Tutorial.CategoriesMultiple where

postulate
  C : Cat
  D : Cat
```

Categories support three structural operations:

- **Product** `C × D` --- the product category, whose objects are pairs and whose morphisms are componentwise.
- **Opposite** `C^` --- the opposite category, where all morphisms are reversed.
- **Functor category** `C → D` --- the category of functors from C to D.

Objects of a category are introduced as terms. A term `x : C` is an object of the category C. There is no separate notion of "element" vs "object" --- everything in DiTT is an object of some category.

**Stdlib module:** `Std.Category`
**Paper reference:** Figure 7 defines the grammar of category-level types.


## 2. Morphisms and Identity

The central concept in DiTT is the *directed hom type*. A morphism from `a` to `b` in category `C` is written:

```
a →[C] b
```

This is not an equality type. It is a directed morphism type: having a term of type `a →[C] b` means there exists a morphism from `a` to `b` in `C`, but says nothing about a morphism from `b` to `a`.

The identity morphism is constructed by `refl`:

```ditt
module Tutorial.Morphisms where

postulate C : Cat

id (x : C) : x →[C] x = refl x
```

`refl x` has type `x →[C] x` --- it is the identity morphism on `x`. This is analogous to how `refl` in HoTT constructs a path from `x` to `x`, but here it is a morphism, not a symmetric path.

The critical difference from HoTT: having `f : a →[C] b` does **not** give you `g : b →[C] a`. Morphisms are one-way. This is the defining feature of the theory, not a limitation.

**Stdlib module:** `Std.Category` (defines `id`)
**Paper reference:** Figures 8 and 9 define the term and predicate grammars, respectively, including the hom predicate form.


## 3. Composition via J

Morphisms can be composed using the J eliminator. J is the fundamental operation on directed equality --- it takes a *diagonal witness* (a function that works at the identity) and a morphism, and produces a function that works along that morphism.

The typing principle: if `h(z)` does something when the source and target are the same (`z`), then `J h [f]` does the analogous thing along a morphism `f : a →[C] b`.

The computation rule is: `J h [refl z]` reduces to `h z`. That is, applying J to the identity morphism recovers the diagonal witness.

Here is morphism composition:

```ditt
module Tutorial.Composition where

postulate C : Cat

// Diagonal witness: identity on morphisms into c
diag_comp (c : C) (z : C) : (z →[C] c) → (z →[C] c) =
  λk. k

// Composition: given f : a → b and g : b → c, produce a → c
compose (a : C^) (b : C) (c : C) (f : a →[C] b) (g : b →[C] c) : a →[C] c =
  (J (diag_comp c) [f]) g
```

Walk through this carefully:

1. `diag_comp c z` is the identity function on `z →[C] c`. When source and target coincide at `z`, "composing" with the identity is just the identity function.
2. `J (diag_comp c) [f]` takes this diagonal witness and extends it along `f : a →[C] b`. J transforms `diag_comp c` along `f`, yielding a function from `(b →[C] c)` to `(a →[C] c)`.
3. Applying this to `g : b →[C] c` gives `a →[C] c`.

Notice that `a : C^` --- `a` appears in the opposite (contravariant) position. This is required by J's typing rule: the source of the morphism must have opposite variance.

The identity laws and associativity are expressible as definitions whose types witness the equalities. The type checker verifies these judgmentally:

```ditt
// Left identity: compose (refl a) f = f
compose_left_id (a : C) (b : C) (f : a →[C] b) : a →[C] b =
  compose a a b (refl a) f

// Right identity: compose f (refl b) = f
compose_right_id (a : C) (b : C) (f : a →[C] b) : a →[C] b =
  compose a b b f (refl b)

// Associativity
compose_assoc (a : C) (b : C) (c : C) (d : C)
  (f : a →[C] b) (g : b →[C] c) (k : c →[C] d) : a →[C] d =
  compose a c d (compose a b c f g) k
```

**Stdlib module:** `Std.Morphism` (defines `compose`, identity laws, associativity, and opposite hom isomorphisms)
**Paper reference:** Figure 11 (J rule), Example 3.1.


## 4. Opposite Categories

The opposite category `C^` reverses all morphisms. A morphism `a →[C^] b` in the opposite category corresponds to a morphism `b →[C] a` in the original category.

Double opposite cancels: `C^^` reduces to `C` judgmentally. This is not an axiom you need to prove --- the type checker treats `C^^` and `C` as the same type.

Variance is tracked automatically by the type checker. Every variable in a term has one of four variance classifications:

- **Covariant** --- appears only in positive positions.
- **Contravariant** --- appears only in negative positions (under `C^`).
- **Dinatural** --- appears in both covariant and contravariant positions.
- **Unused** --- does not appear.

You never write variance annotations. The checker infers them and rejects terms where the variance requirements of a construct are violated.

The opposite hom isomorphism converts between morphisms in C and morphisms in C^op. The J eliminator with diagonal `λz. refl z` witnesses this: at the diagonal, `z →[C^] z` equals `z →[C] z` by double-opposite reduction.

```ditt
// hom_C(x, y) → hom_{C^op}(y, x)
op_hom_forward (x : C) (y : C) (f : x →[C] y) : y →[C^] x =
  J (λz. refl z) [f]

// hom_{C^op}(y, x) → hom_C(x, y)
op_hom_backward (x : C) (y : C) (g : y →[C^] x) : x →[C] y =
  J (λz. refl z) [g]
```

**Stdlib module:** `Std.Morphism` (defines `op_hom_forward`, `op_hom_backward`)
**Paper reference:** Figure 7 (category grammar), Figure 10 (variance rules), Definition 2.5 (opposite categories), Appendix B.5 (opposite hom iso).


## 5. Functors

A functor `F : C → D` maps objects of C to objects of D. In DiTT, functors are postulated as term-level functions:

```ditt
postulate
  C : Cat
  D : Cat
  F : (x : C) → D
```

The *functorial action on morphisms* --- mapping a morphism `f : a →[C] b` to `F a →[D] F b` --- is derived using J. The diagonal witness `λz. refl (F z)` says: when source and target coincide at z, F maps the identity to the identity. J extends this along any morphism:

```ditt
map_F (a : C^) (b : C) (f : a →[C] b) : F a →[D] F b =
  J (λz. refl (F z)) [f]
```

The functorial laws follow from J's computation rule:

```ditt
// Identity law: map_F (refl a) reduces to refl (F a)
map_id (a : C) : F a →[D] F a =
  map_F a a (refl a)

// Composition law: map_F applied to a composite
// reduces to the composite of the mapped morphisms
map_compose (a : C^) (b : C) (c : C)
  (f : a →[C] b) (g : b →[C] c) : F a →[D] F c =
  compose_D (F a) (F b) (F c) (map_F a b f) (map_F b c g)
```

This pattern --- `J (λz. refl (F z)) [f]` --- is the universal way to lift morphisms through any covariant construction. It appears throughout the standard library whenever a functor needs to act on morphisms.

**Stdlib module:** `Std.Functor` (defines `map_F`, `map_id`, `map_compose`)
**Paper reference:** Example 3.2.


## 6. Predicates and Transport

A predicate in DiTT is a type-valued assignment: for each object `x : C`, a proposition `P x`. Formally, `P : (x : C) → Prop` is a *copresheaf* --- a covariant functor from C to the universe of propositions.

The J eliminator can transport predicate evidence along a morphism. If you have `pa : P a` and `f : a →[C] b`, you can produce `P b`:

```ditt
module Tutorial.Transport where

postulate
  C : Cat
  P : (x : C) → Prop

// The diagonal witness is the identity on P z
// (at the diagonal, no transport is needed)
diag_transport (z : C) : P z → P z =
  λpz. pz

// Transport P along a morphism
transport_P (a : C^) (b : C) (f : a →[C] b) : P a → P b =
  J diag_transport [f]
```

The pattern: `diag_transport z` is the identity function on `P z`. When we apply `J diag_transport [f]` with `f : a →[C] b`, J extends the identity function along `f`, producing a function from `P a` to `P b`.

Verifying the computation rule: `J diag_transport [refl z]` reduces to `diag_transport z`, which is `λpz. pz` --- the identity. Transporting along the identity morphism does nothing.

Transport is the directed analogue of HoTT's `transport` along paths. The key difference: in HoTT, transport works in both directions (because paths are invertible). In DiTT, `transport_P a b f` goes from `P a` to `P b`, and there is no reverse direction unless you separately have a morphism from `b` to `a`.

**Stdlib module:** `Std.Yoneda` (defines `transport_P`)
**Paper reference:** Example 3.3.


## 7. Products and Pairs

DiTT has product types at both the category level and the predicate level.

Product categories `C × D` have pairs as objects and componentwise morphisms:

```ditt
module Tutorial.Products where

postulate
  C : Cat
  D : Cat

// Swap components of a product
exchange (x : C) (y : D) : (D × C) = (y, x)

// Projections
first (p : C × D) : C = p.1
second (p : C × D) : D = p.2

// Morphisms in a product category are pairs of morphisms
congruence (a : C) (a2 : C) (b : D) (b2 : D)
  (u : a →[C] a2) (v : b →[D] b2) :
  (a, b) →[(C × D)] (a2, b2) =
  (u, v)
```

Tuples are written `(a, b)`, and projections are `.1` and `.2`. The projections bind tighter than application: `f p.1` parses as `f (p.1)`, not `(f p).1`.

At the predicate level, `A × B` is conjunction/product: a term of type `A × B` is a pair `(a, b)` where `a : A` and `b : B`.

**Paper reference:** Figure 9 (conjunction/product in the predicate grammar), Example 3.4.


## 8. Ends --- Universal Quantification

The *end* is the directed analogue of universal quantification. Written `∫ (x : C). P x`, it asserts: for every object `x` of `C`, the predicate `P x` holds, and this holding is coherent across all morphisms.

The variable `x` must appear *dinaturally* in `P` --- that is, in both covariant and contravariant positions. This coherence condition is what distinguishes an end from a plain universal quantifier.

```ditt
module Tutorial.Ends where

postulate
  C : Cat
  D : Cat
  F : (x : C) → D
  G : (x : C) → D

// Natural transformation type: an ∫ over hom
nat_trans : Prop = ∫ (x : C). (F x →[D] G x)

// Identity natural transformation
nat_id : ∫ (x : C). (F x →[D] F x) = λx. refl (F x)
```

An element of `∫ (x : C). P x` is introduced by providing a family: `λx. ...` where the body has type `P x` for each `x`. The variable `x` is bound by the end.

End elimination extracts a component at a specific object. Given `alpha : ∫ (x : C). P x` and `a : C`, you write `alpha a` to get `P a`. This is function application --- the end-quantified family is applied to the object.

The definition of `nat_trans` illustrates the central role of ends: a natural transformation from `F` to `G` is a family of morphisms `F x →[D] G x`, indexed over all `x : C`, satisfying a coherence condition. The end captures exactly this.

**Paper reference:** Definition 4.8 (ends), Figure 16 (end introduction and elimination rules), Example 3.5 (natural transformations).


## 9. Natural Transformations

Natural transformations are the morphisms between functors. In DiTT, they are characterized as ends:

```
nat_trans : Prop = ∫ (x : C). (F x →[D] G x)
```

This says: a natural transformation from F to G is a family of D-morphisms, one at each C-object, that is coherent (natural) in x.

**Vertical composition** composes natural transformations pointwise:

```ditt
nat_comp (eta : ∫ (x : C). (F x →[D] G x))
         (eps : ∫ (x : C). (G x →[D] H x))
       : ∫ (x : C). (F x →[D] H x) =
  λx. compose_D (F x) (G x) (H x) (eta x) (eps x)
```

**Whiskering** precomposes or postcomposes with a functor:

```ditt
// Precomposition: given K : E → C, produce Nat(F.K, G.K)
whisker_left (eta : ∫ (x : C). (F x →[D] G x))
  : ∫ (e : E). (F (K e) →[D] G (K e)) =
  λe. eta (K e)

// Postcomposition: given L : D → E2, produce Nat(L.F, L.G)
whisker_right (eta : ∫ (x : C). (F x →[D] G x))
  : ∫ (x : C). (L (F x) →[E2] L (G x)) =
  λx. map_L (F x) (G x) (eta x)
```

**Horizontal composition** (the Godement product) composes across two layers of functors. Given `alpha : Nat(F, G)` and `beta : Nat(L, M)` where L, M : D → E2, the composite `beta . alpha` has components `beta_{G x} . L(alpha_x)`:

```ditt
horizontal_comp (alpha : ∫ (x : C). (F x →[D] G x))
                (beta : ∫ (y : D). (L y →[E2] M y))
              : ∫ (x : C). (L (F x) →[E2] M (G x)) =
  λx. compose_E2 (L (F x)) (L (G x)) (M (G x))
    (map_L (F x) (G x) (alpha x)) (beta (G x))
```

The **polymorphic identity** is the canonical element of `∫ (x : C). (x →[C] x)`. The end quantifier enforces dinaturality, which is the directed analog of parametricity: any element must be the identity family.

```ditt
poly_id : ∫ (x : C). (x →[C] x) = λx. refl x
```

**Dinatural transformations** generalize natural transformations. For dipresheaves P, Q : C^op × C → Prop, a dinatural transformation is:

```ditt
dinat : Prop = ∫ (x : C). (PD x x → QD x x)
```

**Stdlib module:** `Std.NatTrans` (defines all of the above)
**Paper reference:** Example 3.5, Appendix B.4, Theorem D.4.


## 10. Coends --- Existential Quantification

The *coend* is the directed analogue of existential quantification. Written `∫^ (x : C). P x`, it asserts: there exists some `x` in `C` for which `P x` holds, subject to coherence.

Coend introduction packages a witness:

```ditt
module Tutorial.Coends where

postulate C : Cat

// For every x, there exists y with a morphism x → y.
// Witness: y = x, morphism = refl x.
singleton : ∫ (x : C). ∫^ (y : C). (x →[C] y) =
  λx. ∫^ (λy. refl x)
```

This is Example 3.6 from the paper. The outer `end` says "for all x" and the inner `coend` says "there exists y". The witness is `y = x` with `refl x : x →[C] x`.

Coend introduction uses `∫^ (λy. witness)` where the lambda binds the existential variable.

Coend elimination works differently from what you might expect. It is not pattern matching. Instead, it uses an *adjoint form*: the coend elimination operator works on the propositional context. This adjoint form is a consequence of the paper's design: unrestricted coend elimination would break dinaturality. The restricted form preserves the coherence guarantees that make the theory consistent. Derived rules in Appendix C recover more natural elimination patterns for specific situations (coend introduction from existential witnesses, single-point introduction, and natural-deduction-style elimination).

**Stdlib module:** `Std.EndCoend` (defines `singleton`, `end_to_coend`, and structural laws)
**Paper reference:** Definition 4.8 (coends), Figures 11 and 16 (coend introduction and elimination rules), Example 3.6, Appendix C (derived rules).


## 11. The Yoneda Lemma

The Yoneda lemma is the central theorem of the (co)end calculus. In DiTT, it states:

> For a copresheaf `P : (x : C) → Prop` and an object `a : C`, there is an isomorphism between `P a` and `∫ (x : C). ((a →[C] x) → P x)`.

The forward direction: given evidence `pa : P a`, construct a natural family that, for each `x`, takes a morphism `f : a →[C] x` and transports `pa` along `f`.

The backward direction: given a natural family `alpha`, instantiate it at `a` with the identity morphism `refl a`.

```ditt
module Tutorial.Yoneda where

postulate
  C : Cat
  P : (x : C) → Prop

transport_P (a : C^) (b : C) (f : a →[C] b) : P a → P b =
  J (λz. λp. p) [f]

// Forward: P a → ∫ (x : C). ((a →[C] x) → P x)
yoneda_forward (a : C) (pa : P a) : ∫ (x : C). ((a →[C] x) → P x) =
  λx. λf. transport_P a x f pa

// Backward: ∫ (x : C). ((a →[C] x) → P x) → P a
yoneda_backward (a : C) (alpha : ∫ (x : C). ((a →[C] x) → P x)) : P a =
  alpha a (refl a)
```

The round-trip `yoneda_backward a (yoneda_forward a pa)` reduces as follows:

1. `yoneda_forward a pa` = `λx. λf. transport_P a x f pa`
2. Applying `yoneda_backward`: `(λx. λf. transport_P a x f pa) a (refl a)`
3. Substituting: `transport_P a a (refl a) pa`
4. `transport_P a a (refl a)` = `J (λz. λp. p) [refl a]`
5. By J-computation: `J (λz. λp. p) [refl a]` = `(λz. λp. p) a` = `λp. p`
6. Applying to `pa`: `(λp. p) pa` = `pa`

Both round-trips are expressible:

```ditt
// Round-trip 1: backward (forward pa) = pa
yoneda_roundtrip (a : C) (pa : P a) : P a =
  yoneda_backward a (yoneda_forward a pa)

// Round-trip 2: forward (backward alpha) = alpha
yoneda_roundtrip_2 (a : C)
  (alpha : ∫ (x : C). ((a →[C] x) → P x))
  : ∫ (x : C). ((a →[C] x) → P x) =
  yoneda_forward a (yoneda_backward a alpha)
```

### The Yoneda Embedding

The *Yoneda embedding* maps each object `a` to the representable copresheaf `yo(a)(x) = x →[C] a`:

```ditt
yo (a : C) (x : C) : Prop = x →[C] a
```

The Yoneda embedding is *fully faithful*: natural transformations `yo(a) => yo(b)` correspond bijectively to morphisms `a →[C] b`. The forward direction post-composes with `f`:

```ditt
yoneda_ff_forward (a : C) (b : C) (f : a →[C] b)
  : ∫ (x : C). ((x →[C] a) → (x →[C] b)) =
  λx. λg. compose_C x a b g f

yoneda_ff_backward (a : C) (b : C)
  (alpha : ∫ (x : C). ((x →[C] a) → (x →[C] b)))
  : a →[C] b =
  alpha a (refl a)
```

The Yoneda lemma is the primary tool for proving isomorphisms in DiTT. Because the theory lacks a propositional equality type for morphisms (see Section 22), the Yoneda technique --- instantiating at a generic copresheaf and constructing natural isomorphisms --- is the standard method for establishing that two constructions are equivalent.

**Stdlib module:** `Std.Yoneda` (defines transport, both Yoneda directions, both round-trips, the embedding, and full faithfulness)
**Paper reference:** Example 6.1, Appendix G.


## 12. Structural Laws for Ends and Coends

The standard library provides a collection of structural laws governing how ends and coends interact with other connectives.

### End preserves products

The end of a product is isomorphic to the product of ends:

```ditt
// Forward: split a product-valued ∫ into a pair of ends
end_preserves_prod_left
  (alpha : ∫ (x : C). (P x × Q x))
  : (∫ (x : C). P x) × (∫ (x : C). Q x) =
  (λx. (alpha x).1, λx. (alpha x).2)

// Backward: combine a pair of ends into a product-valued ∫
end_preserves_prod_right
  (pair : (∫ (x : C). P x) × (∫ (x : C). Q x))
  : ∫ (x : C). (P x × Q x) =
  λx. (pair.1 x, pair.2 x)
```

### End preserves implication

When the hypothesis is constant (does not depend on the end variable), implication commutes with ends:

```ditt
// (K → ∫ (x). P x) → ∫ (x). (K → P x)
end_preserves_impl_fwd
  (f : K → ∫ (x : C). P x) : ∫ (x : C). (K → P x) =
  λx. λk. f k x

// ∫ (x). (K → P x) → (K → ∫ (x). P x)
end_preserves_impl_bwd
  (g : ∫ (x : C). (K → P x)) : K → ∫ (x : C). P x =
  λk. λx. g x k
```

### Fubini for ends

Nested ends can be exchanged (Paper Example 6.4):

```ditt
fubini_left
  (alpha : ∫ (x : C). ∫ (y : D). S x y)
  : ∫ (y : D). ∫ (x : C). S x y =
  λy. λx. alpha x y

fubini_right
  (beta : ∫ (y : D). ∫ (x : C). S x y)
  : ∫ (x : C). ∫ (y : D). S x y =
  λx. λy. beta y x
```

### Currying for ends

Product arguments in end bodies can be curried and uncurried:

```ditt
curry_end (f : ∫ (x : C). ((P x × Q x) → T x))
  : ∫ (x : C). (P x → Q x → T x) =
  λx. λpx. λqx. f x (px, qx)

uncurry_end (g : ∫ (x : C). (P x → Q x → T x))
  : ∫ (x : C). ((P x × Q x) → T x) =
  λx. λpair. g x pair.1 pair.2
```

### Canonical map from ends to coends

A universally quantified family immediately provides an existential witness:

```ditt
end_to_coend (alpha : ∫ (x : C). R x x)
  : ∫^ (x : C). R x x =
  ∫^ (λx. alpha x)
```

**Stdlib module:** `Std.EndCoend` (defines all of the above)
**Paper reference:** Examples 3.6, 6.4, 6.5.


## 13. Kan Extensions

Kan extensions are the fundamental universal constructions of category theory. In DiTT, they are expressed using the pointwise end/coend formulas.

Given a functor `F : C → D` and a copresheaf `P : (x : C) → Prop`:

**Right Kan extension** (the "best approximation from the right"):

```ditt
ran (y : D) : Prop =
  ∫ (x : C). ((y →[D] F x) → P x)
```

For each `y : D`, `ran y` collects all the ways that `y` maps into the image of `F`, weighted by `P`.

**Left Kan extension** (the "best approximation from the left"):

```ditt
lan (y : D) : Prop =
  ∫^ (x : C). ((F x →[D] y) × P x)
```

For each `y : D`, `lan y` collects all the ways that the image of `F` maps into `y`, paired with evidence from `P`.

Both come with unit and counit maps:

```ditt
// Unit of Ran: P x → Ran_F P (F x)
ran_unit (x : C) (px : P x) : ran (F x) =
  λz. λf. (J (λw. λpw. pw) [f]) px

// Counit of Ran: Ran_F P (F x) → P x
ran_counit (x : C) (phi : ran (F x)) : P x =
  phi x (refl (F x))

// Unit of Lan: P x → Lan_F P (F x)
lan_unit (x : C) (px : P x) : lan (F x) =
  ∫^ (λz. (refl (F x), px))
```

The Ran unit uses transport (the J pattern from Section 6). The Ran counit instantiates the end at `z = x` with the identity morphism --- the Yoneda evaluation trick. The Lan unit packages the identity morphism with the evidence into a coend witness.

**Stdlib module:** `Std.KanExtension` (defines `ran`, `lan`, `ran_unit`, `ran_counit`, `lan_unit`)
**Paper reference:** Example 6.3 (Ran), Example D.1 (Lan).


## 14. Adjunctions

An adjunction between functors `F : C → D` and `G : D → C` is a natural isomorphism between hom-sets:

```
hom_D(F a, b) ~ hom_C(a, G b)
```

In DiTT, this is expressed as a pair of postulated natural transformations:

```ditt
postulate
  adjoint_forward : ∫ (a : C). ∫ (b : D). ((F a →[D] b) → (a →[C] G b))
  adjoint_backward : ∫ (a : C). ∫ (b : D). ((a →[C] G b) → (F a →[D] b))
```

The bundled type packages both directions:

```ditt
adjunction_iso : Prop =
  ∫ (a : C). ∫ (b : D).
    (((F a →[D] b) → (a →[C] G b)) × ((a →[C] G b) → (F a →[D] b)))
```

The **unit** and **counit** are derived by instantiating at identity morphisms --- the same Yoneda trick used throughout DiTT:

```ditt
// Unit: eta_a : a →[C] G(F a)
// Instantiate adjoint_forward at b = F a with refl (F a)
unit (a : C) : a →[C] G (F a) =
  adjoint_forward a (F a) (refl (F a))

// Counit: epsilon_b : F(G b) →[D] b
// Instantiate adjoint_backward at a = G b with refl (G b)
counit (b : D) : F (G b) →[D] b =
  adjoint_backward (G b) b (refl (G b))
```

The **triangle identities** state that certain composites equal the identity. DiTT can construct these composites explicitly:

```ditt
// epsilon_{Fx} . F(eta_x) : F x →[D] F x
triangle1_composite (x : C) : F x →[D] F x =
  compose_D (F x) (F (G (F x))) (F x)
    (map_F x (G (F x)) (unit x)) (counit (F x))

// G(epsilon_y) . eta_{Gy} : G y →[C] G y
triangle2_composite (y : D) : G y →[C] G y =
  compose_C (G y) (G (F (G y))) (G y)
    (unit (G y)) (map_G (F (G y)) y (counit y))
```

By the triangle identities, both composites equal the identity. The type checker verifies this judgmentally (both have the same type as `refl`).

**Stdlib module:** `Std.Adjunction` (defines all of the above)
**Paper reference:** Section on adjunctions in the paper, with unit/counit derived from hom-iso by Yoneda.


## 15. Profunctors

A *profunctor* P : B --/--> C is a dipresheaf `P : B^op x C → Set`, written in DiTT as `P : (b : B) → (c : C) → Prop`.

The **hom profunctor** is the simplest example:

```ditt
hom_profunctor (a : C) (b : C) : Prop = a →[C] b
```

**Profunctor composition** uses a coend over the intermediate category:

```ditt
// (Q . P)(b, d) = ∫^ (c : C). P(b, c) × Q(c, d)
prof_compose (b : B) (d : D) : Prop =
  ∫^ (c : C). (P b c × Q c d)
```

The hom profunctor is the identity for composition:

```ditt
prof_id_witness (c : C) (c2 : C) (p : c →[C] c2)
  : ∫^ (z : C). ((c →[C] z) × (z →[C] c2)) =
  ∫^ (λz. (refl c, p))
```

**Representable profunctors** are induced by functors:

```ditt
// RepF(b, c) = hom_C(F b, c) for F : B → C
repr_profunctor (b : B) (c : C) : Prop = F b →[C] c
```

**Right lifts** in the profunctor bicategory:

```ditt
// (Rift_P Q)(b, d) = ∫ (c : C). (P(b, c) → Q(c, d))
rift (b : B) (d : D) : Prop = ∫ (c : C). (P b c → Q c d)
```

**Natural transformations between profunctors:**

```ditt
nat_prof : Prop = ∫ (b : B). ∫ (c : C). (P b c → P2 b c)
```

**Stdlib module:** `Std.Profunctor` (defines all of the above)
**Paper reference:** Definition D.3, Example D.2.


## 16. Limits and Colimits

Limits and colimits are expressed as ends over hom types.

Given a diagram `F : I → C` (a functor from an index category I to C):

**A limit cone** over F with apex c is a compatible family of morphisms from c to each F i:

```ditt
limit_cone (c : C) : Prop = ∫ (i : I). (c →[C] F i)
```

**A colimit cocone** over F with apex c is a compatible family of morphisms from each F i to c:

```ditt
colimit_cocone (c : C) : Prop = ∫ (i : I). (F i →[C] c)
```

The **universal property** of a limit states that the limit object L represents the cone functor. Both directions of the isomorphism, natural in c:

```ditt
limit_property : Prop =
  ∫ (c : C). (((c →[C] L) → limit_cone c) × (limit_cone c → (c →[C] L)))
```

**Weighted (co)limits** generalize ordinary (co)limits by allowing a weight functor `W : I → Prop`:

```ditt
// Weighted limit: {W, F} = ∫ (i : I). (W i → P i)
weighted_limit : Prop = ∫ (i : I). (W i → P i)

// Weighted colimit: W × F = ∫^ (i : I). (W i × P i)
weighted_colimit : Prop = ∫^ (i : I). (W i × P i)
```

Ordinary limits are the special case where W is the constant presheaf at the terminal object.

**Stdlib module:** `Std.Limit` (defines `limit_cone`, `colimit_cocone`, `limit_property`, `colimit_property`, `weighted_limit`, `weighted_colimit`)
**Paper reference:** Limits/colimits as ends/coends is a classical result; weighted (co)limits follow the standard formula.


## 17. The Codensity Monad

The codensity construction at the predicate level is the right Kan extension of a copresheaf along the identity functor:

```ditt
codensity (a : C) : Prop =
  ∫ (x : C). ((a →[C] x) → P x)
```

By the Yoneda lemma, `codensity a` is isomorphic to `P a`. The unit, counit, and join witness this:

```ditt
// Unit: P a → T(a)  (the Yoneda forward direction)
codensity_unit (a : C) (pa : P a) : codensity a =
  λx. λf. (J (λz. λp. p) [f]) pa

// Counit: T(a) → P a  (instantiate at refl)
codensity_counit (a : C) (alpha : codensity a) : P a =
  alpha a (refl a)

// Join: T(T(a)) → T(a)  (unpack twice via Yoneda)
codensity_join (a : C)
  (alpha : ∫ (x : C). ((a →[C] x) → ∫ (y : C). ((x →[C] y) → P y)))
  : codensity a =
  λy. λg. (alpha a (refl a)) y g
```

Note: this is the *predicate-level* codensity monad (`Ran_Id P`). The classical object-level codensity monad of a functor F : C → D (which produces a D-object, not a proposition) is not expressible due to the term/predicate separation in DiTT.

**Stdlib module:** `Std.Codensity` (defines `codensity`, `codensity_unit`, `codensity_counit`, `codensity_join`)
**Paper reference:** This construction follows from Example 6.3 (right Kan extension) specialized to the identity functor.


## 18. Presheaf Constructions

The presheaf category supports exponentials and Day convolution.

### Presheaf exponential

The internal hom (exponential) in the category of copresheaves on C:

```ditt
// (A => B)(x) = ∫ (y : C). ((x →[C] y) × A y → B y)
presheaf_exp (x : C) : Prop =
  ∫ (y : C). (((x →[C] y) × A y) → B y)
```

The **evaluation map** applies the exponential:

```ditt
presheaf_eval (x : C) (phi : presheaf_exp x) (ax : A x) : B x =
  phi x (refl x, ax)
```

**Currying** transposes a morphism into the exponential:

```ditt
presheaf_curry
  (h : ∫ (x : C). ((A x × Z x) → B x))
  (x : C) (zx : Z x) : presheaf_exp x =
  λy. λpair. h y
    ((J (λw. λaw. aw) [pair.1]) (pair.2),
     (J (λw. λzw. zw) [pair.1]) zx)
```

### Day convolution

For copresheaves on a monoidal category (with postulated `tensor` and unit `I_C`):

```ditt
// (A × B)(c) = ∫^ (a). ∫^ (b). (tensor a b →[C] c) × A a × B b
day_conv (c : C) : Prop =
  ∫^ (a : C). ∫^ (b : C). ((tensor a b →[C] c) × A a × B b)

// Unit: the representable copresheaf at the monoidal unit
day_unit (c : C) : Prop = I_C →[C] c
```

**Stdlib module:** `Std.Presheaf` (defines `presheaf_exp`, `presheaf_eval`, `presheaf_curry`, `day_conv`, `day_unit`)
**Paper reference:** Example 6.2 (presheaf exponential).


## 19. Monads and Comonads

DiTT can express the *structure types* of monads and comonads, though the equational *laws* (associativity, unit laws) are verified judgmentally rather than stated as internal propositions.

Given an endofunctor `T : C → C`:

```ditt
// Monad unit type: eta : Id => T
monad_unit_type : Prop = ∫ (x : C). (x →[C] T x)

// Monad multiplication type: mu : T.T => T
monad_mult_type : Prop = ∫ (x : C). (T (T x) →[C] T x)

// Functorial action of T on morphisms
map_T (a : C^) (b : C) (f : a →[C] b) : T a →[C] T b =
  J (λz. refl (T z)) [f]
```

**T-algebras** and **free algebras**:

```ditt
// A T-algebra at object a
algebra (a : C) : Prop = T a →[C] a

// Free algebra from multiplication
free_algebra (mu : monad_mult_type) (a : C) : T (T a) →[C] T a =
  mu a
```

**Comonad structure** is dual:

```ditt
comonad_counit_type : Prop = ∫ (x : C). (W x →[C] x)
comonad_comult_type : Prop = ∫ (x : C). (W x →[C] W (W x))
coalgebra (a : C) : Prop = a →[C] W a
```

### Monad from adjunction

Given an adjunction `F -| G` with counit `epsilon`, the monad multiplication on `T = G.F` is:

```ditt
// mu_x = G(epsilon_{Fx}) : G(F(G(F x))) →[C] G(F x)
adjunction_mult : ∫ (x : C). (G (F (G (F x))) →[C] G (F x)) =
  λx. map_G (F (G (F x))) (F x) (epsilon (F x))
```

This constructs the monad multiplication by applying G's functorial action to the counit component at `F x`.

**Stdlib module:** `Std.Monad` (defines all of the above)
**Paper reference:** Structure-without-laws pattern; monad multiplication from adjunction.


## 20. V-Enriched Categories

DiTT can express the structure of categories enriched over a monoidal category V. This is notable because enriched category theory is typically considered a sophisticated extension of ordinary category theory.

Given a monoidal category `(V, tensor, I_V)` and a category `C`, a V-enriched structure on C consists of:

```ditt
postulate
  V : Cat
  tensor : (x : V) → (y : V) → V
  I_V : V
  C : Cat
  // For each pair of C-objects, an object of V
  hom_V : (a : C) → (b : C) → V
  // Composition: tensor(hom(b,c), hom(a,b)) →[V] hom(a,c)
  comp_V : (a : C) → (b : C) → (c : C)
    → (tensor (hom_V b c) (hom_V a b)) →[V] (hom_V a c)
  // Identity: I_V →[V] hom(a,a)
  id_V : (a : C) → I_V →[V] (hom_V a a)
```

A **V-functor** acts on hom-objects:

```ditt
// hom_C(a, b) →[V] hom_D(F a, F b) for all a, b
v_functor_action : Prop =
  ∫ (a : C). ∫ (b : C). (hom_V a b →[V] hom_V_D (F_obj a) (F_obj b))
```

A **V-natural transformation** is a family of V-morphisms from the monoidal unit:

```ditt
// I_V →[V] hom_D(F a, G a) for all a
v_nat_trans : Prop =
  ∫ (a : C). (I_V →[V] hom_V_D (F_obj a) (G_obj a))
```

**Stdlib module:** `Std.Enriched` (defines `v_functor_action`, `v_nat_trans`)
**Paper reference:** V-enriched categories are expressible because enriched homs are V-objects and composition/identity are V-morphisms.


## 21. Impredicative Encodings

DiTT supports Church-style encodings for data types, using the *shared-parameter idiom*: all types are parameterized by the same category C and copresheaf P, and they interoperate freely because they share these parameters.

### Church booleans

```ditt
BoolCP : Prop = ∫ (x : C). (P x → P x → P x)

trueCP  : BoolCP = λx. λa. λb. a
falseCP : BoolCP = λx. λa. λb. b
```

Boolean operations work as expected:

```ditt
andCP (a : BoolCP) (b : BoolCP) : BoolCP =
  λx. λp. λq. ifCP a x (ifCP b x p q) q

orCP (a : BoolCP) (b : BoolCP) : BoolCP =
  λx. λp. λq. ifCP a x p (ifCP b x p q)

notCP (b : BoolCP) : BoolCP =
  λx. λp. λq. ifCP b x q p
```

### Church naturals

```ditt
NatCP : Prop = ∫ (x : C). (P x → (P x → P x) → P x)

zero : NatCP = λx. λz. λs. z
succ (n : NatCP) : NatCP = λx. λz. λs. s (n x z s)

add (m : NatCP) (n : NatCP) : NatCP =
  λx. λz. λs. m x (n x z s) s

mult (m : NatCP) (n : NatCP) : NatCP =
  λx. λz. λs. m x z (λacc. n x acc s)
```

### Cross-type operations

Because BoolCP and NatCP share the same (C, P) parameters, operations between them work:

```ditt
isZero (n : NatCP) : BoolCP =
  λx. λt. λf. n x t (λp. f)

boolToNat (b : BoolCP) : NatCP =
  λx. λz. λs. b x (s z) z

ifNat (cond : BoolCP) (then_n : NatCP) (else_n : NatCP) : NatCP =
  λx. λz. λs. cond x (then_n x z s) (else_n x z s)
```

### Church lists and option types

With an additional type parameter `A : (x : C) → Prop`:

```ditt
ListAP : Prop = ∫ (x : C). (P x → (A x → P x → P x) → P x)

nil : ListAP = λx. λz. λf. z
cons (head : ∫ (x : C). A x) (tail : ListAP) : ListAP =
  λx. λz. λf. f (head x) (tail x z f)

append (xs : ListAP) (ys : ListAP) : ListAP =
  λx. λz. λf. xs x (ys x z f) f

MaybeAP : Prop = ∫ (x : C). (P x → (A x → P x) → P x)

nothingAP : MaybeAP = λx. λz. λf. z
justAP (a : ∫ (x : C). A x) : MaybeAP =
  λx. λz. λf. f (a x)
```

### Limitations of impredicative encodings

Ends quantify over category objects, not over predicates. This means:

- **Predecessor** on Church naturals is not expressible (requires instantiating at a different predicate internally).
- **Exponentiation** is not expressible (same reason).
- **Map over Church lists** is not expressible (would need to change the element type, requiring a different predicate).

The fully polymorphic System F form `(P : Prop) → P → P → P` (quantifying over predicates) is not available in DiTT. What works is the shared-parameter idiom: all types that share the same (C, P) can interoperate freely.

**Stdlib module:** `Std.ChurchEncoding` (defines BoolCP, NatCP, ListAP, MaybeAP, and all their operations)
**Paper reference:** Section 7 (impredicative encodings and their limitations).


## 22. What You Cannot Do

DiTT is a precise and principled theory, and its boundaries are clearly defined. Understanding what the theory does *not* express is as important as understanding what it does.

**No propositional morphism equality.** There is no predicate form for "morphism `f` equals morphism `g`." Equational reasoning about morphisms (such as associativity of composition or functoriality laws) is handled judgmentally by the type checker, not by constructing proof terms. You cannot state or prove within DiTT that two morphisms are equal --- you can only rely on the type checker recognizing judgmental equalities. This is why monad laws, functor laws, naturality squares, and triangle identities cannot be stated as internal propositions --- they can only be verified by the normalizer. (Paper: Figures 8/11, Theorem 5.2.)

**No symmetry of directed equality.** Having `f : a →[C] b` does not provide any way to construct a term of type `b →[C] a`. This is the core design feature of the theory --- the "Di-" in DiTT stands for "Directed." Non-symmetry is proven to be non-admissible in Theorem 5.2.

**First-order categories only.** DiTT is first-order. Categories are base sorts in a fixed signature introduced by postulates. You cannot quantify over categories, construct new categories internally, or pass categories as arguments to functions. (Paper: Figure 7, Section 1.1.)

**No quantification over predicates.** You cannot write a function that takes a predicate `P` as an argument. Predicates are fixed syntactic forms, not first-class values. This limits impredicative encodings: Church booleans/naturals/lists work for a fixed (C, P) via the shared-parameter idiom, but the fully polymorphic System F form is not available. (Paper: Figure 9, Section 7.)

**Adjoint-form coend elimination.** Coends cannot be eliminated by pattern matching. The elimination operator works on the propositional context in adjoint form. Derived rules (Appendix C) partially recover more natural elimination patterns: coend introduction from existential witnesses (C.1), single-point introduction (C.2), and natural-deduction-style elimination (Example 3.10). (Paper: Figure 11, Theorem 5.3.)

**Dinaturals do not compose in general.** Two dinatural transformations cannot always be composed. The unrestricted cut rule is not admissible. However, *restricted cuts* --- composing a natural transformation with a dinatural one --- do work and cover the practical cases. (Paper: Theorem 5.3.)

**No coproducts or disjunction.** The predicate grammar includes Top (unit), conjunction (products), implication (arrows), hom types, ends, and coends. There is no disjunction or coproduct type. Individual cases that would use disjunction can sometimes be handled via separate constructions or by encoding choices through other means, but the connective itself is absent. (Paper: Figure 9.)

**No recursion, induction, or initial algebras.** The type theory has no fixpoint operator, no inductive types, and no way to state initiality of an algebra. F-algebra types like `T a →[C] a` are expressible (see Section 19), but catamorphisms (unique algebra morphisms from an initial algebra) cannot be constructed because initiality requires second-order quantification over algebras. (Paper: Figure 9.)

**Term/predicate separation.** Terms are functors (object-level); predicates/entailments are (di)natural transformations (proposition-level). Constructions that need to "return an object" (like the classical codensity monad of a functor, or initial algebras as objects) are not expressible --- only predicate-level analogs work. (Paper: Figures 8-9, Section 1.1 item 2.)

For the complete analysis of all capabilities and limitations with paper citations and workarounds, see `docs/THEORY_CAPABILITIES.md`.
