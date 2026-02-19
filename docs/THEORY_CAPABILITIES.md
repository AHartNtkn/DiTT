# Theory Capabilities and Limitations

Reference: Andrea Laretto, Fosco Loregian, Niccolo Veltri, "Di- is for Directed: First-Order Directed Type Theory via Dinaturality" (POPL 2026).

## What DiTT Expresses

1. **Morphism composition and identity** --- The directed J eliminator composes morphisms: `compose a b c f g = (J (\z. diag_comp c z) [f]) g`, where the motive uses a diagonal witness. Identity is `refl x`. Paper: Figure 11 (J rule), Example 3.1.

2. **Functorial action on morphisms** --- `map_F a b f = J (\z. refl (F z)) [f]` lifts a morphism through a covariant functor. Paper: Example 3.2.

3. **Transport of predicates** --- `J (\z. \p. p) [f]` transports predicate evidence along a morphism. Paper: Example 3.3.

4. **Natural transformations as ends** --- `Nat(F, G) = end (x : C). (F x ->[D] G x)`. Includes vertical composition (`nat_comp`), horizontal composition (Godement product), and both whiskering directions. Paper: Example 3.5, Appendix B.4, Theorem D.4.

5. **Yoneda lemma (both directions and round-trips)** --- Forward: `\x. \f. transport_P a x f pa`. Backward: `alpha a (refl a)`. Both round-trips are expressible. The Yoneda embedding `yo(a)(x) = x ->[C] a` and its full faithfulness (`Nat(yo a, yo b) ~ hom(a, b)`) are provable. Paper: Example 6.1, Appendix G.

6. **Right Kan extensions (pointwise formula)** --- `(Ran_F P)(y) = end (x : C). ((y ->[D] F x) -> P x)` with unit and counit. Paper: Example 6.3.

7. **Left Kan extensions (pointwise formula)** --- `(Lan_F P)(y) = coend (x : C). ((F x ->[D] y) * P x)` with unit via coend intro. Paper: Example D.1.

8. **Adjunctions (hom-iso, unit/counit, triangle identities)** --- Stated as `end (a : C). end (b : D). ((F a ->[D] b) -> (a ->[C] G b))`. Unit and counit derived by instantiating at refl. Triangle identity composites `epsilon_{Fx} . F(eta_x)` and `G(epsilon_y) . eta_{Gy}` are constructible (these should equal identity by the triangle identities, verified judgmentally by the normalizer).

9. **Profunctor composition and related constructions** --- `(Q . P)(a, c) = coend (b : B). (P a b * Q b c)`. Also expressible: representable profunctors, right lifts `Rift_P(Q)(b, d) = end (c : C). (P b c -> Q c d)`, and natural transformations between profunctors. Paper: Definition D.3, Example D.2.

10. **Codensity monad at predicate level** --- `T(a) = end (x : C). ((a ->[C] x) -> P x)`, isomorphic to `P(a)` by Yoneda, with unit, counit, and join. Note: this is `Ran_Id P`, the predicate-level codensity monad. The classical object-level codensity monad of a functor F : C -> D (which would produce a D-object, not a Prop) is not expressible due to the term/predicate separation (L10).

11. **Presheaf exponential** --- `(A => B)(x) = end (y : C). ((x ->[C] y) * A y -> B y)` with evaluation and currying maps. Paper: Example 6.2.

12. **Day convolution** --- `(A * B)(c) = coend (a : C). coend (b : C). ((tensor a b ->[C] c) * A a * B b)` for a postulated monoidal structure, with unit presheaf `I_C ->[C] c`.

13. **Fubini for ends** --- `end (x : C). end (y : D). P x y <-> end (y : D). end (x : C). P x y`. Paper: Example 6.4.

14. **End/coend structural laws** --- End preserves products (both directions), end preserves implication when the hypothesis is constant (`(K -> end x. P x) <-> end x. (K -> P x)`, Paper Example 6.5), currying for ends, singleton existence (`end (x : C). coend (y : C). (x ->[C] y)` is inhabited, Paper Example 3.6), and the canonical map from ends to coends.

15. **Limits and colimits as ends/coends** --- Limit cones `end (i : I). (c ->[C] F i)`, colimit cocones `end (i : I). (F i ->[C] c)`, and their universal properties as representability conditions. Weighted (co)limits: `{W, F} = end (i). (W i -> F i)` and `W * F = coend (i). (W i * F i)`.

16. **Opposite category hom isomorphism** --- `hom_C(x, y) -> hom_{C^op}(y, x)` and vice versa, via J with diagonal `\z. refl z`. Paper: Appendix B.5.

17. **Monad and comonad structure types** --- Monad unit type `end (x). (x ->[C] T x)`, multiplication type `end (x). (T(Tx) ->[C] Tx)`, T-algebra type `T a ->[C] a`, free algebra from multiplication; dual comonad/coalgebra types. Monad multiplication derived from adjunction counit. These express the *structure* of monads/comonads (the types and operations), though the *laws* (associativity, unit laws) can only be verified judgmentally, not stated as internal propositions (L1).

18. **Dinatural transformations as ends** --- `Dinat(P, Q) = end (x : C). (P x x -> Q x x)` for dipresheaves P, Q. Paper: Theorem D.4.

19. **Polymorphic identity and parametricity** --- `poly_id : end (x : C). (x ->[C] x) = \x. refl x`. The end quantifier enforces dinaturality, which is the directed analog of parametricity: any element of `end (x : C). (x ->[C] x)` must be the identity.

20. **V-enriched category structure** --- For a monoidal category V with `tensor` and unit `I`, V-enriched categories (with postulated hom-objects `hom_V : C -> C -> V`, composition, identity), V-functors (`end (a). end (b). (hom_V a b ->[V] hom_V_D (F a) (F b))`), and V-natural transformations (`end (a). (I ->[V] hom_V_D (F a) (G a))`) are all expressible. This is notable because enriched category theory is typically considered a sophisticated extension.

21. **Impredicative encodings (limited)** --- Church booleans, naturals, lists, and maybe/option types are expressible for a fixed predicate P and category C. Working operations include: `true`, `false`, `and`, `or`, `not`, `zero`, `succ`, `add`, `mult`, `iterate`, `nil`, `cons`, `foldr`, `append`, `nothing`, `just`, and cross-type operations like `isZero : NatCP -> BoolCP`, `boolToNat : BoolCP -> NatCP`, and `ifNat : BoolCP -> NatCP -> NatCP -> NatCP`. These all work because the types share the same parameters (C, P). The limitation: ends quantify over category objects, not over predicates, so these are not fully polymorphic System F encodings. Specifically, predecessor, exponentiation, and map over Church lists are not expressible because they would require instantiating at different predicates.

## Paper-Inherent Limitations

All limitations classified as **(P)** for paper-inherent.

- **L1: No propositional morphism equality (P)** --- Figures 8/11, Theorem 5.2. The predicate grammar has no form for "alpha = beta". Equational reasoning is judgmental only. This means monad laws, functor laws, naturality squares, and triangle identities cannot be stated as internal propositions --- they can only be verified by the normalizer.

- **L2: First-order categories (P)** --- Figure 7, Section 1.1. Categories are base sorts in a fixed signature. No quantification over categories.

- **L3: Adjoint-form coend elimination (P)** --- Figure 11, Section 1.1 item 10, Theorem 5.3. The coend rule operates on the propositional context, not as a term destructor. Derived rules (Example C.2) partially recover single-point introduction. This makes coYoneda and density comonad constructions only partially expressible.

- **L4: No coproducts/disjunction (P)** --- Figure 9. The predicate grammar has Top, conjunction, implication, hom, ends, coends. No disjunction or sum types (though "P or Q" cannot be stated, individual cases can sometimes be handled via separate constructions).

- **L5: Limited impredicative encodings (P)** --- Section 7. Church booleans/naturals/lists work for a fixed predicate and category (the "shared-parameter idiom"), but ends quantify over category objects, not over predicates or types. Predecessor, exponentiation, and map are not expressible.

- **L6: No second-order predicate quantification (P)** --- Figure 9, Section 7. Cannot write `(P : (x : C) -> Prop) -> ...`.

- **L7: Dinaturals don't compose (P)** --- Theorem 5.3. Unrestricted cut is not admissible. Restricted cuts (cut-nat, cut-din) work for natural-with-dinatural composition.

- **L8: No function extensionality (P)** --- Example 3.5 explicitly states the reverse direction (from end-family to functor-category morphism) is not derivable.

- **L9: No internal isomorphism type (P)** --- Figure 9 grammar. The Yoneda technique (Section 6) provides a working mechanism for isomorphism proofs despite the absence of a dedicated type.

- **L10: Term/predicate separation (P)** --- Figures 8-9, Section 1.1 item 2. Terms are functors (object-level); predicates/entailments are (di)natural transformations (proposition-level). This means constructions that need to "return an object" (like the classical codensity monad of a functor, or initial algebras) are not expressible --- only predicate-level analogs work.

- **L11: No higher categories (P)** --- Section 1.1 item 1, Section 7. The theory is 1-categorical. Higher categories mentioned as future work.

- **L12: No internal category construction (P)** --- Figure 7. Categories are introduced by signature, not constructed internally.

- **L13: No recursion, induction, or initial algebras (P)** --- The type theory has no fixpoint operator, no inductive types, and no way to state initiality of an algebra. F-algebra types `T a ->[C] a` are expressible, but catamorphisms (unique algebra morphisms from an initial algebra) cannot be constructed because initiality requires a universal property that involves quantification over algebras (which are propositions parameterized by objects, and second-order quantification over such families is not available per L6).

## Implementation Artifacts

- **Variance is inferred not declared (I)** --- The paper defines variance as a property (Figures 10, 14) but does not prescribe surface-level annotations. An implementation could accept explicit variance annotations.

## Design Features Often Mistaken for Limitations

Non-symmetry of directed equality is the central design feature, not a limitation. Theorem 5.2 proves symmetry is not admissible. The paper's title "Di- is for Directed" makes this explicit.

## Workarounds

- **Yoneda technique** (Section 6): Prove isomorphisms by assuming a generic presheaf and constructing natural isomorphisms `C(Phi, A) ~ C(Phi, B)`.

- **Restricted cut**: The cut-nat and cut-din rules allow composing naturals with dinaturals, covering all practical cases.

- **Derived coend rules** (Appendix C): Example C.1 derives coend-intro from `exists x. P(x, x)`. Example C.2 derives a coend-unit rule for single-point introduction. Example C.3 derives coend elimination into a context. Example 3.10 derives natural-deduction-style coend elimination.

- **Shared-parameter idiom**: Church-encoded data types that share the same ambient parameters (C, P) can interoperate freely. For example, `isZero : NatCP -> BoolCP` and `boolToNat : BoolCP -> NatCP` work because both types are parameterized by the same (C, P). This extends to lists, option types, and conditional expressions on naturals.

- **Structure-without-laws pattern**: Algebraic structures (monads, comonads, algebras) can have their types and operations expressed as DiTT definitions, with the equational laws verified judgmentally by the normalizer rather than stated as internal propositions. The structure is fully expressible; only the equational laws require judgmental (rather than propositional) verification.

## Future Extensions

From the paper's Section 7 roadmap:

- **Set universe with directed univalence**: Adding `hom_Set(A, B) = A => B` would internalize the Yoneda lemma.
- **Cat as a universe**: Quantification over categories via pseudo-ends in Cat.
- **Type dependency**: Full dependent directed type theory (most impactful extension).
- **Enrichment beyond Set**: While significant V-enriched structure is already expressible (V-enriched categories, V-functors, V-natural transformations), enriching the base theory itself over a category other than Set could add disjunction and other connectives.
- **Higher categories**: Geometric models for (infinity, 1)-categories.
