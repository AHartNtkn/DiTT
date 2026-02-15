module Paper.Ex2_4 where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D

P (x : C) : Prop =
  x ->[C] x

ex2_4 : Prop =
  (x : C) -> (y : D) -> ((y ->[D] F x) -> P x)

ex2_4_derivation_predicate : ex2_4 =
  \x. \y. \u. refl x
