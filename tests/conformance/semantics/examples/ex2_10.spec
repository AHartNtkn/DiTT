module Paper.Ex2_10 where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D

ex2_10 : Prop =
  (x : C) -> (y : D) -> (y ->[D] F x)

ex2_10_opposite_predicate : ex2_10 =
  \x. \y. \u. u
