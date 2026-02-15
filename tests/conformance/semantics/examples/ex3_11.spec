module Paper.Ex3_11 where

postulate
  C : Cat
  P : (a : C) -> Prop
  Q : (a : C) -> Prop
  R : (a : C) -> Prop

ex3_11 : Prop =
  (a : C) -> (P a -> Q a) -> (Q a -> R a) -> (P a -> R a)

ex3_11_implication_transitivity : ex3_11 =
  \a. \pq. \qr. \pa. qr (pq pa)
