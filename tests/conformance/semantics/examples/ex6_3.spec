module Paper.Ex6_3 where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  Phi : (y : D) -> Prop

P (x : C) : Prop =
  Phi (F x)

phi_transport_D (a : D^) (b : D) (e : a ->[D] b) : Phi a -> Phi b =
  J (\z. \p. p) [e]

ex6_3_statement : Prop =
  (y : D) -> Phi y -> end (x : C). ((y ->[D] F x) -> P x)

ex6_3_right_kan_pointwise : ex6_3_statement =
  \y. \phi. \x. \f. (phi_transport_D y (F x) f) phi
