module Paper.Ex3_7 where

postulate
  C : Cat
  P : (x : C) -> Prop

Q (x : C) : Prop =
  P x

diag_natural (z : C) : P z -> Q z =
  \pz. pz

transport_naturality (a : C^) (b : C) (u : a ->[C] b) : P a -> Q b =
  J diag_natural [u]

ex3_7 : Prop =
  (a : C^) -> (b : C) -> (a ->[C] b) -> P a -> Q b

ex3_7_internal_naturality : ex3_7 =
  \a. \b. \u. \pa. (transport_naturality a b u) pa
