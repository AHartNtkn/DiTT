module Paper.Ex3_8 where

postulate
  C : Cat
  P : (x : C) -> (y : C) -> Prop

Q (x : C) (y : C) : Prop =
  P x y

diag_dinatural (z : C) : P z z -> Q z z =
  \pzz. pzz

transport_dinaturality (a : C^) (b : C) (u : a ->[C] b) : P b a -> Q a b =
  J diag_dinatural [u]

ex3_8 : Prop =
  (a : C^) -> (b : C) -> (a ->[C] b) -> P b a -> Q a b

ex3_8_internal_dinaturality : ex3_8 =
  \a. \b. \u. \pba. (transport_dinaturality a b u) pba
