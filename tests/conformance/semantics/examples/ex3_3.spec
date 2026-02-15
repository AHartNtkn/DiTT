module Paper.Ex3_3 where

postulate
  C : Cat
  P : (x : C) -> Prop
  compose_C :
    (a : C^) -> (b : C) -> (c : C) -> (a ->[C] b) -> (b ->[C] c) -> (a ->[C] c)

diag_transport (z : C) : P z -> P z =
  \pz. pz

ex3_3 : Prop =
  (a : C^) -> (b : C) -> (a ->[C] b) -> P a -> P b

ex3_3_transport : ex3_3 =
  \a. \b. \u. \pa. (J diag_transport [u]) pa

ex3_3_transport_identity (z : C) (pz : P z) : P z =
  ex3_3_transport z z (refl z) pz

ex3_3_transport_composition
  (a : C^) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) (pa : P a) :
  P c =
  ex3_3_transport a c (compose_C a b c f g) pa
