module Paper.Ex6_2 where

postulate
  C : Cat
  A : (x : C) -> Prop
  Phi : (x : C) -> Prop

B (y : C) : Prop =
  (A y) * Phi y

phi_transport (a : C^) (b : C) (e : a ->[C] b) : Phi a -> Phi b =
  J (\z. \p. p) [e]

ex6_2_statement : Prop =
  (x : C) -> Phi x -> end (y : C). (((x ->[C] y) * A y) -> B y)

ex6_2_tensor_hom : ex6_2_statement =
  \x. \phi. \y. \pair. (pair.2, (phi_transport x y pair.1) phi)
