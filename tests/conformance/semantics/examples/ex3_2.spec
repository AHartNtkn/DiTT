module Paper.Ex3_2 where

postulate
  C : Cat
  D : Cat
  F : (x : C) -> D
  compose_D :
    (a : D) -> (b : D) -> (c : D) -> (a ->[D] b) -> (b ->[D] c) -> (a ->[D] c)

diag_map (z : C) : F z ->[D] F z = refl (F z)

ex3_2 : Prop =
  (x : C) -> (y : C) -> (x ->[C] y) -> (F x ->[D] F y)

ex3_2_functorial_map : ex3_2 =
  \x. \y. \u. J diag_map [u]

ex3_2_map_identity (z : C) : F z ->[D] F z =
  ex3_2_functorial_map z z (refl z)

ex3_2_map_composition
  (a : C) (b : C) (c : C) (f : a ->[C] b) (g : b ->[C] c) :
  F a ->[D] F c =
  compose_D
    (F a)
    (F b)
    (F c)
    (ex3_2_functorial_map a b f)
    (ex3_2_functorial_map b c g)
