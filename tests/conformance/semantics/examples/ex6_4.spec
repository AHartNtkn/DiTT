module Paper.Ex6_4 where

postulate
  C : Cat
  D : Cat
  P : (x : C) -> (y : D) -> Prop
  Phi : Prop
  seed : (x : C) -> (y : D) -> Phi -> P x y

fiber_y (x : C) : Phi -> end (y : D). P x y =
  \phi. \y. seed x y phi

ex6_4_fubini_left_statement : Prop =
  Phi -> end (x : C). end (y : D). P x y

ex6_4_fubini_left : ex6_4_fubini_left_statement =
  \phi. \x. fiber_y x phi

ex6_4_fubini_right_statement : Prop =
  Phi -> end (y : D). end (x : C). P x y

ex6_4_fubini_right : ex6_4_fubini_right_statement =
  \phi. \y. \x. ex6_4_fubini_left phi x y
