module Paper.Ex3_5 where

postulate
  C : Cat
  D : Cat
  F : C -> D
  G : C -> D

diag_eval (h : C -> D) (x : C) : (h x) ->[D] (h x) =
  refl (h x)

ex3_5 : Prop =
  (e : F ->[C -> D] G) -> end (x : C). ((F x) ->[D] (G x))

ex3_5_higher_dimensional_rewriting : ex3_5 =
  \e. \x. J (\h. diag_eval h x) [e]
