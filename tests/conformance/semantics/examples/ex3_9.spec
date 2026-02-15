module Paper.Ex3_9 where

postulate
  C : Cat
  Gamma : Cat
  P : (x : C) -> (y : C) -> Prop
  F : (g : Gamma) -> C
  lift_at_F : (g : Gamma) -> P (F g) (F g) -> (x : C) -> P x x

ex3_9_end_elim_statement : Prop =
  (g : Gamma) -> ∫ (x : C). P x x -> P (F g) (F g)

ex3_9_end_elim : ex3_9_end_elim_statement =
  \g. \alpha. (end^-1 alpha) (F g)

ex3_9_coend_intro_statement : Prop =
  (g : Gamma) -> P (F g) (F g) -> ∫^ (x : C). P x x

ex3_9_coend_intro : ex3_9_coend_intro_statement =
  \g. \k. coend (lift_at_F g k)
