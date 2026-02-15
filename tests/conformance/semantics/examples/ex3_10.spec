module Paper.Ex3_10 where

postulate
  C : Cat
  Delta : Cat
  F : (d : Delta) -> C
  P : (x : C) -> (d : Delta) -> Prop
  intro_term_lift : (d : Delta) -> ((F d) →[C] (F d)) -> (x : C) -> (x →[C] x)

Q (d : Delta) : Prop =
  ∫^ (x : C). P x d

R (x : C^) (y : C) : Prop =
  x →[C] y

S (x : C) (d : Delta) : Prop =
  x →[C] x

diag_branch (z : C) : R z z -> R z z =
  \k. k

ex3_10_coend_elim_statement : Prop =
  (d : Delta) -> (∫^ (x : C). P x d) -> Q d

ex3_10_coend_elim : ex3_10_coend_elim_statement =
  \d. \h. coend (\z. (coend⁻¹ h) z)

ex3_10_coend_intro_term_statement : Prop =
  (d : Delta) -> S (F d) d -> ∫^ (x : C). S x d

ex3_10_coend_intro_term : ex3_10_coend_intro_term_statement =
  \d. \s. coend (intro_term_lift d s)

ex3_10_coend_intro_two_vars_statement : Prop =
  (x : C^) -> (y : C) -> R x y -> ∫^ (z : C). R z z

ex3_10_coend_intro_two_vars : ex3_10_coend_intro_two_vars_statement =
  \x. \y. \rxy. coend (\z. (J diag_branch [rxy]))
