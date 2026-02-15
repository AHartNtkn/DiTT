module Paper.Ex6_1 where

postulate
  C : Cat
  P : (x : C) -> Prop
  Phi : (x : C) -> Prop
  phi_to_predicate_diag : (z : C) -> Phi z -> P z
  predicate_to_phi_diag : (z : C) -> P z -> Phi z
  coend_elim :
    (a : C) ->
    (coend (x : C). ((x ->[C] a) * P x)) ->
    ((x : C) -> ((x ->[C] a) * P x) -> Phi a) ->
    Phi a

phi_transport (a : C^) (x : C) (f : a ->[C] x) : Phi a -> Phi x =
  J (\z. \phi. phi) [f]

predicate_transport (x : C) (a : C) (f : x ->[C] a) : P x -> P a =
  J (\z. \p. p) [f]

ex6_1_yoneda_statement : Prop =
  (a : C) -> Phi a -> end (x : C). ((a ->[C] x) -> P x)

ex6_1_yoneda : ex6_1_yoneda_statement =
  \a. \phi. \x. \f. phi_to_predicate_diag x ((phi_transport a x f) phi)

ex6_1_coyoneda_statement : Prop =
  (a : C) -> (coend (x : C). ((x ->[C] a) * P x)) -> Phi a

ex6_1_coyoneda : ex6_1_coyoneda_statement =
  \a. \h. coend_elim a h (\x. \pair. predicate_to_phi_diag a ((predicate_transport x a pair.1) pair.2))
