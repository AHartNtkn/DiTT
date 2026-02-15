module Paper.Ex3_1 where

postulate
  C : Cat

diag_comp (c : C) (z : C) : (z ->[C] c) -> (z ->[C] c) =
  \k. k

ex3_1 : Prop =
  (a : C^) -> (b : C) -> (c : C) -> (a ->[C] b) -> (b ->[C] c) -> (a ->[C] c)

ex3_1_compose : ex3_1 =
  \a. \b. \c. \f. \g. (J (diag_comp c) [f]) g
