module Paper.Ex3_6 where

postulate
  C : Cat

ex3_6 : Prop =
  end (x : C). coend (y : C). (x ->[C] y)

ex3_6_coend_step (x : C) (k : coend (y : C). (x ->[C] y)) :
  coend (y : C). (x ->[C] y) =
  coend (coend^-1 k)

ex3_6_singleton_exists : ex3_6 =
  \x. coend (\y. refl x)
