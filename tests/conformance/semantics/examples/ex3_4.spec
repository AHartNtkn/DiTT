module Paper.Ex3_4 where

postulate
  C : Cat
  D : Cat

ex3_4 : Prop =
  (a : C) -> (a2 : C) -> (b : D) -> (b2 : D) ->
  (a ->[C] a2) -> (b ->[D] b2) ->
  ((a, b) ->[(C * D)] (a2, b2))

ex3_4_pair_rewrites : ex3_4 =
  \a. \a2. \b. \b2. \u. \v. (u, v)
