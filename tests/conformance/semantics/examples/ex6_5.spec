module Paper.Ex6_5 where

postulate
  C : Cat
  Q : Prop
  Phi : Prop

P (x : C) : Prop =
  Q

ex6_5_implication_respects_limits_left_statement : Prop =
  Phi -> (Q -> end (x : C). P x)

ex6_5_implication_respects_limits_left : ex6_5_implication_respects_limits_left_statement =
  \phi. \q. \x. q

ex6_5_implication_respects_limits_right_statement : Prop =
  Phi -> end (x : C). (P x -> Q)

ex6_5_implication_respects_limits_right : ex6_5_implication_respects_limits_right_statement =
  \phi. \x. \px. px
