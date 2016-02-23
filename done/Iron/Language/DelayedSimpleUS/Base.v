
Require Export Iron.Language.DelayedSimpleUS.Tactics.Chargueraud.
Require Export Iron.Language.DelayedSimpleUS.Tactics.Case.
Require Export Iron.Language.DelayedSimpleUS.Tactics.Rip.
Require Export Iron.Language.DelayedSimpleUS.Tactics.Nope.

Require Export Iron.Language.DelayedSimpleUS.Data.Lists.
Require Export Iron.Language.DelayedSimpleUS.Data.Subst.


(********************************************************************)
(* Override the default notation for lists to be right biased.
   We're only using lists for environments and substitutions, 
   where the right biased order is more natural. *)
Notation "xs :> x"  := (x :: xs)   (at level 61, left associativity).
Notation "xs >< ys" := (app ys xs) (at level 60, right associativity).

