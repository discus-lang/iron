
Require Export Iron.Language.DelayedSimple.Tactics.Chargueraud.
Require Export Iron.Language.DelayedSimple.Tactics.Case.
Require Export Iron.Language.DelayedSimple.Tactics.Rip.
Require Export Iron.Language.DelayedSimple.Tactics.Nope.

Require Export Iron.Language.DelayedSimple.Data.Lists.
Require Export Iron.Language.DelayedSimple.Data.Subst.


(********************************************************************)
(* Override the default notation for lists to be right biased.
   We're only using lists for environments and substitutions, 
   where the right biased order is more natural. *)
Notation "xs :> x"  := (x :: xs)   (at level 61, left associativity).
Notation "xs >< ys" := (app ys xs) (at level 60, right associativity).

