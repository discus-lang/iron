

Require Import Iron.Tactics.LibTactics.

(* Rip apart compound hypothesis and goals.
   Then try auto to eliminate the easy stuff. *)
Ltac rip1
 := match goal with
      |- forall _, _ 
      => intros

    | |- _ /\ _      
      => split

    | [H: _ /\ _             |- _ ]         
      => inverts H

    | [H1: ?a -> ?b, H2: ?a  |-  _]
      => specializes H1 H2
   end; try split.


Ltac rip
 := try (repeat rip1); auto.
