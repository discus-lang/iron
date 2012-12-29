
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

    | [ H1 : _ = ?C ?y1
      , H2 : _ = ?C ?y2 |- _]
    => assert (y1 = y2); rewrite H1 in H2; inverts H2; trivial

    | [ H1 : ?C ?y1 = _
      , H2 : ?C ?y2 = _ |- _]
    => assert (y1 = y2); rewrite H1 in H2; inverts H2; trivial
   end; try split.


Ltac rip
 := try (repeat rip1); auto.

