
Require Import Iron.Tactics.Short.
Require Import Iron.Tactics.LibTactics.


(* Rip apart compound hypothesis and goals.
   Then try auto to eliminate the easy stuff. *)
Ltac rip
 := try 
     (repeat
       (match goal with
                              |- forall _, _ => intros;     rip
        |                        |- _ /\ _   => split;      rip
        | [H: _ /\ _             |- _ ]      => inverts H;  rip
        | [H1: ?a -> ?b, H2: ?a  |-  _]      => spec H1 H2; rip
        end)); try auto.

