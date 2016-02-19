
Require Export Iron.Data.List.
Require Export Iron.Tactics.Case.
Require Export Iron.Tactics.LibTactics.


(********************************************************************)
(* Rip apart compound hypothesis and goals.
   Then try auto to eliminate the easy stuff. *)
Ltac rip1
 := match goal with
      |- forall _, _ 
      => intros

    | |- _ /\ _
      => split

    | [H: _ /\ _            |- _ ]
      => inverts H

    | [H1: ?a -> ?b, H2: ?a |-  _]
      => specializes H1 H2
   end; try split.


Ltac rip
 := try (repeat rip1); auto.


(********************************************************************)
(* A better 'false'. 
   Try to eliminate the goal by finding a false hypothesis.
   This can be expensive as we repeatedly invert hypothesis, 
   which produces more of them.
*)
Ltac nope1
 := match goal with
    (* An equality might be false, so check it before
       attemptiong to clear it in the next case. *)
      [ H : _ = _ |- _] => solve [false]

    (* Inverting an equality doesn't make progress, 
       so just get rid of it. *)
    | [ H : _ = _ |- _] => clear H

    (* Keep inverting hypothesis provided we don't get anymore
       goals. If we get more goals then we'll diverge, and we're
       looking to eliminate this goal, not make more. *)
    | [ H : _     |- _] 
      => first [ solve [false]
               | solve [inverts H]
               | (inverts H ; [idtac]) ]
    end.


(* Nope solves the goal completely or does nothing *)
Ltac nope 
 := first [ solve [false; congruence]
          | rip; solve [repeat nope1] 
          | idtac ].

