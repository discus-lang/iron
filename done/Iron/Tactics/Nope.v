
Require Import Iron.Tactics.Rip.
Require Import Iron.Tactics.LibTactics.


(* A better 'false'. 
   Try to eliminate the goal by finding a false hypothesis.
   Can be expensive when inverting many of the hypothesis produce
   more premises. *)
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
