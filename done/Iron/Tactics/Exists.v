(* Tactics for working with existentials. *)

(* Destruct the existential in hypothesis H,
   and just use the name of the quantifier for the new variable. *)
Ltac dest H
 := match goal with 
    [ H : exists a, _ |- _ ]
     => destruct H as [a]
    end.

Ltac dests H
 := repeat (dest H).


(* Destruct the existential in hypothesis H, 
   and instantiate the existential in the goal with this variable. *)
Ltac shift H
 := match goal with 
    [ H : exists a, _ |- exists b, _] 
     => destruct H as [a]; exists a
    end.

Ltac shifts H
 := repeat (shift H).


