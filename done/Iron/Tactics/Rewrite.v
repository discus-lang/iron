
Require Import Iron.Tactics.Have.


(* Apply rewrites from the hypotheses *)
Ltac rewritess
 := simpl; 
    match goal with
    | [H: eq _ _               |- _ ] => simpl; rewrite H; auto
    | [H: forall _,     eq _ _ |- _ ] => simpl; rewrite H; auto
    | [H: forall _ _,   eq _ _ |- _ ] => simpl; rewrite H; auto
    | [H: forall _ _ _, eq _ _ |- _ ] => simpl; rewrite H; auto
    end.


(* Rewrite using the 'have' tactic.
   Just state the equality to use. *)
Tactic Notation "rrwrite" constr(xx)
 := let H := fresh 
    in  assert xx as H  by have_auto; rewrite H in *;  clear H.

Tactic Notation "rrwrite" constr(xx) "by" tactic(T)
 := let H := fresh 
    in  assert xx as H  by T; rewrite H in *;  clear H.

Tactic Notation "rrwrite" constr(xx) "in" hyp(H)
 := let H2 := fresh
    in  assert xx as H2 by have_auto; rewrite H2 in H; clear H2.


