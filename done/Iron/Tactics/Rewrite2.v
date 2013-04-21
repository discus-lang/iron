
Require Import Iron.Tactics.Have.


(* Apply matching rewrites from the hypothesis. *)
Ltac down 
 := repeat (match goal with
    | [H : ?X = _  |- ?X = _  ] => rewrite H
    | [H : _  = ?X |- ?X = _  ] => rewrite H
    | [H : ?X = _  |- _  = ?X ] => rewrite <- H
    | [H : _  = ?X |- _  = ?X ] => rewrite <- H
    end); auto.


(* Apply all rewrites from the hypothesis. *)
Ltac rewritess
 := repeat (match goal with
    | [H: eq _ _                 |- _ ] => rewrite H in *
    | [H: forall _,       eq _ _ |- _ ] => rewrite H in *
    | [H: forall _ _,     eq _ _ |- _ ] => rewrite H in *
    | [H: forall _ _ _,   eq _ _ |- _ ] => rewrite H in *
    | [H: forall _ _ _ _, eq _ _ |- _ ] => rewrite H in *
    end).


(* Apply all erewrites from the hypothesis. *)
Ltac espread
 := repeat (match goal with
    | [H: eq _ _                       |- _ ] => erewrite H in *; clear H
    | [H: forall _,       eq _ _       |- _ ] => erewrite H in *; clear H
    | [H: forall _ _,     eq _ _       |- _ ] => erewrite H in *; clear H
    | [H: forall _ _ _,   eq _ _       |- _ ] => erewrite H in *; clear H
    | [H: forall _ _ _ _, eq _ _       |- _ ] => erewrite H in *; clear H
    | [H: forall _,       _ -> eq _ _  |- _ ] => erewrite H in *; clear H
    | [H: forall _ _,     _ -> eq _ _  |- _ ] => erewrite H in *; clear H
    | [H: forall _ _ _,   _ -> eq _ _  |- _ ] => erewrite H in *; clear H
    | [H: forall _ _ _ _, _ -> eq _ _  |- _ ] => erewrite H in *; clear H
    end).


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
