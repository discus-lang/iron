

(* Apply rewrites from the hypotheses *)
Ltac rewritess
 := simpl; 
    match goal with
    | [H: eq _ _               |- _ ] => simpl; rewrite H; auto
    | [H: forall _,     eq _ _ |- _ ] => simpl; rewrite H; auto
    | [H: forall _ _,   eq _ _ |- _ ] => simpl; rewrite H; auto
    | [H: forall _ _ _, eq _ _ |- _ ] => simpl; rewrite H; auto
    end.


Tactic Notation "rw" constr(E) "by" tactic(T) :=
 let H := fresh 
 in assert E as H by T; rewrite H; clear H.

