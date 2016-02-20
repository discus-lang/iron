

Require Import Coq.Lists.List.


Class Monoid {A : Type}
 (unit : A)
 (dot  : A -> A -> A) : Prop 
:= {
 dot_assoc : forall x y (z : A)
           , dot x (dot y z) = dot (dot x y) z;

 dot_left  : forall x, dot unit x = x;
 dot_right : forall x, dot x unit = x 
}.


(* Monoid instance for lists with append *)
Instance MonoidListApp 
 : forall A, @Monoid (list A) nil (@app A).
Proof.
 intros. split.
 - apply app_assoc.
 - apply app_nil_l.
 - apply app_nil_r.
Defined.

