
Require Import Base.Class.Functor.
Require Import Base.Class.Monoid.
Require Import Program.Basics.
Require Import Coq.Lists.List.

Section list.
Hint Transparent compose.


Instance Functor_list 
 : @Functor list map.
Proof. split.

 (* map_id *)
 - intros. 
   induction xx; simpl. 
   + trivial.
   + rewrite IHxx. trivial.

 (* map_map *)
 - intros.
   induction xx; simpl.
   + trivial.
   + rewrite IHxx. trivial.
Qed.


Instance Monoid_list_app {A : Type}
 : @Monoid (@list A) (@nil A) (@app A).
Proof. split.

 (* unit_left *)
 - intros. simpl. trivial.

 (* unit_right *)
 - intros.
   induction x.
   + simpl. trivial.
   + simpl. rewrite IHx. trivial.

 (* dot_assoc *)
 - apply app_assoc.
Qed.


End list.

