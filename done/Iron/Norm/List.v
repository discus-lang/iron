
Require Import Coq.Lists.List.


(* Normalise foralls to In form. *)
Ltac norm_lists := 
 repeat
  (match goal with 
   | [ H: Forall _ _ |- _ ] => rewrite Forall_forall in H
   | [ H: _ |- Forall _ _ ] => rewrite Forall_forall
   end).

