
Require Export Iron.Base.


(* Kind expressions *)
Inductive ki : Type :=
 | KStar   : ki.


(* Kind environments. *)
Definition kienv := list ki.
Hint Unfold kienv.


