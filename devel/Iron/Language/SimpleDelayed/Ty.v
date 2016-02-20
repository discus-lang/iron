
Require Export Iron.Language.SimpleDelayed.Base.
Require Export Iron.Language.SimpleDelayed.Subst.


(* Types *)
Inductive ty  : Type :=
 (* Data type constructor. *)
 | TCon  (c: name) : ty

 (* Function type constructor. *)
 | TFun  (t1: ty) (t2: ty) : ty.
Hint Constructors ty.


(* Type Environments *)
Definition tyenv := @env ty.




