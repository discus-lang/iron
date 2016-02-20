
Require Export Iron.Language.DelayedSystemF.Base.


(********************************************************************)
(* Kinds *)
Inductive ki : Type :=
 | KStar  : ki.


(* Kind Environments *)
Definition kienv := @env ki.


(********************************************************************)
(* Types *)
Inductive ty : Type :=
 (* Data type constructor. *)
 | TCon  (c: name) : ty

 (* Type variable. *)
 | TVar  (a: name) : ty

 (* Type variable binding. *)
 | TForall (st: @subst ty ki) (a: name) (k: ki) (t: ty) : ty

 (* Function type constructor. *)
 | TFun  (t1: ty) (t2: ty) : ty.
Hint Constructors ty.


(* Type Environments *)
Definition tyenv := @env ty.

