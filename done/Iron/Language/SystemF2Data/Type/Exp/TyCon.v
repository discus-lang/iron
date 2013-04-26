
Require Export Iron.Language.SystemF2Data.Base.
Require Export Iron.Language.SystemF2Data.Kind.


(********************************************************************)
(* Type Constructors. *)
Inductive tycon : Type :=
 (* The function type constructor. *)
 | TyConFun  : tycon

 (* Primitive type constructors. *)
 | TyConNat  : tycon
 | TyConBool : tycon

 (* Data type constructors. *)
 | TyConData : nat   -> ki -> tycon.
Hint Constructors tycon.


(* The unit type constructor. *)
Definition  tcUnit := TyConData 0 KStar.
Hint Unfold tcUnit.


(********************************************************************)
(* Check whether two type constructors are equal. *)
Fixpoint tycon_beq t1 t2 :=
 match t1, t2 with
 | TyConFun,       TyConFun       => true
 | TyConNat,       TyConNat       => true
 | TyConBool,      TyConBool      => true
 | TyConData n1 _, TyConData n2 _ => beq_nat n1 n2
 | _,              _              => false
 end.


(* Check whether this is the function type constructor. *)
Definition isTyConFun  (tc: tycon) : Prop :=
 match tc with
 | TyConFun      => True
 | _             => False
 end.
Hint Unfold isTyConFun.


(* Check whether this is is an algebraic type constructor
   not the function type constructor or a primitive type. *) 
Definition isTyConData (tc: tycon) : Prop :=
 match tc with
 | TyConData _ _ => True
 | _             => False
 end.
Hint Unfold isTyConData.

