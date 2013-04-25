
Require Export Iron.Language.SystemF2Data.Base.
Require Export Iron.Language.SystemF2Data.Kind.
Require Export Iron.Language.SystemF2Data.Type.Exp.TyCon.


(* Type Expressions. *)
Inductive ty  : Type :=
 | TCon      : tycon -> ty
 | TVar      : nat   -> ty
 | TForall   : ty    -> ty
 | TApp      : ty    -> ty -> ty.
Hint Constructors ty.


(* Builtin in types. *)
Definition tUnit 
 := TCon tcUnit.

Definition tFun (t1: ty) (t2: ty)
 := TApp (TApp (TCon TyConFun) t1) t2.
Hint Unfold tFun.

Definition tNat
 := TCon TyConNat.

Definition tBool
 := TCon TyConBool.
