
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




