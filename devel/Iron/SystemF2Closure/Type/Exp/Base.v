
Require Export Iron.SystemF2Closure.Kind.
Require Export Iron.SystemF2Closure.Type.Exp.TyCon.
Require Export Iron.SystemF2Closure.Type.Exp.TyCap.


(********************************************************************)
(* Type Expressions. *)
Inductive ty  : Type :=
 | TVar      : nat    -> ty
 | TForall   : ki     -> ty -> ty
 | TApp      : ty     -> ty -> ty
 | TSum      : ty     -> ty -> ty
 | TBot      : ki     -> ty

 (* Primitive constructed types. *)
 | TCon0     : tycon0 -> ty
 | TCon1     : tycon1 -> ty -> ty
 | TCon2     : tycon2 -> ty -> ty -> ty
 | TCon3     : tycon3 -> ty -> ty -> ty -> ty

 (* Primitive capabilities. *)
 | TCap      : tycap  -> ty.
Hint Constructors ty.


(********************************************************************)
(* Notations for baked in types *)
(* Function type. *)
Notation TFun A B    := (TApp (TApp (TCon0 TyConFun) A) B).

(* Computation type,
   with a result type, effect and closure. *)
Notation TComp A E C := (TApp (TApp (TApp (TCon3 TyConComp) A) E) C).

(* Effect types *)
Notation TRead  R    := (TCon1 TyConRead  R).
Notation TWrite R    := (TCon1 TyConWrite R).
Notation TAlloc R    := (TCon1 TyConAlloc R).

(* Closure types *)
Notation TUse   R    := (TCon1 TyConUse   R).

(* Primitive data types. *)
Notation TUnit       := (TCon0 TyConUnit).
Notation TBool       := (TCon0 TyConBool).
Notation TNat        := (TCon0 TyConNat).

(* Reference to a value in some region. *)
Notation TRef R T    := (TCon2 TyConRef R T).


(********************************************************************)
(* Predicates to test whether types have specific forms. *)

(* Check whether a type is a variable with the given index. *)
Definition isTVar (n : nat) (t : ty) : bool
 := match t with
    | TVar n'               => beq_nat n n'
    | _                     => false
    end.


(* If we know a type is a variable, then it is one.. *)
Lemma isTVar_form
 :  forall i t
 ,  true = isTVar i t
 -> t    = TVar i.
Proof.
 intros.
 destruct t; snorm; try nope.
Qed.
Hint Resolve isTVar_form.


(* Check whether a type is a region handle with the given index. *)
Definition isTCapRegion  (n : nat) (t : ty) : bool
 := match t with
    | TCap (TyCapRegion n') => beq_nat n n'
    | _                     => false
    end.


(* If we know a tpye is a region handle, then it is one.. *)
Lemma isTCapRegion_form
 :  forall i t
 ,  true = isTCapRegion i t
 -> t    = TCap (TyCapRegion i).
Proof.
 intros.
 destruct t; snorm; try nope.
  destruct t. snorm. subst. auto.
Qed.
Hint Resolve isTCapRegion_form.


(* Check whether a type is an effect on the given region variable. *)
Definition isEffectOnVar (n : nat) (t : ty) : bool
 := match t with
    | TCon1 tc t1 => andb (isEffectTyCon tc) (isTVar n t1)
    | _           => false
    end.


(* Check whether a type is an effect on the given region handle. *)
Definition isEffectOnCap (n : nat) (t : ty) : bool
 := match t with 
    | TCon1 tc t1 => andb (isEffectTyCon tc) (isTCapRegion n t1)
    | _           => false
    end.

