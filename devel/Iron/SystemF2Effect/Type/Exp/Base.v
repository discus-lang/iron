
Require Export Iron.SystemF2Effect.Kind.
Require Export Iron.SystemF2Effect.Type.Exp.TyCon.
Require Export Iron.SystemF2Effect.Type.Exp.TyCap.


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

 (* Primitive capabilities. *)
 | TCap      : tycap  -> ty.
Hint Constructors ty.


(********************************************************************)
(* Notations for baked in types *)
(* Effect types *)
Notation TRead  R    := (TCon1 TyConRead  R).
Notation TWrite R    := (TCon1 TyConWrite R).
Notation TAlloc R    := (TCon1 TyConAlloc R).

(* Function type. *)
Notation TFun A E B  := (TApp (TApp (TApp (TCon0 TyConFun) A) E) B).

(* Primitive data types. *)
Notation TUnit       := (TCon0 TyConUnit).
Notation TBool       := (TCon0 TyConBool).
Notation TNat        := (TCon0 TyConNat).

(* Reference to a value in some region. *)
Notation TRef R T    := (TCon2 TyConRef R T).


(********************************************************************)
(* Predicates *)
Definition isTVar        (n : nat) (t : ty) : bool
 := match t with
    | TVar n'               => beq_nat n n'
    | _                     => false
    end.


Lemma isTVar_form
 :  forall i t
 ,  true = isTVar i t
 -> t    = TVar i.
Proof.
 intros.
 destruct t; snorm; try nope.
Qed.
Hint Resolve isTVar_form.


Definition isTCapRegion  (n : nat) (t : ty) : bool
 := match t with
    | TCap (TyCapRegion n') => beq_nat n n'
    | _                     => false
    end.

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


Definition isEffectOnVar (n : nat) (t : ty) : bool
 := match t with
    | TCon1 tc t1 => andb (isEffectTyCon tc) (isTVar n t1)
    | _           => false
    end.

Definition isEffectOnCap (n : nat) (t : ty) : bool
 := match t with 
    | TCon1 tc t1 => andb (isEffectTyCon tc) (isTCapRegion n t1)
    | _           => false
    end.
