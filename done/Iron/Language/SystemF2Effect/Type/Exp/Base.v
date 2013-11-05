
Require Export Iron.Language.SystemF2Effect.Kind.
Require Export Iron.Language.SystemF2Effect.Type.Exp.TyCon.
Require Export Iron.Language.SystemF2Effect.Type.Exp.TyCap.


(********************************************************************)
(* Type Expressions. *)
Inductive ty  : Type  := 
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
(* Region handles *)
Notation TRgn   P    := (TCap (TyCapRegion P)).

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
(* Predicates to test whether types have specific forms. *)

(* Check whether a type is a variable with the given index. *)
Definition isTVar   (n : nat) (t : ty) :=
 match t with
 | TVar n' => beq_nat n n'
 | _       => false
 end.


Definition IsTVar  (n : nat) (t : ty)
 := isTVar n t = true.


(* If we know a type is a variable, then it is one.. *)
Lemma isTVar_form
 :  forall i t
 ,  IsTVar i t
 -> t    = TVar i.
Proof.
 intros.
 destruct t; snorm; try nope.
 unfold IsTVar in *. snorm.
Qed.
Hint Resolve isTVar_form.


(* Check whether a type is a region handle with the given index. *)
Definition isTRgn (p : nat) (t : ty) :=
 match t with
 | TRgn p' => beq_nat p p'
 | _       => false
 end.


Definition IsTRgn   (p : nat) (t : ty) 
 := isTRgn p t = true.
Hint Unfold IsTRgn.


(* If we know a tpye is a region handle, then it is one.. *)
Lemma isTRgn_form
 :  forall p t
 ,  IsTRgn p t
 -> t    = TRgn p.
Proof.
 intros.
 destruct t; snorm; try nope.
 destruct t. unfold IsTRgn in *. snorm. subst. auto.
Qed.
Hint Resolve isTRgn_form.


(* Check whether a type is an effect on the given region variable. *)
Definition isEffectOnVar (n : nat) (t : ty) := 
 match t with
 | TCon1 tc t1 => andb (isEffectTyCon_b tc) (isTVar n t1)
 | _           => false
 end.


(* Check whether a type is an effect on the given region handle. *)
Definition isEffectOnCap (p : nat) (t : ty) :=
 match t with 
 | TCon1 tc t1 => andb (isEffectTyCon_b tc) (isTRgn p t1)
 | _           => false
 end.

