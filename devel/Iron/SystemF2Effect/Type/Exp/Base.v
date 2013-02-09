
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


(* Synonyms for baked in types. *****)

(* Function type. *)
Definition tFun   t1 eff t2     := TApp (TApp (TApp (TCon0 TyConFun) t1) eff) t2.

(* Primitive value types. *)
Definition tUnit                := TCon0 TyConUnit.
Definition tBool                := TCon0 TyConBool.
Definition tNat                 := TCon0 TyConNat.

(* Reference to a value in some region. *)
Definition tRef   r1 t2         := TCon2 TyConRef r1 t2.

(* Effect types. *)
Definition tRead    r1          := TCon1 TyConRead  r1.
Definition tWrite   r1          := TCon1 TyConWrite r1.
Definition tAlloc   r1          := TCon1 TyConAlloc r1.


(********************************************************************)
(* Type Utils *)

(* Construct a type application from a constructor type
   and a list of argument types. *)
Fixpoint makeTApps (t1: ty) (tt: list ty) : ty :=
 match tt with
 | nil     => t1
 | t :: ts => makeTApps (TApp t1 t) ts
 end.


Fixpoint takeTCon (tt: ty) : ty :=
 match tt with 
 | TApp t1 t2 => takeTCon t1
 | _          => tt
 end.

Fixpoint takeTArgs (tt: ty) : list ty :=
 match tt with 
 | TApp t1 t2 => snoc t2 (takeTArgs t1)
 | _          => cons tt nil
 end.


(* Break apart a type application into the constructor type
   and a list of argument types. *)
Definition takeTApps (tt: ty) : (ty * list ty) 
 := (takeTCon tt, takeTArgs tt).



Lemma makeTApps_snoc
 : forall t1 t2 t3 ts
 , makeTApps (TApp t1 t2) (snoc t3 ts) 
 = TApp (makeTApps t1 (cons t2 ts)) t3.
Proof.
 intros. gen t1 t2.
 induction ts; burn.
Qed.


Lemma makeTApps_snoc'
 :  forall t1 t2 ts
 ,  makeTApps t1 (snoc t2 ts)
 =  TApp (makeTApps t1 ts) t2.
Proof.
 intros. gen t1 t2.
 induction ts; burn.
Qed.


Lemma takeTCon_makeTApps
 :  forall t1 ts
 ,  takeTCon (makeTApps t1 ts) = takeTCon t1.
Proof.
 intros. gen t1.
 induction ts; rip; burn.
 simpl. rewritess. burn.
Qed.    
Hint Resolve takeTCon_makeTApps.


Lemma makeTApps_takeTCon
 :  forall t1 t2 ts  
 ,  makeTApps t1 ts = t2
 -> takeTCon t1     = takeTCon t2.
Proof.
 intros. gen t1 t2.
 induction ts; intros.
  simpl in H. subst. auto.
  eapply IHts in H. simpl in H. auto.
Qed.
Hint Resolve makeTApps_takeTCon.


Lemma makeTApps_rewind
 :  forall t1 t2 ts
 ,  makeTApps (TApp t1 t2) ts = makeTApps t1 (t2 :: ts).
Proof. burn. Qed.

