
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.WfT.


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


(* Take the region identifier from an effect, if any. *)
Fixpoint handleOfEffect (e : ty) : option nat :=
 match e with
 | TCon1 tc (TRgn p)  => if isEffectTyCon_b tc then Some p else None
 | _                  => None
 end.


(********************************************************************)
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
 - simpl in H. subst. auto.
 - eapply IHts in H. simpl in H. auto.
Qed.
Hint Resolve makeTApps_takeTCon.


Lemma makeTApps_rewind
 :  forall t1 t2 ts
 ,  makeTApps (TApp t1 t2) ts 
 =  makeTApps t1 (t2 :: ts).
Proof. burn. Qed.


(* A type application constructed from well formed components is
   itself well formed. *)
Lemma makeTApps_wfT
 :  forall n t1 ts
 ,  WfT n t1 
 -> Forall (WfT n) ts
 -> WfT n (makeTApps t1 ts).
Proof.
 intros. gen t1.
 induction ts; intros.
 - simpl. auto.
 - simpl.
   inverts H0.
   have HS: (ts = nil \/ (exists t ts', ts = t <: ts')) 
    by (apply snocable).
   inverts HS.
   + simpl. auto.
   + dest H0. dest H0. subst.
     eapply IHts; auto.
Qed.


Lemma handleOfEffect_form_some
 :  forall e p
 ,  handleOfEffect e = Some p
 -> exists tc
     ,  e    = TCon1 tc (TRgn p) 
     /\ true = isEffectTyCon_b tc.
Proof.
 intros.
 destruct e; snorm.
 - destruct e; snorm. 
   destruct t0; snorm.
   exists t. rip.
 - destruct e; snorm.
   destruct t0; snorm.
Qed.
Hint Resolve handleOfEffect_form_some.

