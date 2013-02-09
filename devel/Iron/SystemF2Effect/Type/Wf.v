
Require Export Iron.SystemF2Effect.Kind.
Require Export Iron.SystemF2Effect.Type.Ty.


(* Well formed types are closed under the given kind environment. *)
Inductive wfT (kn: nat) : ty -> Prop :=
 | WfT_TVar 
   :  forall ki
   ,  ki < kn
   -> wfT kn (TVar ki)

 | WfT_TForall
   :  forall k t
   ,  wfT (S kn) t
   -> wfT kn (TForall k t)

 | WfT_TApp
   :  forall t1 t2
   ,  wfT kn t1 -> wfT kn t2
   -> wfT kn (TApp t1 t2)

 | WfT_TSum
   :  forall t1 t2
   ,  wfT kn t1 -> wfT kn t2
  ->  wfT kn (TSum t1 t2)

 | WfT_TBot
   :  forall k
   ,  wfT kn (TBot k)

 | WfT_TCon0
   :  forall tc
   ,  wfT kn (TCon0 tc)

 | WfT_TCon1 
   :  forall tc t1
   ,  wfT kn t1
   -> wfT kn (TCon1 tc t1)

 | WfT_TCon2 
   :  forall tc t1 t2
   ,  wfT kn t1 -> wfT kn t2
   -> wfT kn (TCon2 tc t1 t2)

 | WfT_TCap
   :  forall tc
   ,  wfT kn (TCap tc).

Hint Constructors wfT.


(******************************************************************************)
(* Closed types are well formed under an empty environment. *)
Definition closedT : ty -> Prop
 := wfT O.
Hint Unfold closedT.


Lemma closedT_tRef
 :  forall r1 t2
 ,  closedT t2
 -> closedT (tRef (TCap (TyCapRegion r1)) t2).
Proof. 
 intros.
 unfold tRef. auto.
Qed.
Hint Resolve closedT_tRef.


(******************************************************************************)
(* Type is well formed under an environment one element larger. *)
Lemma wfT_succ
 :  forall tn t1
 ,  wfT tn     t1
 -> wfT (S tn) t1.
Proof.
 intros. gen tn.
 induction t1; intros; inverts H; eauto.
Qed.
Hint Resolve wfT_succ.


(* Type is well formed under a larger environment. *)
Lemma wfT_more
 :  forall tn1 tn2 tt
 ,  tn1 <= tn2
 -> wfT tn1 tt
 -> wfT tn2 tt.
Proof.
 intros. gen tn1 tn2.
 induction tt; intros; inverts H0; eauto.

 Case "TVar".
  eapply WfT_TVar; burn. omega.

 Case "TForall".
  eapply WfT_TForall.
  lets D: IHtt H2 (S tn2).
  eapply D. omega.
Qed.
Hint Resolve wfT_more.


(* Type is well formed under a larger environment. *)
Lemma wfT_max
 :  forall tn1 tn2 tt
 ,  wfT tn1 tt
 -> wfT (max tn1 tn2) tt.
Proof.
 intros.
 assert (  ((tn1 <  tn2) /\ max tn1 tn2 = tn2) 
        \/ ((tn2 <= tn1) /\ max tn1 tn2 = tn1)).
  eapply Max.max_spec.

 inverts H0. rip. rewritess.
  eapply wfT_more; eauto.

 inverts H1. rip. rewritess; burn.
Qed.
Hint Resolve wfT_max.


(* For every type, there is an environment that it is well formed under. *)
Lemma wfT_exists
 :  forall t1
 ,  (exists tn, wfT tn t1).
Proof.
 intros.
 induction t1;
  try (solve [exists 0; auto]).

 Case "TVar".
  exists (S n). eauto.

 Case "TForall".
  shift tn.
  eapply WfT_TForall; eauto.

 Case "TApp".
  destruct IHt1_1 as [tn1].
  destruct IHt1_2 as [tn2].
  exists (max tn1 tn2).
  eapply WfT_TApp. 
   eauto.
   rewrite Max.max_comm. eauto.

 Case "TSum".
  destruct IHt1_1 as [tn1].
  destruct IHt1_2 as [tn2].
  exists (max tn1 tn2).
  eapply WfT_TSum.
   eauto.
   rewrite Max.max_comm. eauto.

 Case "TCon1".
  shift tn. auto.

 Case "TCon2".
  destruct IHt1_1 as [tn1].
  destruct IHt1_2 as [tn2].
  exists (max tn1 tn2).
  eapply WfT_TCon2.
   eauto.
   rewrite Max.max_comm. auto.
Qed.
Hint Resolve wfT_exists.


(* A type application constructed from well formed components is
   itself well formed. *)
Lemma makeTApps_wfT
 :  forall n t1 ts
 ,  wfT n t1 
 -> Forall (wfT n) ts
 -> wfT n (makeTApps t1 ts).
Proof.
 intros. gen t1.
 induction ts; intros.
  simpl. auto.
  simpl.
  inverts H0.
  assert (ts = nil \/ (exists t ts', ts = t <: ts')) as HS.
   apply snocable.
   inverts HS.
    simpl. auto. 
    dest H0. dest H0. subst.
    eapply IHts. auto.
     auto.
Qed.

