
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Kind.


(********************************************************************)
(* Well formed types are closed under the given kind environment. *)
Inductive WfT (kn: nat) : ty -> Prop :=
 | WfT_TVar 
   :  forall ki
   ,  ki < kn
   -> WfT kn (TVar ki)

 | WfT_TForall
   :  forall k t
   ,  WfT (S kn) t
   -> WfT kn (TForall k t)

 | WfT_TApp
   :  forall t1 t2
   ,  WfT kn t1 -> WfT kn t2
   -> WfT kn (TApp t1 t2)

 | WfT_TSum
   :  forall t1 t2
   ,  WfT kn t1 -> WfT kn t2
  ->  WfT kn (TSum t1 t2)

 | WfT_TBot
   :  forall k
   ,  WfT kn (TBot k)

 | WfT_TCon0
   :  forall tc
   ,  WfT kn (TCon0 tc)

 | WfT_TCon1 
   :  forall tc t1
   ,  WfT kn t1
   -> WfT kn (TCon1 tc t1)

 | WfT_TCon2 
   :  forall tc t1 t2
   ,  WfT kn t1 -> WfT kn t2
   -> WfT kn (TCon2 tc t1 t2)

 | WfT_TCap
   :  forall tc
   ,  WfT kn (TCap tc).
Hint Constructors WfT.

Notation ClosedT := (WfT 0).


(******************************************************************************)
Lemma closedT_tRef
 :  forall p1 t2
 ,  ClosedT t2
 -> ClosedT (TRef (TRgn p1) t2).
Proof. auto. Qed.
Hint Resolve closedT_tRef.


(* Type is well formed under an environment one element larger. *)
Lemma wfT_succ
 :  forall tn t1
 ,  WfT tn     t1
 -> WfT (S tn) t1.
Proof.
 intros. gen tn.
 induction t1; intros; inverts H; eauto.
Qed.
Hint Resolve wfT_succ.


(* Type is well formed under a larger environment. *)
Lemma wfT_more
 :  forall tn1 tn2 tt
 ,  tn1 <= tn2
 -> WfT tn1 tt
 -> WfT tn2 tt.
Proof.
 intros. gen tn1 tn2.
 induction tt; intros; inverts H0; eauto.
Qed.
Hint Resolve wfT_more.


(* Type is well formed under a larger environment. *)
Lemma wfT_max
 :  forall tn1 tn2 tt
 ,  WfT tn1 tt
 -> WfT (max tn1 tn2) tt.
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
 ,  (exists tn, WfT tn t1).
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

