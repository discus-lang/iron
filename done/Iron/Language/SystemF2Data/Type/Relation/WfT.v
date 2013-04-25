
Require Export Iron.Language.SystemF2Data.Type.Exp.


(********************************************************************)
(* Well formed types are closed under the given kind environment. *)
Inductive wfT (kn: nat) : ty -> Prop :=
 | WfT_TVar 
   :  forall ki
   ,  ki < kn
   -> wfT kn (TVar ki)

 | WfT_TCon
   :  forall n
   ,  wfT kn (TCon n)

 | WfT_TForall
   :  forall t
   ,  wfT (S kn) t
   -> wfT kn (TForall t)

 | WfT_TApp
   :  forall t1 t2
   ,  wfT kn t1 -> wfT kn t2
   -> wfT kn (TApp t1 t2).
Hint Constructors wfT.


(* Closed types are well formed under an empty environment. *)
Definition closedT : ty -> Prop
 := wfT O.
Hint Unfold closedT.


(********************************************************************)
Lemma wfT_succ
 :  forall tn t1
 ,  wfT tn     t1
 -> wfT (S tn) t1.
Proof.
 intros. gen tn.
 induction t1; intros; inverts H; eauto.
Qed.
Hint Resolve wfT_succ.


Lemma wfT_more
 :  forall tn1 tn2 tt
 ,  tn1 <= tn2
 -> wfT tn1 tt
 -> wfT tn2 tt.
Proof.
 intros. gen tn1 tn2.
 induction tt; intros; inverts H0; eauto.
Qed.
Hint Resolve wfT_more.


Lemma wfT_max
 :  forall tn1 tn2 tt
 ,  wfT tn1 tt
 -> wfT (max tn1 tn2) tt.
Proof.
 intros.
 assert (  ((tn1 <  tn2) /\ max tn1 tn2 = tn2) 
        \/ ((tn2 <= tn1) /\ max tn1 tn2 = tn1)).
  eapply Max.max_spec.

 inverts H0. 
 - rip. rewritess.
   eapply wfT_more; eauto. 

 - inverts H1.
   rip. rewritess. auto.
Qed.
Hint Resolve wfT_max.


Lemma wfT_exists
 :  forall t1
 ,  (exists tn, wfT tn t1).
Proof.
 intros.
 induction t1.
 - Case "TCon".
   exists 0. auto.

 - Case "TVar".
   exists (S n). eauto.

 - Case "TForall".
   shift tn.
   eapply WfT_TForall; eauto.

 - Case "TApp".
   destruct IHt1_1 as [tn1].
   destruct IHt1_2 as [tn2].
   exists (max tn1 tn2).
   eapply WfT_TApp. 
    eauto.
    rewrite Max.max_comm. eauto.
Qed.
Hint Resolve wfT_exists.
