
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.


(* Type subsumptinon.
   The interesting cases all concern sums. *)
Inductive SubsT : ki -> ty -> ty -> Prop :=
 | SbEquiv
   :  forall k t1 t2
   ,  EquivT k t1 t2
   -> SubsT  k t1 t2

 | SbTrans
   :  forall k t1 t2 t3
   ,  SubsT  k t1 t2 -> SubsT k t2 t3
   -> SubsT  k t1 t3

 | SbBot
   :  forall k t
   ,  SubsT  k t (TBot k)

 | SbSumAbove
   :  forall k t1 t2 t3
   ,  SubsT  k t1 t2
   -> SubsT  k t1 t3
   -> SubsT  k t1 (TSum t2 t3)

 | SbSumBelow
   :  forall k t1 t2 t3
   ,  SubsT  k t1 t2
   -> SubsT  k (TSum t1 t3) t2.

Hint Constructors SubsT.


Lemma substT_equiv_above
 :  forall k t1 t1' t2
 ,  EquivT k t1 t1' 
 -> SubsT  k t1 t2  -> SubsT k t1' t2.
Proof. eauto. Qed.


Lemma substT_equiv_below
 :  forall k t1 t2 t2'
 ,  EquivT k t2 t2' 
 -> SubsT  k t1 t2  -> SubsT k t1 t2'.
Proof. eauto. Qed.


Lemma subsT_sum_comm_below
 :  forall k t1 t2 t3
 ,  SubsT  k t1 (TSum t2 t3)
 -> SubsT  k t1 (TSum t3 t2).
Proof. eauto. Qed.
Hint Resolve subsT_sum_comm_below.


Lemma subsT_sum_comm_above
 :  forall k t1 t2 t3
 ,  SubsT  k (TSum t1 t2) t3
 -> SubsT  k (TSum t2 t1) t3.
Proof. eauto. Qed.
Hint Resolve subsT_sum_comm_above.


Lemma subsT_sum_left
 : forall k t1 t1' t2
 , SubsT  k t1 t1'
-> SubsT  k (TSum t1 t2) (TSum t1' t2).
Proof.
 intros.
 eapply SbSumAbove. 
  eapply SbSumBelow. trivial.
  eapply SbTrans.
   eapply SbEquiv. 
    eapply EqSumComm.
   eapply SbSumBelow.
    eapply SbEquiv.
    eapply EqRefl.
Qed.
Hint Resolve subsT_sum_left.


Lemma subsT_sum_right
 : forall k t1 t2 t2'
 , SubsT  k t2 t2'
-> SubsT  k (TSum t1 t2) (TSum t1 t2').
Proof.
 intros.
 eapply SbSumAbove; eauto.
Qed.
Hint Resolve subsT_sum_right.


Lemma subsT_sum_merge
 :  forall k t1 t1' t2 t2'
 ,  SubsT  k t1 t1'
 -> SubsT  k t2 t2'
 -> SubsT  k (TSum t1 t2) (TSum t1' t2').
Proof.
 intros.
 eapply SbTrans.
  eapply subsT_sum_left.  eauto.
  eapply subsT_sum_right. eauto.
Qed.

