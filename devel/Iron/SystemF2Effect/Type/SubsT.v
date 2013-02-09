
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.


(* Type subsumptinon.
   The interesting cases all concern sums. *)
Inductive SubsT : ty -> ty -> Prop :=
 | SbEquiv
   :  forall t1 t2
   ,  EquivT t1 t2
   -> SubsT  t1 t2

 | SbTrans
   :  forall t1 t2 t3
   ,  SubsT  t1 t2 -> SubsT t2 t3
   -> SubsT  t1 t3

 | SbBot
   :  forall t k
   ,  SubsT  t (TBot k)

 | SbSumAbove
   :  forall t1 t2 t3
   ,  SubsT t1 t2
   -> SubsT t1 t3
   -> SubsT t1 (TSum t2 t3)

 | SbSumBelow
   :  forall t1 t2 t3
   ,  SubsT t1 t2
   -> SubsT (TSum t1 t3) t2.

Hint Constructors SubsT.


Lemma substT_equiv_above
 :  forall t1 t1' t2
 ,  EquivT t1 t1' 
 -> SubsT  t1 t2  -> SubsT t1' t2.
Proof. eauto. Qed.


Lemma substT_equiv_below
 :  forall t1 t2 t2'
 ,  EquivT t2 t2' 
 -> SubsT  t1 t2  -> SubsT t1 t2'.
Proof. eauto. Qed.


Lemma subsT_sum_comm_below
 :  forall t1 t2 t3
 ,  SubsT t1 (TSum t2 t3)
 -> SubsT t1 (TSum t3 t2).
Proof. eauto. Qed.
Hint Resolve subsT_sum_comm_below.


Lemma subsT_sum_comm_above
 :  forall t1 t2 t3
 ,  SubsT (TSum t1 t2) t3
 -> SubsT (TSum t2 t1) t3.
Proof. eauto. Qed.
Hint Resolve subsT_sum_comm_above.


Lemma subsT_sum_left
 : forall t1 t1' t2
 , SubsT  t1 t1'
-> SubsT (TSum t1 t2) (TSum t1' t2).
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
 : forall t1 t2 t2'
 , SubsT  t2 t2'
-> SubsT (TSum t1 t2') (TSum t1 t2').
Proof.
 intros.
 eapply SbSumAbove; eauto.
Qed.
Hint Resolve subsT_sum_right.

