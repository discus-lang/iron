
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.SystemF2Effect.Type.Relation.EquivTs.
Require Export Iron.SystemF2Effect.Type.Operator.BunchT.


Inductive SubsTs  : kienv -> stprops -> list ty -> list ty -> ki -> Prop :=
 | SbsSum 
   :  forall ke sp ts1 ts2 k
   ,  sumkind k
   -> Forall (fun t1 => KIND ke sp t1 k) ts1
   -> Forall (fun t2 => KIND ke sp t2 k) ts2
   -> Forall (fun t2 => In t2 ts1) ts2
   -> SubsTs ke sp ts1 ts2 k.


Lemma equivTs_subsTs
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> EquivTs ke sp t1 t2 k
 -> SubsTs  ke sp t1 t2 k.
Proof.
 intros.
 inverts H0.
 eapply SbsSum; auto.
Qed.


Lemma equivT_subsTs
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> EquivT ke sp t1 t2 k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros.
 eapply equivTs_subsTs; auto.
 eapply equivT_equivTs; auto.
Qed.


Lemma subsT_subsTs 
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> SubsT  ke sp t1             t2           k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros ke sp t1 t2 k HS HT.
 induction HT.
  Case "SbSumEquiv".
   eapply equivT_subsTs; auto.

  admit.                                   (* ok, need SubsTs trans *)
  admit.                                   (* ok, need SubsTs nil *)

  Case "SbSumAbove".
  { eapply SbsSum; rip.
    - have (KIND ke sp t1 k). 
      eapply flattenT_kind. 
      auto.
    - simpl. eapply Forall_app; eauto.
    - simpl. eapply Forall_app.
      inverts IHHT1. auto.
      inverts IHHT2. auto.
  }

 Case "SbSumBelow".
 { eapply SbsSum; rip.
   norm.
   simpl.
   inverts IHHT.
   norm.
 }
Qed.


Lemma bunchT_singleton
 :  forall ke sp t k
 ,  sumkind k
 -> KIND ke sp t k
 -> EquivT ke sp (bunchT k (t :: nil)) t k.
Proof.
 intros.
 simpl.
 eapply EqSym. 
  auto.
  auto.
  eapply EqSumBot; auto.
Qed.


Lemma subsTs_single_cases
 :  forall ke sp ts1 t1 t2 k
 ,  SubsTs ke sp (ts1 :> t1) (nil :> t2) k
 -> SubsTs ke sp ts1 (nil :> t2) k
 \/ t1 = t2.
Proof.
 admit.
Qed.


Lemma subsTs_subsT_1
 :  forall ke sp ts1 t2 k
 ,  SubsTs ke sp ts1 (t2 :: nil) k
 -> SubsT  ke sp (bunchT k ts1) t2 k.
Proof.
 intros.
 induction ts1.
 - nope.
 - have (sumkind k)       by inverts H; auto.
   have (KIND ke sp a  k) by inverts H; norm.
   have (KIND ke sp t2 k) by inverts H; norm.
   simpl.

   lets D: subsTs_single_cases H.
   inverts D.

   SCase "a = t2".
    rip.
    eapply subsT_sum_comm_above.
    eapply SbSumBelow; auto.
     eauto.

   SCase "subs".
    eapply SbSumBelow; auto.
     eapply bunchT_kind. auto.
      inverts H. norm.
Qed.


Lemma subsTs_subsT
 :  forall ke sp ts1 ts2 k
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsT  ke sp (bunchT k ts1) (bunchT k ts2) k.
Proof.
 intros. gen ke sp ts1.
 induction ts2; intros.
  - have (sumkind k)   by inverts H; auto.
    simpl.
    eapply SbBot; auto.
     eapply bunchT_kind; auto.
      inverts H. norm.

  - have (sumkind k)   by inverts H; auto.
    simpl.
    eapply SbSumAbove; auto.
    + eapply subsTs_subsT_1; auto.
      inverts H.
      eapply SbsSum; rip.
      norm. norm.

    + eapply IHts2.
      inverts H.
      eapply SbsSum; rip.
      norm. norm.
Qed.  
