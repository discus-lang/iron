
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivTs.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindTs.
Require Export Iron.Language.SystemF2Effect.Type.Operator.BunchT.


(********************************************************************)
Inductive SubsTs  : kienv -> stprops -> list ty -> list ty -> ki -> Prop :=
 | SbsSum 
   :  forall ke sp ts1 ts2 k
   ,  SumKind k
   -> KindTs ke sp ts1 k
   -> KindTs ke sp ts2 k
   -> Forall (fun t2 => In t2 ts1) ts2
   -> SubsTs ke sp ts1 ts2 k.


Lemma subsTs_single_cases
 :  forall ke sp ts1 t1 t2 k
 ,  SubsTs ke sp (ts1 :> t1) (nil :> t2) k
 -> SubsTs ke sp ts1 (nil :> t2) k
 \/ t1 = t2.
Proof.
 intros.
 inverts H.
 simpl in H3.
 eapply Forall_forall with (x := t2) in H3.
 - inverts H3.
   + tauto.
   + left. eapply SbsSum; snorm. eauto.
 - auto.
Qed.


Lemma subsTs_sumkind
 :  forall ke sp ts1 ts2 k
 ,  SubsTs ke sp ts1 ts2 k
 -> SumKind k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve subsTs_sumkind.


Lemma subsTs_kinds_left
 :  forall ke sp ts1 ts2 k
 ,  SubsTs ke sp ts1 ts2 k
 -> KindTs ke sp ts1 k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve subsTs_kinds_left.


Lemma subsTs_kinds_right
 :  forall ke sp ts1 ts2 k
 ,  SubsTs ke sp ts1 ts2 k
 -> KindTs ke sp ts1 k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve subsTs_kinds_right.


Lemma subsTs_refl
 :  forall ke sp ts k
 ,  SumKind k
 -> KindTs ke sp ts k
 -> SubsTs ke sp ts ts k.
Proof.
 intros.
 eapply SbsSum; eauto.
 snorm.
Qed.
Hint Resolve subsTs_refl.


Lemma subsTs_trans
 :  forall ke sp ts1 ts2 ts3 k
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsTs ke sp ts2 ts3 k
 -> SubsTs ke sp ts1 ts3 k.
Proof.
 intros.
 inverts H. inverts H0.
 eapply SbsSum; snorm.
Qed.


Lemma equivTs_subsTs
 :  forall ke sp t1 t2 k
 ,  SumKind k
 -> EquivTs ke sp t1 t2 k
 -> SubsTs  ke sp t1 t2 k.
Proof.
 intros.
 inverts H0.
 eapply SbsSum; auto.
Qed.


Lemma equivT_subsTs
 :  forall ke sp t1 t2 k
 ,  SumKind k
 -> EquivT ke sp t1 t2 k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros.
 eapply equivTs_subsTs; auto.
 eapply equivT_equivTs; auto.
Qed.


Lemma subsT_subsTs 
 :  forall ke sp t1 t2 k
 ,  SumKind k
 -> SubsT  ke sp t1             t2           k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros ke sp t1 t2 k HS HT.
 induction HT.

 - Case "SbEquiv".
   eapply equivT_subsTs; auto.

 - Case "SbTrans".
   eapply subsTs_trans. 
    eauto.
    spec IHHT1 HS.
    spec IHHT2 HS.
    auto.

 - Case "SbBot".
   simpl.
   eapply SbsSum; snorm.

 - Case "SbSumAbove".
   eapply SbsSum; rip.
    + have (KindT ke sp t1 k). auto.
    + simpl. eapply kindTs_app; eauto.
    + simpl. eapply Forall_app; eauto.
      inverts IHHT1; auto.
      inverts IHHT2; auto.

 - Case "SbSumBelow".
   spec IHHT HS.
   eapply SbsSum; eauto.
   inverts IHHT.
   snorm.

 - Case "SbSumAboveLeft".
   spec IHHT HS.
   simpl in IHHT.
   inverts IHHT.
   eapply SbsSum; eauto.

 - Case "SbSumAboveRight".
   spec IHHT HS.
   inverts IHHT.
   eapply SbsSum; eauto.
Qed.
Hint Resolve subsT_subsTs.


Lemma subsTs_subsT_1
 :  forall ke sp ts1 t2 k
 ,  SubsTs ke sp ts1 (t2 :: nil) k
 -> SubsT  ke sp (bunchT k ts1) t2 k.
Proof.
 intros.
 induction ts1.
 - nope.
 - have (SumKind k)        by inverts H; auto.
   have (KindT ke sp a  k) by inverts H; eauto.
   have (KindT ke sp t2 k) by inverts H; eauto.
   simpl.

   lets D: subsTs_single_cases H.
   inverts D.

   + SCase "subs". 
     rip.
 
   + SCase "a = t2".
     eapply SbSumBelow; auto.
     eapply bunchT_kindT. auto. 
      inverts H; eauto.
Qed.


Lemma subsTs_subsT
 :  forall ke sp ts1 ts2 k
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsT  ke sp (bunchT k ts1) (bunchT k ts2) k.
Proof.
 intros. gen ke sp ts1.
 induction ts2; intros.
  - have (SumKind k)   by inverts H; auto.
    simpl.
    eapply SbBot; auto.
     eapply bunchT_kindT; auto.
      inverts H. norm.

  - have (SumKind k)   by inverts H; auto.
    simpl.
    eapply SbSumAbove; auto.
    + eapply subsTs_subsT_1; auto.
      inverts H.
      eapply SbsSum; rip. 
       eauto. snorm.

    + eapply IHts2.
      inverts H.
      eapply SbsSum; rip.
       eauto. snorm.
Qed.  
Hint Resolve subsTs_subsT.

