
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


Lemma typex_kind_type_effect
 :  forall ke te se sp v t e
 ,  TypeX  ke te se sp v t e
 -> (KindT ke sp t KData /\ KindT ke sp e KEffect).
Proof.
 intros. gen ke te se sp t e. 
 induction v using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TypeV  ke te se sp v t
      -> KindT  ke sp t KData);
   intros; inverts_type; eauto 1.

 - Case "VLam".
   lets D: IHv H8. rip.
    eapply KiApp.
     unfold AppKind. congruence.
     eapply KiApp.
     unfold AppKind. congruence.
     eapply KiApp.
     unfold AppKind. congruence.
     eapply KiCon0. simpl. eauto.
   auto. auto. auto.

 - Case "VLAM".
   spec IHv H7. rip.

 - Case "XConst".
   destruct c; snorm.

 - Case "XVar".
   burn.

 - Case "XApp".
   lets D1: IHv1 H10.
   lets D2: IHv2 H11.
   rip.

 - Case "XLet".
   lets D1: IHv H6.
   inverts D1.
   inverts H4.
   inverts H8.
   inverts H10.
   simpl in *.
   inverts H5. eauto.

 - Case "XAPP".
   eapply IHv in H6.
   inverts_kind.
   rip.
   eapply subst_type_type; eauto.

 - Case "XOp1".
   destruct o; simpl in *; inverts H6;
    rip.

 - Case "XPrivate".
   spec IHv H7. rip.
   eapply lower_type_type; eauto.
   eapply lower_type_type; eauto.

 - Case "XExtend".
   spec IHv H10. rip.
   + eapply subst_type_type; eauto.
   + eapply KiSum; auto. 
     eapply lower_type_type with (k1 := KRegion).
      eapply H2. eauto.
      eapply KiCon1; snorm.
 
 - Case "XAlloc".
   rip.
    eapply KiCon2; eauto. snorm.
    eapply KiCon1; eauto. snorm.
  
 - Case "XRead".
   spec IHv H9.
   inverts_kind; rip.
    destruct tc. norm. inverts H1. auto. 
    destruct tc. norm. inverts H1.
    eapply KiCon1. simpl in *. eauto. eauto.

 - Case "XWrite".
   rip. eapply KiCon1; eauto. snorm.
Qed.
Hint Resolve typex_kind_type_effect.


Lemma typev_kind_type
 :  forall ke te se sp v t
 ,  TypeV  ke te se sp v t
 -> KindT  ke sp t KData.
Proof.
 intros.
 eapply TxVal in H.
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typev_kind_type.


Lemma typex_kind_type
 :  forall ke te se sp x t e
 ,  TypeX  ke te se sp x t e
 -> KindT  ke sp t KData.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_type.


Lemma typex_kind_effect
 :  forall ke te se sp x t e
 ,  TypeX  ke te se sp x t e
 -> KindT  ke sp e KEffect.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_effect.

