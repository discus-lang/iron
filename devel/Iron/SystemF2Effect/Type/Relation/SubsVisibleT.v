
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.SystemF2Effect.Type.Operator.


Definition isVisibleE (sp : stprops) (t : ty) : bool
 := match t with 
    | TCon1 tc (TCap (TyCapRegion n)) 
    => andb (isEffectTyCon tc) (hasSRegion n sp)

    | otherwise
    => true
    end.


Lemma isVisibleE_TCon1_false
 :  forall sp t1
 ,  false = isVisibleE sp t1
 -> (exists tc n
      ,  t1    = TCon1 tc (TCap (TyCapRegion n))
     /\ (false = isEffectTyCon tc \/ false = (hasSRegion n sp))).
Proof.
 destruct t1; try nope.

 Case "TCon1".
  intros.
  exists t. 
  destruct t1; snorm; try nope.
   destruct t0.
   apply beq_false_split in H.
   exists n. rip.
Qed.



Definition SubsVisibleT ke sp e e'
 := SubsT ke
          sp 
          e 
          (maskOnT (fun t => negb (isVisibleE sp t)) e') 
          KEffect.


Lemma subsT_visible_refl
 :  forall ke sp e
 ,  KindT ke sp e KEffect
 -> SubsVisibleT ke sp e e.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT. auto.
Qed.
Hint Resolve subsT_visible_refl.


Lemma subsT_subsVisibleT
 :  forall       ke sp e1 e2
 ,  SubsT        ke sp e1 e2 KEffect
 -> SubsVisibleT ke sp e1 e2.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT. auto.
Qed.


Lemma subsVisibleT_sum_above
 :  forall ke sp e1 e2 e3
 ,  SubsVisibleT ke sp e1 e2
 -> SubsVisibleT ke sp e1 e3
 -> SubsVisibleT ke sp e1 (TSum e2 e3).
Proof. 
 intros.
 unfold SubsVisibleT in *.
 simpl.
 eapply SbSumAbove; auto.
Qed.
Hint Resolve subsVisibleT_sum_above.


Lemma subsVisibleT_sum_above_left
 :  forall ke sp e1 e2 e3
 ,  SubsVisibleT ke sp e1 (TSum e2 e3)
 -> SubsVisibleT ke sp e1 e2.
Proof. 
 intros.
 unfold SubsVisibleT in *.
 eapply SbSumAboveLeft. eauto.
Qed.
Hint Resolve subsVisibleT_sum_above_left.


Lemma subsVisibleT_sum_above_right
 :  forall ke sp e1 e2 e3
 ,  SubsVisibleT ke sp e1 (TSum e2 e3)
 -> SubsVisibleT ke sp e1 e3.
Proof. 
 intros.
 unfold SubsVisibleT in *.
 eapply SbSumAboveRight. eauto.
Qed.
Hint Resolve subsVisibleT_sum_above_right.


(********************************************************************)
Lemma subsVisibleT_mask
 :  forall sp r n e1 e2
 ,  hasSRegion n sp = false
 -> r = TCap (TyCapRegion n)
 -> SubsVisibleT nil sp e1 (maskOnT (isEffectOnVar 0) e2)
 -> SubsVisibleT nil sp e1 (substTT 0 r e2).
Proof.
 intros.
 induction e2.

 - Case "TVar".
   snorm.
   subst.
   have (ClosedT (TVar  0)). nope.
   have (ClosedT (TVar n0)). nope.

 - Case "TForall".
   simpl in H1.
   have (ClosedT (TForall k e2)).
   rrwrite ( substTT 0 r (TForall k e2) 
           = TForall k e2).
   auto.
  
 - Case "TApp".
   simpl in H1.
   have (ClosedT (TApp e2_1 e2_2)).
   rrwrite ( substTT 0 r (TApp e2_1 e2_2) 
           = TApp e2_1 e2_2).
   auto.

 - Case "TSum".
   snorm.
   simpl.
   eapply subsVisibleT_sum_above; eauto.
 
 - Case "TBot".
   snorm.

 - Case "TCon0".
   snorm.
  
 - Case "TCon1".
   snorm.
   unfold SubsVisibleT in H1.
   unfold maskOnT at 2 in H1.
   split_if. 
   + snorm.
     unfold SubsVisibleT.
     unfold maskOnT.
     split_if; auto.
     * apply isTVar_form in H3. subst.
       snorm. congruence.

   + snorm.
     unfold SubsVisibleT.
     unfold maskOnT. 
     split_if.
     * eauto.
     * unfold maskOnT in H1.
       norm_negb.
       
       split_if. 
       { norm_negb.
         eapply isVisibleE_TCon1_false in HeqH1.
         destruct HeqH1 as [tc].
         destruct H2    as [n2]. rip.
         inverts H3.
         snorm.
         inverts H4; congruence.
       }
       { have HC: (ClosedT (TCon1 t e2)).
         inverts HC.
         rrwrite (substTT 0 r e2 = e2).
         auto.
       }

 - Case "TCon2".
   simpl in H1.
   have (ClosedT (TCon2 t e2_1 e2_2)).
   rrwrite ( substTT 0 r (TCon2 t e2_1 e2_2)
           = TCon2 t e2_1 e2_2).
   snorm.
     
 - Case "TCap".
   snorm.
Qed.

