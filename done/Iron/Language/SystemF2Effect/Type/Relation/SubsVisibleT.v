
Require Export Iron.Language.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.


(********************************************************************)
(* Check whether an effect is visible relative to the region handles
   the given store properties. If an effect is some other region handle
   not in the store properties, then count that as not visible. *)
Definition isVisibleE (sp : stprops) (t : ty) : bool :=
 match t with 
 | TCon1 tc (TRgn n) => andb (isEffectTyCon_b tc) (hasSRegion n sp)
 | otherwise         => true
 end.


(* Subsumption of effects, where we only care about effects that 
   are visible in the given set of store properties. 

   We use this in the proof of perservation.
   At each step in the reduction we allow the term to allocate new
   regions and have effects on those regions, as they are not
   mentioned in the previous list of store properties. *)
Definition SubsVisibleT ke sp spVis e e'
 := SubsT ke
          sp 
          e 
          (maskOnT (fun t => negb (isVisibleE spVis t)) e') 
          KEffect.


(********************************************************************)
(* If isVisibleE applied to some type returns false,
   then that type must have been an effect on some region handle
   that was not in the provided store properties. *)
Lemma isVisibleE_TCon1_false
 :  forall sp t1
 ,  false = isVisibleE sp t1
 -> (exists tc p
      ,  t1    = TCon1 tc (TRgn p)
     /\ (false = isEffectTyCon_b tc \/ false = (hasSRegion p sp))).
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


Lemma isVisibleE_extends_cover
 :  forall sp sp' t
 ,  extends sp' sp
 -> false = isVisibleE sp' t
 -> false = isVisibleE sp  t.
Proof.
 intros.
 unfold isVisibleE in *.
 destruct t;  auto.
 destruct t0; auto.
 destruct t0; auto.
 apply beq_false_split in H0.
 inverts H0.
 - eapply beq_false_join. snorm.
 - eapply beq_false_join. 
   right.
   unfold hasSRegion in *. 
   unfold extends in *. 
   destruct H. subst.
   induction sp. snorm. snorm.
Qed.



Lemma subsVisibleT_refl
 :  forall ke sp spVis e
 ,  KindT  ke sp e KEffect
 -> SubsVisibleT ke sp spVis e e.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT_below. auto.
Qed.
Hint Resolve subsVisibleT_refl.


Lemma subsVisibleT_trans
 :  forall ke sp spVis e1 e2 e3
 ,  SubsVisibleT ke sp spVis e1 e2
 -> SubsVisibleT ke sp spVis e2 e3
 -> SubsVisibleT ke sp spVis e1 e3.
Proof.
 intros.
 unfold SubsVisibleT in *.
 eapply SbTrans.
  eapply H.
  eapply maskOnT_subsT in H0.
  erewrite maskOnT_idemp in H0. 
  auto.
Qed.
 

 Lemma subsT_subsVisibleT
 :  forall       ke sp spVis e1 e2
 ,  SubsT        ke sp       e1 e2 KEffect
 -> SubsVisibleT ke sp spVis e1 e2.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT_below. auto.
Qed.


Lemma subsVisibleT_sum_above
 :  forall ke sp spVis e1 e2 e3
 ,  SubsVisibleT ke sp spVis e1 e2
 -> SubsVisibleT ke sp spVis e1 e3
 -> SubsVisibleT ke sp spVis e1 (TSum e2 e3).
Proof. 
 intros.
 unfold SubsVisibleT in *.
 simpl.
 eapply SbSumAbove; auto.
Qed.
Hint Resolve subsVisibleT_sum_above.


Lemma subsVisibleT_sum_above_left
 :  forall ke sp spVis e1 e2 e3
 ,  SubsVisibleT ke sp spVis e1 (TSum e2 e3)
 -> SubsVisibleT ke sp spVis e1 e2.
Proof. 
 intros.
 unfold SubsVisibleT in *.
 eapply SbSumAboveLeft; eauto.
Qed.
Hint Resolve subsVisibleT_sum_above_left.


Lemma subsVisibleT_sum_above_right
 :  forall ke sp spVis e1 e2 e3
 ,  SubsVisibleT ke sp spVis e1 (TSum e2 e3)
 -> SubsVisibleT ke sp spVis e1 e3.
Proof. 
 intros.
 unfold SubsVisibleT in *.
 eapply SbSumAboveRight; eauto.
Qed.
Hint Resolve subsVisibleT_sum_above_right.


Lemma subsVisibleT_stprops_extends
 :  forall ke sp1 sp2 spVis e e'
 ,  extends sp2 sp1
 -> SubsVisibleT ke sp1 spVis e e'
 -> SubsVisibleT ke sp2 spVis e e'.
Proof.
 intros.
 unfold SubsVisibleT in *.
 eapply subsT_stprops_extends; eauto.
Qed.


Lemma maskOnT_subsT_impl
 :  forall ke sp e1 e2 (p : ty -> bool) (p' : ty -> bool)
 ,  (forall t, true = p t -> true = p' t)
 -> SubsT ke sp e1 (maskOnT p  e2) KEffect
 -> SubsT ke sp e1 (maskOnT p' e2) KEffect.
Proof.
 intros. gen ke sp.
 induction e2; snorm.

 - Case "TSum".
   eapply SbSumAbove; eauto.

 - Case "TCon1".
   clear IHe2.
   unfold maskOnT. 
   split_if.
   + eauto.
   + unfold maskOnT in H0.
     remember (p (TCon1 t e2)) as X.  
     destruct X.
     * apply H in HeqX. congruence.
     * tauto.
Qed.


Lemma subsVisibleT_spVis_strengthen
 :  forall ke sp spVis spVis' e1 e2
 ,  extends spVis' spVis
 -> SubsVisibleT ke sp spVis' e1 e2
 -> SubsVisibleT ke sp spVis  e1 e2.
Proof.
 intros.
 induction e2; snorm.

 - Case "TSum".
   lets He1: subsVisibleT_sum_above_left  H0.
   lets He2: subsVisibleT_sum_above_right H0.
   rip.

 - Case "TCon1".
   clear IHe2.
   unfold SubsVisibleT in H0.
   unfold SubsVisibleT.
   eapply maskOnT_subsT_impl.
   + assert (  forall t0, true = negb (isVisibleE spVis' t0)
                       -> true = negb (isVisibleE spVis  t0)) as HV.
     { intros.
       snorm.
       eapply negb_true_intro.
       eapply isVisibleE_extends_cover; eauto.
     }
     eapply HV.
   + eauto.
Qed.     


(* Manage the region phase change. 
   We need this when allocating a new region, where the associated
   region variable is replaced by the freshly allocated region handle. 

   Because the region handle will have been freshly allocated, 
   it won't appear in the previous set of store properties. *)
Lemma subsVisibleT_mask
 :  forall sp spVis r p e1 e2
 ,  hasSRegion p spVis = false
 -> r = TRgn p
 -> SubsVisibleT nil sp spVis e1 (maskOnVarT 0 e2)
 -> SubsVisibleT nil sp spVis e1 (substTT    0 r e2).
Proof.
 intros.
 induction e2; 
  try (solve [snorm]).

 - Case "TVar".
   snorm.
   subst.
   have (ClosedT (TVar  0)). nope.
   have (ClosedT (TVar  n)). nope.

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
   
 - Case "TCon1".
   snorm.
   unfold SubsVisibleT in H1.
   unfold maskOnVarT   in H1.
   unfold maskOnT at 2 in H1.
   split_if. 
   + snorm.
     unfold SubsVisibleT.
     unfold maskOnT.
     split_if; auto.
     * have HV: (IsTVar 0 e2).
       apply isTVar_form in HV. subst.
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
Qed.

