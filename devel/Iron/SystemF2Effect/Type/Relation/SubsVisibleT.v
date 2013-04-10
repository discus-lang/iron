
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.SystemF2Effect.Type.Operator.


(********************************************************************)
(* Check whether an effect is visible relative to the region handles
   the given store properties. If an effect is some other region handle
   not in the store properties, then count that as not visible. *)
Definition isVisibleE (sp : stprops) (t : ty) : bool
 := match t with 
    | TCon1 tc (TCap (TyCapRegion n)) 
    => andb (isEffectTyCon tc) (hasSRegion n sp)

    | otherwise
    => true
    end.


(* If isVisibleE applied to some type returns false,
   then that type must have been an effect on some region handle
   that was not in the provided store properties. *)
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


(********************************************************************)
(* Subsumption of effects, where we only care about effects that 
   are visible in the given set of store properties. 

   We use this in the proof of perservation.
   At each step in the reduction we allow the term to allocate new
   regions and have effects on those regions, as they are not
   mentioned in the previous list of store properties. *)
Definition SubsVisibleT ke sp e e'
 := SubsT ke
          sp 
          e 
          (maskOnT (fun t => negb (isVisibleE sp t)) e') 
          KEffect.

  !!!!!!!!!!!! need to add another sp parameter.
               the effect e' will contain more regions than e, 
               but we only want to check it against the ones in e.
               Need to keep the sps for both e and e'.
               Otherwise the effect with more region handles isn't well kinded.



Lemma subsVisibleT_refl
 :  forall ke sp e
 ,  KindT  ke sp e KEffect
 -> SubsVisibleT ke sp e e.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT_below. auto.
Qed.
Hint Resolve subsVisibleT_refl.


Lemma subsVisibleT_trans
 :  forall ke sp e1 e2 e3
 ,  SubsVisibleT ke sp e1 e2
 -> SubsVisibleT ke sp e2 e3
 -> SubsVisibleT ke sp e1 e3.
Proof.
 intros.
 unfold SubsVisibleT in *.
 eapply SbTrans.
  eapply H.
  eapply maskOnT_subsT in H0.
  erewrite maskOnT_idemp in H0. 
  auto.
Qed.
 

(********************************************************************)
Lemma subsT_subsVisibleT
 :  forall       ke sp e1 e2
 ,  SubsT        ke sp e1 e2 KEffect
 -> SubsVisibleT ke sp e1 e2.
Proof.
 intros.
 unfold SubsVisibleT.
  eapply maskOnT_subsT_below. auto.
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
(*
Lemma subsT_stprops_weaken
 ,  forall ke sp1 sp2 t1 t2
 ,  extends sp2 sp1
 -> SubsT ke sp sp
*)

Lemma subsVisibleT_strengthen
 :  forall ke sp1 sp2 e e'
 ,  extends sp2 sp1
 -> SubsVisibleT ke sp2 e e'
 -> SubsVisibleT ke sp1 e e'.
Proof.
 intros.
 induction e'.
 - admit. 
   (* unfold SubsVisibleT in *. snorm.
   clear H. induction H0; auto. 
    admit. eauto. admit. *)
 
 - unfold SubsVisibleT in *.
   snorm.

Qed.


(********************************************************************)
(* Manage the region phase change. 
   We need this when allocating a new region, where the associated
   region variable is replaced by the freshly allocated region handle. 

   Because the region handle will have been freshly allocated, 
   it won't appear in the previous set of store properties. *)
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

