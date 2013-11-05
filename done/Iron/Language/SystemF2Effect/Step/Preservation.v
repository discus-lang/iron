
Require Export Iron.Language.SystemF2Effect.Step.TypeC.
Require Export Iron.Language.SystemF2Effect.Store.LiveS.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp sp' ss ss' fs fs' x x' t e
 ,  WfFS   se sp ss  fs
 -> LiveS ss fs -> LiveE  fs e
 -> TypeC  nil nil se sp fs  x   t  e    
 -> StepF  ss  sp  fs x  ss' sp' fs' x'   
 -> (exists se' e'
    ,  WfFS  se' sp' ss' fs'
    /\ LiveS ss' fs'    
    /\ LiveE fs' e'
    /\ SubsVisibleT  nil sp' sp  e  e'
    /\ TypeC nil nil se' sp' fs' x' t e').
Proof.
 intros se sp sp' ss ss' fs fs' x x' t e.
 intros HH HLS HLE HC HS. 
 gen t e.
 induction HS; intros.


 (*********************************************************)
 (* Pure evaluation. *)
 Case "SfStep". 
 { inverts_typec. 
   exists se. 
   exists e. 
   intuition.

   (* Original effect visibly subsumes effect of result. *)
   - apply subsVisibleT_refl.
     eauto.

   (* Resulting configuration is well typed. *)
   - eapply TcExp; eauto.
     eapply stepp_preservation; eauto.
 }


 (*********************************************************)
 (* Push let context. *)
 Case "SfLetPush".
 { exists se.
   exists e.
   intuition.
   
   (* Frame stack with new FLet frame is well formed. *)
   - inverts HH. split; auto.
     unfold StoreP in *. rip.
     + inverts H3. nope. eauto.
     + inverts H3. nope. eauto.
    
   (* All store bindings mentioned by frame stack are still live. *)
   - eapply liveS_push_flet; auto.

   (* Original effect visibly subsumes effect of result. *)
   - inverts_typec.
     eapply subsVisibleT_refl; eauto.

   (* Resulting configuation is well typed. *)
   - inverts_typec.
     eapply TcExp 
      with (t1 := t) (e1 := e0) (e2 := TSum e3 e2).
      + eapply EqTrans.
        * eapply EqSumAssoc; eauto.
        * auto.
      + auto.
      + eapply TfConsLet; eauto.
 }


 (*********************************************************)
 (* Pop let context and substitute. *)
 Case "SfLetPop".
 { exists se.
   exists e.
   intuition.

   (* Store is still well formed. *)
   - inverts HH. split; auto.
     unfold StoreP in *. 
     rip; firstorder.  

   (* After popping top FLet frame, effects of result are still 
      to live regions. *)
   - eapply liveE_pop_flet; eauto.

   (* Original effect visibly subsumes effect of result. *)
   - inverts_typec.
     eapply subsVisibleT_refl; eauto.

   (* Resulting configuration is well typed. *)
   - inverts_typec.
     eapply TcExp  
      with (t1 := t3) (e1 := e0) (e2 := e3).
      + eapply EqTrans.
        * eapply equivT_sum_left; auto.
          have (KindT nil sp e0 KEffect).
          have (KindT nil sp e3 KEffect).
          eapply KiSum; eauto.
        * auto.
      + eapply subst_val_exp; eauto.
      + auto.
 } 


 (*********************************************************)
 (* Create a private region. *)
 Case "SfPrivatePush".
 { inverts_typec.
   set (r := TRgn p).
   exists se.
   exists (TSum (substTT 0 r e0) (substTT 0 r e2)).

   have (SumKind KEffect).

   have (KindT (nil :> KRegion) sp e0 KEffect).

   have (KindT nil sp e1 KEffect)
    by  (eapply equivT_kind_left; eauto).
   have (ClosedT e1).

   have (KindT nil sp e2 KEffect)
    by  (eapply equivT_kind_left; eauto).
   have (ClosedT e2).
   intuition.

   (* All store bindings mentioned by resulting frame stack
      are still live. *)
   - inverts HH.
     subst p.
     eapply liveS_push_fpriv_none_allocRegion; eauto.

   (* Resulting effect is to live regions. *)
   - eapply liveE_sum_above.
     + eapply liveE_phase_change.

       have HLL: (liftTT 1 0 e1 = maskOnVarT 0 e0)
        by  (eapply lowerTT_some_liftTT; eauto).
       rrwrite (liftTT 1 0 e1 = e1) in HLL.

       have (SubsT nil sp e e1 KEffect) 
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs e1).

       have HLW: (LiveE (fs :> FPriv None p) e1).
       rewrite HLL in HLW.

       have HL0: (LiveE (fs :> FPriv None p) e0) 
        by (eapply liveE_maskOnVarT; eauto).

       trivial.

     + have (SubsT nil sp e e2 KEffect)
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs e2).
       have (LiveE (fs :> FPriv None p) e2).
       rrwrite (substTT 0 r e2 = e2); auto.
       
   (* Effect of result is subsumed by previous. *)
   - rrwrite ( TSum (substTT 0 r e0) (substTT 0 r e2)
             = substTT 0 r (TSum e0 e2)).
     have (ClosedT e).
     rgwrite (e = substTT 0 r e)
      by (symmetry; eauto).

     simpl.
     set (sp' := SRegion p <: sp).
     assert (SubsVisibleT nil sp' sp (substTT 0 r e) (substTT 0 r e0)).
     { have HE: (EquivT       nil sp' e (TSum e1 e2) KEffect)
        by (subst sp'; eauto).

       have HS: (SubsT        nil sp' e e1 KEffect)
        by (subst sp'; eauto).
      
       apply lowerTT_some_liftTT in H5.

       assert   (SubsVisibleT nil sp' sp (liftTT 1 0 e) (liftTT 1 0 e1)) as HV.
        rrwrite (liftTT 1 0 e  = e).
        rrwrite (liftTT 1 0 e1 = e1).
        eapply subsT_subsVisibleT.
        auto.
       rewrite H5 in HV.

       rrwrite (liftTT  1 0 e = e) in HV.
       rrwrite (substTT 0 r e = e).
       eapply subsVisibleT_mask; eauto.
     }

     assert (SubsVisibleT nil sp' sp (substTT 0 r e) (substTT 0 r e2)).
     { rrwrite (substTT 0 r e  = e).
       rrwrite (substTT 0 r e2 = e2).

       have HE: (EquivT nil sp' e (TSum e1 e2) KEffect)
        by (subst sp'; eauto).
        
       eapply SbEquiv in HE.
       eapply SbSumAboveRight in HE.
       eapply subsT_subsVisibleT. auto. auto.
     }
 
     unfold SubsVisibleT.
      simpl.
      apply SbSumAbove; auto.

   (* Result expression is well typed. *)
   - rrwrite (substTT 0 r e2 = e2).
     eapply TcExp 
       with (sp := SRegion p <: sp) 
            (t1 := substTT 0 r t0)
            (e1 := substTT 0 r e0)
            (e2 := substTT 0 r e2); auto.

     (* Type of result is equivlent to before *)
     + rrwrite (substTT 0 r e2 = e2).
       eapply EqRefl.
        eapply KiSum; auto.
         * eapply subst_type_type. 
            eauto.
            subst r. eauto.

     (* Type is preserved after substituting region handle. *)
     + rgwrite (nil = substTE 0 r nil).
       rgwrite (se  = substTE 0 r se)
        by (inverts HH; symmetry; auto).

       eapply subst_type_exp with (k2 := KRegion).
       * rrwrite (liftTE 0 nil = nil).
         rrwrite (liftTE 0 se  = se) 
          by (inverts HH; auto).
         auto.
       * subst r.
         eapply KiRgn.
         rgwrite (SRegion p <: sp = sp ++ (nil :> SRegion p)).
         eapply in_app_right; auto.

     (* New frame stack is well typed. *)
     + eapply TfConsPriv; eauto 2.

       (* Effect of frame stack is still to live regions *)
       * rrwrite (substTT 0 r e2 = e2).
         have    (SubsT nil sp e e2 KEffect) 
          by     (eapply EqSym in H0; eauto).
         eapply  liveE_subsT; eauto.

       (* Frame stack is well typed after substituting region handle.
          The initial type and effect are closed, so substituting
          the region handle into them doesn't do anything. *)
       * assert (ClosedT t0).
         { have HK: (KindT  (nil :> KRegion) sp t0 KData).
           eapply kind_wfT in HK.
           simpl in HK.

           have (~FreeT 0 t0) 
            by (eapply lowerTT_freeT; eauto).
           eapply freeT_wfT_drop; eauto.
         }

         rrwrite (substTT 0 r t0 = t0).
         rrwrite (substTT 0 r e2 = e2).
         rrwrite (t1 = t0)
          by (eapply lowerTT_closedT; eauto).
         eauto.
 }


 (*********************************************************)
 (* Pop a private region from the frame stack. *)
 Case "SfPrivatePop".
 { inverts_typec.

   (* We can only pop if there is at least on region in the store. *)
   destruct sp.

   (* No regions in store. *)
   - inverts HH. rip. 
     unfold StoreP in *. rip.
     have (In (FPriv None p) (fs :> FPriv None p)).
     have (In (SRegion p) nil) by firstorder.
     nope.

   (* At least one region in store. *)
   - destruct s.
     exists se.
     exists e2.
     intuition.

     (* Frame stack is still well formed after popping the top FUse frame *)
     + eapply wfFS_region_deallocate; auto.

     (* After popping top FUse,
        all store bindings mentioned by frame stack are still live. *)
     + eapply liveS_deallocRegion; eauto.

     (* New effect subsumes old one. *)
     + eapply subsT_subsVisibleT. 
       have (EquivT nil (sp :> SRegion n) e2 e KEffect).
       eauto.

     (* Resulting configuation is well typed. *)
     + eapply TcExp 
         with (sp := sp :> SRegion n)
              (e1 := TBot KEffect)
              (e2 := e2); eauto.

       eapply EqSym; eauto.
 }


 (*********************************************************)
 (* Push an extend frame on the stack. *)
 Case "SfExtendPush".
 { inverts_typec.
   set (r1 := TRgn p1).
   set (r2 := TRgn p2).
   exists se.
   exists (TSum (substTT 0 r2 e0) (TSum e2 (TAlloc r1))).
   intuition.
   
   (* Updated store is well formed. *)
   - inverts_kind. 
     eapply wfFS_push_priv_ext; auto.

   (* Updated store is live relative to frame stack. *)
   - inverts HH.
     subst p2.
     eapply liveS_push_fpriv_some_allocRegion; eauto.

     assert (SubsT nil sp e (TAlloc (TRgn p1)) KEffect).
     { have (SubsT nil sp e (TSum (TSum eL (TAlloc (TRgn p1))) e2) KEffect).
       eapply SbSumAboveLeft; eauto.
     }

     have (LiveE fs (TAlloc (TRgn p1))).
     eapply liveSP_from_effect; eauto.
      snorm.
     
   (* Frame stack is live relative to effect. *)
   - apply liveE_sum_above.
     + assert (ClosedT eL).
       { have (KindT nil sp (TSum (TSum eL (TAlloc (TRgn p1))) e2) KEffect).
         inverts_kind. eauto.
       }

       have HLL: (liftTT 1 0 eL = maskOnVarT 0 e0)
        by  (eapply lowerTT_some_liftTT; eauto).
       rrwrite (liftTT 1 0 eL = eL) in HLL.

       have (LiveE fs (TSum (TSum eL (TAlloc (TRgn p1))) e2))
        by (eapply liveE_equivT_left; eauto).
       have (LiveE fs eL).

       apply liveE_phase_change.

       have HLW: (LiveE (fs :> FPriv (Some p1) p2) eL).
       rewrite HLL in HLW.

       eapply liveE_maskOnVarT; eauto.

    + have (SubsT nil sp e (TSum (TSum eL (TAlloc (TRgn p1))) e2) KEffect).
      apply liveE_sum_above.
      * have (SubsT nil sp e e2 KEffect).
        eapply liveE_subsT; eauto.
      * have (SubsT nil sp e (TAlloc (TRgn p1)) KEffect).
        eapply liveE_subsT; eauto.
      
   (* Effect of result is subsumed by previous. *)
   - set (sp' := SRegion p2 <: sp).
     have (KindT nil sp    (TSum (TSum eL (TAlloc (TRgn p1))) e2) KEffect).
     have (SubsT nil sp' e (TSum (TSum eL (TAlloc (TRgn p1))) e2) KEffect)
      by (subst sp'; eapply subsT_stprops_snoc; eauto).

     inverts_kind.

     assert (SubsVisibleT nil sp' sp e (substTT 0 r2 e0)) as HE1.
     { eapply subsVisibleT_mask
        with (p := p2); auto.

       have HL: (liftTT 1 0 eL = maskOnVarT 0 e0)
        by (apply lowerTT_some_liftTT; auto).

       rewrite <- HL.
       rgwrite (liftTT 1 0 eL = eL).
       eapply subsT_subsVisibleT.
       eapply SbSumAboveLeft; eauto.
      }

     assert (SubsVisibleT nil sp' sp e e2)          as HE2.
     { eapply subsT_subsVisibleT.
       eapply SbSumAboveRight; eauto.
     }

     assert (SubsVisibleT nil sp' sp e (TAlloc r1)) as HE3.
     { subst r1.
       eapply subsT_subsVisibleT.
       eapply SbSumAboveLeft; eauto.
     }
     eauto.

   (* Resulting state is well typed. *)
   - eapply TcExp
       with (e1 := substTT 0 r2 e0)
            (e2 := TSum e2 (TAlloc r1))
            (t1 := substTT 0 r2 t0).
     (* Equivalence of result effect *)
     + eapply EqRefl.
       eapply KiSum; auto.
       * subst r2.
         have (KindT (nil :> KRegion) sp                 e0 KEffect).
         have (KindT (nil :> KRegion) (SRegion p2 <: sp) e0 KEffect).
         have (KindT nil (SRegion p2 <: sp) (TRgn p2) KRegion).
         eapply subst_type_type. eauto. eauto.
       * apply equivT_kind_left in H0.
         inverts_kind. subst r1.
         eapply KiSum; auto.
         eapply KiCon1. snorm. eauto.
   
     (* Expression with new region subst is well typed. *)
     + rgwrite (nil = substTE 0 r2 nil).
       rgwrite (se  = substTE 0 r2 se)
        by (inverts HH; symmetry; auto).

       eapply subst_type_exp.
       * eapply typex_stprops_snoc.
         rgwrite (nil = liftTE 0 nil).
         rgwrite (se  = liftTE 0 se)
          by (inverts HH; symmetry; auto).
         eauto.
       * subst r2. eauto.

     (* Extended frame stack is well typed. *)
     + have (KindT (nil :> KRegion) sp t0 KData).
       have (not (In (SRegion p2) sp))
        by (subst p2; auto).
       eapply TfConsExt; eauto.
       * inverts_kind. eauto.
       * eapply typeF_freshSuppFs; eauto.
       * have (LiveE fs (TSum (TSum eL (TAlloc (TRgn p1))) e2))
          by (eapply liveE_equivT_left; eauto).
         eapply liveE_sum_above.
          eapply liveE_sum_above_right; eauto.
          eapply liveE_sum_above_left  in H4.
          eapply liveE_sum_above_right in H4.
          trivial.
       * erewrite mergeT_substTT.
         eapply typeF_stprops_snoc. auto.
         eauto. eauto.
  }

 (*********************************************************)
 (* Pop and extend frame from the stack, 
    and merge the new region with the old one. *)
 Case "SfExtendPop".
 { inverts_typec.
   set (r1 := TRgn p1).
   set (r2 := TRgn p2).
   exists (mergeTE p1 p2 se).
   exists e0.
   intuition.

   (* Updated store is well formed. *)
   - rrwrite (map (mergeB p1 p2) ss = mergeBs p1 p2 ss).
     eapply wfFS_pop_priv_ext; eauto.
    
   (* Updated store is live relative to frame stack. *)
   - SCase "LiveS".
     eapply liveS_mergeB.
     + have (LiveSF ss (FPriv (Some p1) p2)).
       unfold LiveSF in H0.
       unfold LiveSP. intros.
       eapply H0 in H1. inverts H1. auto.
     + have (LiveS ss fs).
       auto.

   (* Frame stack is live relative to effect. *) 
   - SCase "LiveE".
     eapply liveE_sum_above_left; eauto.

   (* Effect of result is subsumed by previous. *)
   - SCase "SubsVisibleT".
     eapply subsT_subsVisibleT.
     set (e' := (TSum (TBot KEffect) (TSum e0 (TAlloc (TRgn p1))))).
     have (KindT  nil sp e'   KEffect).
     have (EquivT nil sp e e' KEffect).
     eapply SbSumAboveRight; eauto.

   (* Resulting state is well typed. *)
   - SCase "TypeC".
     eapply TcExp
       with (t1 := mergeT p1 p2 t1)
            (e1 := TBot KEffect)
            (e2 := e0).

     (* Equivalence of result effect. *)
     + have (KindT nil sp (TSum (TBot KEffect) 
                          (TSum e0 (TAlloc (TRgn p1)))) KEffect).
       inverts_kind.
       eapply EqSym; eauto.

     (* Result value is well typed. *)
     + rgwrite (nil                    = mergeTE p1 p2 nil).
       rgwrite (XVal (mergeV p1 p2 v1) = mergeX  p1 p2 (XVal v1)).
       rgwrite (TBot KEffect           = mergeT  p1 p2 (TBot KEffect)).
       eapply mergeX_typeX. auto. eauto.

     (* Popped frame stack is well typed. *)
     + rgwrite (nil = mergeTE p1 p2 nil).
       eapply typeF_mergeTE; eauto.
 }

 (*********************************************************)
 (* Allocate a reference. *)
 Case "SfStoreAlloc".
 { inverts HC.
   inverts H0.
   exists (TRef   (TRgn p1) t2 <: se).
   exists e2.
   intuition.

   (* Store is well formed after adding a binding. *)
   - remember (TRgn p1) as r.

     have (SubsT nil sp e (TAlloc r) KEffect)
      by  (eapply EqSym in H; eauto).

     have (LiveE fs (TAlloc r)).
     subst r.

     eapply wfFS_stbind_snoc; auto.
     inverts_kind. auto.

   (* Resulting effects are to live regions. *)
   - have  (SubsT nil sp e e2 KEffect)
      by   (eapply EqSym in H; eauto).
     eapply liveE_subsT; eauto.

   (* Original effect visibly subsumes resulting one. *)
   - eapply EqSym in H.
      eapply subsT_subsVisibleT; eauto.
      eauto. eauto.

   (* Resulting configuation is well typed. *)
   - eapply TcExp
      with (t1 := TRef (TRgn p1) t2)
           (e1 := TBot KEffect)
           (e2 := e2).
     + eapply EqSym.
        * eauto. 
        * eapply KiSum; eauto.
        * eapply equivT_sum_left; eauto.
     + eapply TxVal.
       eapply TvLoc.
        have    (length se = length ss).
        rrwrite (length ss = length se).
        eauto. eauto.
     + eapply typeF_stenv_snoc; eauto.
 }


 (*********************************************************)
 (* Read from a reference. *)
 Case "SfStoreRead".
 { inverts HC.
   exists se.
   exists e2. 
   intuition.

   (* Resulting effects are to live regions. *)
   - have  (SubsT nil sp e e2 KEffect)
      by   (eapply EqSym in H0; eauto).
     eapply liveE_subsT; eauto.

   (* Original effect visibly subsumes resulting one. *)
   - eapply EqSym in H0.
      eapply subsT_subsVisibleT; eauto.
      eauto. eauto.

   (* Resulting configutation is well typed. *)
   - eapply TcExp
      with (t1 := t1)
           (e1 := TBot KEffect)
           (e2 := e2).
     + eapply EqSym; eauto.
     + inverts H1.
       inverts H12.
       eapply TxVal.
        inverts HH. rip.
        eapply storet_get_typev; eauto.
     + eauto.
 }


 (*********************************************************)
 (* Write to a reference. *)
 Case "SfStoreWrite".
 { inverts HC.
   exists se.
   exists e2.
   intuition.

   (* Resulting store is well formed. *)
   - inverts_type.
     eapply wfFS_stbind_update; eauto.
     inverts_kind; auto.

   (* All store bindings mentioned by frame stack are still live. *)
   - eapply liveS_stvalue_update.
     + inverts_type.
       remember (TRgn p) as r.

       have (SubsT nil sp e (TWrite r) KEffect)
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs (TWrite r))
        by  (eapply liveE_subsT; eauto).

       eapply liveE_fpriv_in with (e := TWrite r).
       * subst r. snorm. 
       * subst r. snorm.
     + auto.

   (* Resulting effects are to live regions. *)
   - have  (SubsT nil sp e e2 KEffect)
      by   (eapply EqSym in H0; eauto).
     eapply liveE_subsT; eauto.

   (* Original effect visibly subsumes resulting one. *)
    - eapply EqSym in H0.
      eapply subsT_subsVisibleT; eauto.
       eauto. eauto.

   (* Resulting configuration is well typed. *)
   - eapply TcExp
      with (t1 := t1)
           (e1 := TBot KEffect)
           (e2 := e2).
     + eapply EqSym; eauto.
     + inverts_type.
       eapply TxVal.
        inverts HH. rip.
     + eauto.
 }
Qed.

