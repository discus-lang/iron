
Require Export Iron.SystemF2Effect.Step.TypeC.
Require Export Iron.SystemF2Effect.Type.Operator.FreeTT.
Require Export Iron.SystemF2Effect.Store.LiveS.
Require Export Iron.SystemF2Effect.Store.LiveE.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp sp' ss ss' fs fs' x x' t e
 ,  WfFS   se sp ss  fs
 -> LiveS ss fs -> LiveE  fs e
 -> TYPEC  nil nil se sp fs  x   t  e    
 -> STEPF  ss  sp  fs x  ss' sp' fs' x'   
 -> (exists se' e'
    ,  extends se' se
    /\ WfFS  se' sp' ss' fs'
    /\ LiveS ss' fs'    
    /\ LiveE fs' e'
    /\ SubsVisibleT  nil sp' sp  e  e'
    /\ TYPEC nil nil se' sp' fs' x' t e').
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
   rip.

   (* Original effect visibly subsumes effect of result. *)
   - apply subsVisibleT_refl.
     eauto.

   (* Resulting configuration is well typed. *)
   - eapply TcExp; eauto.
     eapply stepp_preservation; eauto.
     inverts HH. rip.
 }


 (*********************************************************)
 (* Push let context. *)
 Case "SfLetPush".
 { exists se.
   exists e.
   rip. 

   (* Frame stack with new FLet frame is well formed. *)
   - unfold WfFS in *. rip.
     unfold STOREP in *. rip.
     eapply H3.
     inverts H2.
     + nope.
     + auto.
    
   (* All store bindings mentioned by frame stack are still live. *)
   - eapply liveS_push_fLet; auto.

   (* Original effect visibly subsumes effect of result. *)
   - eapply subsVisibleT_refl. 
     inverts HC; eauto.

   (* Resulting configuation is well typed. *)
   - inverts HC.
     inverts H0.
     eapply TcExp 
      with (t1 := t) (e1 := e0) (e2 := TSum e3 e2).
      + eapply EqTrans.
         eapply EqSumAssoc; eauto.
         auto.
      + auto.
      + eapply TfConsLet; eauto.
(*        * inverts HH. rip. *)
 }


 (*********************************************************)
 (* Pop let context and substitute. *)
 Case "SfLetPop".
 { exists se.
   exists e.
   rip.

   (* Store is still well formed. *)
   - unfold WfFS in *. rip.
     unfold STOREP in *. rip.

   (* After popping top FLet frame, 
      all store bindings mentioned by frame stack are still live. *)
   - eapply liveS_pop_fLet; eauto.

   (* After popping top FLet frame, effects of result are still 
      to live regions. *)
   - eapply liveE_pop_flet; eauto.

   (* Original effect visibly subsumes effect of result. *)
   - eapply subsVisibleT_refl.
     inverts HC; eauto.

   (* Resulting configuration is well typed. *)
   - inverts HC.
     inverts H1.
     eapply TcExp  
      with (t1 := t3) (e1 := e0) (e2 := e3).
      + inverts H0.
        subst.
        eapply EqTrans.
        * eapply equivT_sum_left. eauto.
          have (KindT nil sp e0 KEffect).
          have (KindT nil sp e3 KEffect).
          eauto.
        * auto.
      + eapply subst_val_exp. 
        * eauto.
        * inverts H0. auto.
      + eauto.
 } 


 (*********************************************************)
 (* Create a new region. *)
 Case "SfRegionNew".
 { inverts_typec.
   set (r := TCap (TyCapRegion p)).
   exists se.
   exists (TSum (substTT 0 r e0) (substTT 0 r e2)).

   have (sumkind KEffect).

   have (KindT (nil :> KRegion) sp e0 KEffect).

   have (KindT nil sp e1 KEffect)
    by  (eapply equivT_kind_left; eauto).
   have (ClosedT e1).

   have (KindT nil sp e2 KEffect)
    by  (eapply equivT_kind_left; eauto).
   have (ClosedT e2).

   rip.

   (* All store bindings mentioned by resulting frame stack
      are still live. *)
   - inverts HH. rip.
     subst p.
     eapply liveS_push_fUse_fresh; eauto.

   (* Resulting effect is to live regions. *)
   - eapply liveE_sum_above.
     + have HLL: (liftTT 1 0 e1 = maskOnVarT 0 e0)
        by  (eapply lowerTT_some_liftTT; eauto).
       rrwrite (liftTT 1 0 e1 = e1) in HLL.

       have (SubsT nil sp e e1 KEffect) 
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs e1).

       have HLW: (LiveE (fs :> FUse p) e1).
       rewrite HLL in HLW.

       have HL0: (LiveE (fs :> FUse p) e0) 
        by (eapply liveE_maskOnVarT; eauto).

       eapply liveE_phase_change; eauto.

     + have (SubsT nil sp e e2 KEffect)
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs e2).
       have (LiveE (fs :> FUse p) e2).
       rrwrite (substTT 0 r e2 = e2); auto.
       
   (* Effect of result is subsumed by previous. *)
   - rrwrite ( TSum (substTT 0 r e0) (substTT 0 r e2)
             = substTT 0 r (TSum e0 e2)).
     have (ClosedT e).
     have HE: (substTT 0 r e = e). rewrite <- HE. clear HE.

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
         * eapply subst_type_type. eauto.
           subst r. eauto.

     (* Type is preserved after substituting region handle. *)
     + have HTE: (nil = substTE 0 r nil).
       rewrite HTE.

       have HSE: (se  = substTE 0 r se)
        by (inverts HH; symmetry; auto).
       rewrite HSE.

       eapply subst_type_exp with (k2 := KRegion).
       * rrwrite (liftTE 0 nil = nil).
         rrwrite (liftTE 0 se  = se) by (inverts HH; auto).
         auto.
       * subst r. auto.
         eapply KiCap.
          rrwrite (SRegion p <: sp = sp ++ (nil :> SRegion p)).
          eapply in_app_right. snorm.

     (* New frame stack is well typed. *)
     + eapply TfConsUse.

       (* New region handle is not in the existing frame stack. *)
       * unfold not. intros.

         have (In (SRegion p) sp)
          by (eapply wfFS_fuse_sregion; eauto).

         have (not (In (SRegion (allocRegion sp)) sp)).
         have (In (SRegion p) sp).
         rewrite H in H14. tauto.

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

           have (freeTT 0 t0 = false) by (eapply lowerTT_freeT; eauto).
           eapply freeTT_wfT_drop; eauto.
         }

         rrwrite (substTT 0 r t0 = t0).
         rrwrite (substTT 0 r e2 = e2).
         rrwrite (t1 = t0) by (eapply lowerTT_closedT; eauto).
         eauto.
 }


 (*********************************************************)
 (* Pop a region from the frame stack. *)
 Case "SfRegionPop".
 { inverts_typec.

   (* We can only pop if there is at least on region in the store. *)
   destruct sp.

   (* No regions in store. *)
   - inverts HH. rip. 
     unfold STOREP in *.
     spec H5 p.
     have (In (FUse p) (fs :> FUse p)).
      rip. nope.

   (* At least one region in store. *)
   - destruct s.
     exists se.
     exists e2.
     rip.
     (* Frame stack is still well formed after popping the top FUse frame *)
     + eapply wfFS_region_deallocate; auto.

     (* After popping top FUse,
        all store bindings mentioned by frame stack are still live. *)
     + eapply liveS_deallocate; eauto.

     (* New effect subsumes old one. *)
     + eapply subsT_subsVisibleT.
       have HE: (EquivT nil (sp :> SRegion n) e2 e KEffect).
       eauto.

     (* Resulting configuation is well typed. *)
     + eapply TcExp 
         with (sp := sp :> SRegion n)
              (e1 := TBot KEffect)
              (e2 := e2); eauto.

       eapply EqSym; eauto.
 }


 (*********************************************************)
 (* Allocate a reference. *)
 Case "SfStoreAlloc".
 { inverts HC.
   inverts H0.
   exists (TRef   (TCap (TyCapRegion r1)) t2 <: se).
   exists e2.
   rip.

   (* All store bindings mentioned by frame stack are still live. *)
   - remember (TCap (TyCapRegion r1)) as p.

     have (SubsT nil sp e (TAlloc p) KEffect)
      by  (eapply EqSym in H; eauto).

     have (LiveE fs (TAlloc p)).

     assert (In (FUse r1) fs).
      eapply liveE_fUse_in; eauto.
      subst p. simpl. auto.
     
     eapply liveS_stvalue_snoc; auto.

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
      with (t1 := TRef (TCap (TyCapRegion r1)) t2)
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
     + eauto.
 }


 (*********************************************************)
 (* Read from a reference. *)
 Case "SfStoreRead".
 { inverts HC.
   exists se.
   exists e2. 
   rip.

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
   rip.

   (* Resulting store is well formed. *)
   - inverts_type.
     eapply wfFS_stbind_update; eauto.

   (* All store bindings mentioned by frame stack are still live. *)
   - eapply liveS_stvalue_update.
     + inverts_type.
       remember (TCap (TyCapRegion r)) as p.

       have (SubsT nil sp e (TWrite p) KEffect)
        by  (eapply EqSym in H0; eauto).

       have (LiveE fs (TWrite p))
        by  (eapply liveE_subsT; eauto).

       eapply liveE_fUse_in with (e := TWrite p).
        subst p. snorm. eauto.

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

