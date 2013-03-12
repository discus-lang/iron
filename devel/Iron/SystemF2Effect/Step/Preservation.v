
Require Export Iron.SystemF2Effect.Step.TfJudge.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp sp' ss ss' fs fs' x x' t e
 ,  WfFS   se sp ss fs 
 -> TYPEC  nil nil se sp fs  x   t  e
 -> STEPF  ss  sp fs  x ss' sp' fs' x'
 -> (exists se' e'
            ,  extends se' se
            /\ WfFS         se' sp' ss' fs'
            /\ SubsVisibleT nil sp e e'
            /\ TYPEC nil nil se' sp' fs' x' t e').
Proof.
 intros se sp sp' ss ss' fs fs' x x' t e.
 intros HH HC HS. 
 gen t e.
 induction HS; intros.

 (* Pure evaluation. *)
 Case "SfStep". 
 { inverts_typec. 
   exists se. 
   exists e.
   rip.
   - apply subsT_visible_refl.
     eauto.
   - eapply TcExp; eauto.
     eapply stepp_preservation; eauto.
     inverts HH. rip.
 }

 (* Push let context. *)
 Case "SfLetPush".
  admit.                                                   (* Case SfLetPush *)

 (* Pop let context and substitute. *)
 Case "SfLetPop".
  admit.                                                   (* Case SfLetPop *)

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

   (* Effect of result is subsumed by previous. *)
   - eapply SbTrans
      with (t2 := TSum (substTT 0 r e1) (substTT 0 r e2)).
     + eauto.

     + eapply KiSum.
        eauto.
        rrwrite (substTT 0 r e1 = e1); auto.
        rrwrite (substTT 0 r e2 = e2); auto.

     + simpl.
       eapply KiSum.
       * eauto.
       * admit.               (* ok, not visible *)
       * eapply maskOnT_kind.
         rrwrite (substTT 0 r e2 = e2); auto.

     + eapply SbEquiv.
        rrwrite (substTT 0 r e1 = e1); auto.
        rrwrite (substTT 0 r e2 = e2); auto.
        eapply EqSym.
         eapply equivT_kind_right; eauto.
         eauto.
        auto.

     + eapply subsT_sum_merge; fold maskOnT.
       * eauto.

       (* Push e0 through region phase change relation. *)  
       * have    (ClosedT r) by (subst r; eauto).
         rrwrite (substTT 0 r e1 = e1).

         admit.                                            (* need maskOnVar/maskOnCap link *)

(*       Probably don't need this stuff.
         assert (substTT 0 r e0 = liftTT 1 0 (substTT 0 r e0)) as HS.
         { assert (WfT 1 e0).
           { have HK: (KindT (nil :> KRegion) sp e0 KEffect).
             have HE: (WfT  (length (nil :> KRegion)) e0) 
              by (eapply kind_wfT; eauto).
             simpl in HE.
             trivial.
           }
           have (ClosedT (substTT 0 r e0)) by (eapply substTT_closing; eauto).
           eapply substTT_liftTT_wfT1; eauto.
         }
         rewrite HS. clear HS.
*)        

       (* Push e2 though region phase change relation. *)
       * have    (ClosedT r)  by (subst r; eauto).
         rrwrite (substTT 0 r e2 = e2).
         eapply maskOnT_subsT. eauto.

   (* Result expression is well typed. *)
   - rrwrite (substTT 0 r e2 = e2).
     eapply TcExp 
       with (sp := sp :> SRegion p) 
            (t1 := substTT 0 r t0)
            (e1 := substTT 0 r e0)
            (e2 := substTT 0 r e2); auto.

     (* Type of result is equivlent to before *)
     + rrwrite (substTT 0 r e2 = e2).
       eapply EqRefl.
        eapply KiSum; auto.
         * eapply subst_type_type. eauto.
           subst r. eauto.
         * eapply kind_stprops_cons. auto.

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

     (* New frame stack is well typed. *)
     + eapply TfConsUse.

       (* New region handle is not in the existing frame stack. *)
       * unfold not. intros.

         have (In (SRegion p) sp)
          by (eapply wfFS_fuse_sregion; eauto).

         have (not (In (SRegion (allocRegion sp)) sp)).
         have (In (SRegion p) sp).
         rewrite H in H14. tauto.

       * rrwrite (substTT 0 r e2 = e2).
         have    (ClosedT t0)           by admit.          (* ok, t0 does not mention ^0 via lowerTT *)
         rrwrite (substTT 0 r t0 = t0).
         rrwrite (t0 = t1)              by admit.          (* ok, lowering closed type is identity *)
         admit.                                            (* need weaken stprops in typef *)
 }

 (* Pop a region from ths stack. *)
 Case "SfRegionPop".
 { inverts_typec.

   (* We can only pop if there is at least on region in the store. *)
   destruct sp.

   (* No regions in store. *)
   - inverts HH. rip. 
     unfold STOREP in *.
     spec H4 p.
     have (In (FUse p) (fs :> FUse p)).
      rip. nope.

   (* At least one region in store. *)
   - destruct s.
     exists se.
     exists e2.
     rip.
     (* Frame stack is still well formed after popping the top FUse frame *)
     + eapply wfFS_stack_pop; eauto.

     (* New effect subsumes old one. *)
     + eapply subsT_visible_equiv.
       have HE: (EquivT nil (sp :> SRegion n) e2 e KEffect).
       eauto.

     (* Resulting configuation is well typed. *)
     + eapply TcExp 
         with (sp := sp :> SRegion n)
              (e1 := TBot KEffect)
              (e2 := e2); eauto.

       eapply EqSym; eauto.
 }


 (* Allocate a reference. *)
 Case "SfStoreAlloc".
  admit.                                                   (* Case SfStoreAlloc *)
 
 (* Read from a reference. *)
 Case "SfStoreRead".
  admit.                                                   (* Case SfStoreRead *)

 (* Write to a reference. *)
 Case "SfStoreWrite".
  admit.                                                   (* Case SfStoreWrite *)
Qed.

