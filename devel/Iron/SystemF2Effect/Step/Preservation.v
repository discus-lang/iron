
Require Export Iron.SystemF2Effect.Step.TfJudge.


Definition subsT_visible sp e e'
 := SubsT KEffect e (maskOnCap (fun r => negb (hasSRegion r sp)) e').


Lemma subsT_maskOnCap
 :  forall p e1 e2
 ,  SubsT  KEffect e1 e2
 -> SubsT  KEffect e1 (maskOnCap p e2).
Proof. admit. Qed.


Lemma subsT_visible_refl
 :  forall sp e
 ,  subsT_visible sp e e.
Proof.
 intros.
 unfold subsT_visible.
  eapply subsT_maskOnCap.
  auto.
Qed.


Lemma subsT_visible_equiv
 :  forall sp e1 e2
 ,  SubsT KEffect e1 e2
 -> subsT_visible sp e1 e2.
Proof.
 intros.
 unfold subsT_visible.
  eapply subsT_maskOnCap.
  auto.
Qed.


Lemma subsT_phase_change
 :  forall sp p r e1 e2
 ,  hasSRegion p sp = false
 -> r               = TCap (TyCapRegion p)
 -> SubsT KEffect e1 e2
 -> subsT_visible sp e1 (liftTT 1 0 (substTT 0 r e2)).
Proof.
 admit.
Qed.



(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp sp' ss ss' fs fs' x x' t e
 ,  WfFS   se sp ss fs 
 -> TYPEC  nil nil se sp fs  x   t  e
 -> STEPF  ss  sp fs  x ss' sp' fs' x'
 -> (exists se' e'
            ,  extends se' se
            /\ WfFS  se' sp' ss' fs'
            /\ subsT_visible sp e e'
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
   - eapply TcExp; eauto.
     eapply stepp_preservation; eauto.
     inverts HH. rip.
 }

 (* Push let context. *)
 Case "SfLetPush".
  admit.

 (* Pop let context and substitute. *)
 Case "SfLetPop".
  admit.

 (* Create a new region. *)
 Case "SfRegionNew".
 { inverts_typec.
   set (r := TCap (TyCapRegion p)).
   exists se.
   exists (TSum (substTT 0 r e0) (substTT 0 r e2)).
   rip.

   (* Effect of result is subsumed by previous. *)
   - eapply SbTrans.
     + eapply SbEquiv.
       eapply EqSym. eauto.
     + simpl.
       eapply subsT_sum_merge.

       (* Push e0 through region phase change relation. *)  
       * assert (substTT 0 r e0 = liftTT 1 0 (substTT 0 r e0)) as HS.
         { assert (wfT 1 e0).
           { have HK: (KIND (nil :> KRegion) sp e0 KEffect).
             have HE: (wfT  (length (nil :> KRegion)) e0) 
              by (eapply kind_wfT; eauto).
             simpl in HE.
             trivial.
           }
           have (closedT r) 
             by (subst r; eauto).

           have (closedT (substTT 0 r e0)) 
             by (eapply substTT_closing; eauto).

           eapply substTT_liftTT_wfT1; eauto.
          }
          rewrite HS. clear HS.

         eapply subsT_phase_change with (p := p); auto.
          admit.                                          (* ok, e1 has no free vars *)

       (* Push e2 though region phase change relation. *)
       * assert (substTT 0 r e2 = liftTT 1 0 (substTT 0 r e2)) as HS.
         { have (wfT (@length ki nil) e2)  by eauto.
           have (closedT r)                by (subst r; eauto).
           have (closedT (substTT 0 r e2)) by (eapply substTT_closing; eauto).
           eapply substTT_liftTT_wfT1; eauto.
         }
         rewrite HS. clear HS.

         eapply subsT_phase_change with (p := p); auto.

   (* Result expression is well typed. *)
   -  have HW: (wfT (@length ki nil) e2) by eauto.
       simpl in HW.
      have HE2: (substTT 0 r e2 = e2).
      rewrite HE2.

     eapply TcExp 
       with (sp := sp :> SRegion p) 
            (t1 := substTT 0 r t0)
            (e1 := substTT 0 r e0)
            (e2 := substTT 0 r e2); auto.

     (* Type of result is equivlent to before *)
     + rewrite HE2. auto.

     (* Type is preserved after substituting region handle. *)
     + have HTE: (nil = substTE 0 r nil).
       rewrite HTE.

       have HSE: (se  = substTE 0 r se)
        by (inverts HH; symmetry; auto).
       rewrite HSE.

       eapply subst_type_exp with (k2 := KRegion).
       * rrwrite (liftTE 0 nil    = nil).
         rrwrite (liftTE 0 se = se) by (inverts HH; auto).
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
         rewrite H in H7. tauto.

       * admit.                                      (* ok, t0 doesn't mention ^0 by lowerTT *)
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
     + eapply subsT_visible_equiv. eauto. 

     (* Resulting configuation is well typed. *)
     + eapply TcExp 
         with (sp := sp :> SRegion n)
              (e1 := TBot KEffect)
              (e2 := e2); eauto.
 }


 (* Allocate a reference. *)
 Case "SfStoreAlloc".
  admit.
 
 (* Read from a reference. *)
 Case "SfStoreRead".
  admit.

 (* Write to a reference. *)
 Case "SfStoreWrite".
  admit.
Qed.

