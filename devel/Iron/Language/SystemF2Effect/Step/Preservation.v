
Require Export Iron.Language.SystemF2Effect.Step.TfJudge.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp ss ss' fs fs' x x' t e
 ,  WfFS   se sp ss fs 
 -> TYPEC  nil nil se sp fs  x   t  e
 -> STEPF  ss  fs  x  ss' fs' x'
 -> (exists se' sp' e'
            ,  extends se' se
            /\ WfFS  se' sp' ss' fs'
            /\ SubsT e e'
            /\ TYPEC nil nil se' sp' fs' x' t e').
Proof.
 intros se sp ss ss' fs fs' x x' t e HH HC HS. gen sp t e.
 induction HS; intros.

 (* Pure evaluation. *)
 Case "SfStep". 
 { inverts_typec. 
   exists se. 
   exists sp. 
   exists e.
   rip.
   eapply TcExp; eauto.
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
   exists (sp :> SRegion p).
   exists (substTT 0 r e).
   rip.

   admit. (* ok, e2 has no vars because it's typed under empty kienv
                 e1 has no vars because it comes from  masked e0 
                    and there was only one possible var in e0 (which was masked) *)

   (* Result is well typed. *)
   + eapply TcExp 
       with (sp := sp :> SRegion p) 
            (t1 := substTT 0 r t0)
            (e1 := substTT 0 r e0)
            (e2 := substTT 0 r e2); auto.

      admit. (* ok, equiv preserved by subst *) 

     (* Type is preserved after substituting region handle. *)
     - have HTE: (nil = substTE 0 r nil).
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
     - eapply TfConsUse.
       admit.                  (* ok, region handle is fresh, goodness of allocRegionFs *)
       admit.                  (* ok, t0 doesn't mention ^0 by lowerTT *)
 }

 (* Pop a region from ths stack. *)
 Case "SfRegionPop".
 { inverts_typec.

   (* We can only pop if there is at least on region in the store. *)
   destruct sp.
   (* No regions in store. *)
   + inverts HH. rip. 
     unfold STOREP in *.
     spec H4 p.
     have (In (FUse p) (fs :> FUse p)).
      inverts H4. rip. nope.

   (* At least one region in store. *)
   + destruct s.
     exists se.
     exists (sp :> SRegion n).
     exists e2.
     rip.
     - admit.  (* CHANGE to allow store well formed under smaller frame stack *)
     - admit.  (* ok, effect subst, bot *)

     (* Resulting configuation is well typed. *)
     - eapply TcExp 
         with (sp := sp :> SRegion n)
              (e1 := TBot KEffect)
              (e2 := e2).
       admit.         (* ok, effect equiv *)
       eapply TxVal.
        eauto.
       eauto.
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

