
Require Export Iron.SystemF2Effect.Step.TfJudge.

Fixpoint elem {A} (p : A -> bool) (xx : list A)
 := match xx with
    | nil      => false
    | x :: xs  => if p x then true else elem p xs
    end.


Definition isSRegion (r : nat) (pp : stprop) : bool
 := match pp with
    | SRegion r' => beq_nat r r'
    end.


Definition hasSRegion (r : nat) (sp : stprops) 
 := elem (isSRegion r) sp.


Definition subsT_visible sp e e'
 := SubsT e (maskOnCap (fun r => negb (hasSRegion r sp)) e').


Lemma subsT_maskOnCap
 :  forall p e1 e2
 ,  SubsT e1 e2
 -> SubsT e1 (maskOnCap p e2).
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
 ,  SubsT e1 e2
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
 -> SubsT e1 e2
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
       * have (substTT 0 r e0 = liftTT 1 0 (substTT 0 r e0)) by admit. (* no vars in subst result *)
          rewrite H1. clear H1.
         eapply subsT_phase_change with (p := p).
          admit.                   (* ok, p not in sp, by goodness of allocRegionFs *)
          subst r. auto.
          admit.                   (* ok, e1 has no free vars *)

       * have (substTT 0 r e2 = liftTT 1 0 (substTT 0 r e2)) by admit. (* no vars in subst result *)
          rewrite H1. clear H1.
         eapply subsT_phase_change with (p := p).
          admit.                   (* ok, p not in sp, by goodness of allocRegionFs *)      
          subst r.  auto.
          auto.
          
   -  have HE2: (substTT 0 r e2 = e2) by admit.  (* e2 has no vars as under empty kienv *)
      rewrite HE2. auto.

   (* Result is well typed. *)
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
       admit.            (* ok, region handle is fresh, goodness of allocRegionFs *)
       admit.            (* ok, t0 doesn't mention ^0 by lowerTT *)
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
      inverts H4. rip. nope.

   (* At least one region in store. *)
   - destruct s.
     exists se.
     exists e2.
     rip.
     + admit.  (* CHANGE to allow store well formed under smaller frame stack *)

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

