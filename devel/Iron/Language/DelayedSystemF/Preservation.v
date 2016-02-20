
Require Export Iron.Language.DelayedSystemF.Step.


(* If a well typed expression takes an evaluation step 
   then the result has the same type as before. *)
Theorem preservation
 :  forall ke te x x' t
 ,  TypeX  ke te x  t
 -> Step   x  x'
 -> TypeX  ke te x' t.
Proof.
 intros ke te x x' t HT HS. gen t x'.
 induction x.

 - Case "XVar". 
   intros. inverts HS.

 - Case "XAbs".
   intros. inverts HS.

 - Case "XApp".
   intros.
   inverts HS.
   + SCase "x1 steps".
     inverts_type.
     eapply TxApp; eauto.

   + SCase "x2 steps".
     inverts_type.
     eapply TxApp; eauto.

   + SCase "substitute x2".
     inverts_type.
     eapply subst_exp_exp.
     * simpl. assumption.
     * unfold ForallSubstXT. simpl.
       eapply Forall2_cons; auto.

 - Case "XABS".
   intros. inverts HS.

 - Case "XAPP".
   intros.
   inverts HS.
   + SCase "x1 steps".
     inverts_type.
     eapply TxAPP; eauto.

   + SCase "substitute t2".
     inverts_type.
     (* need subst_type_exp lemma *)

Qed.


(* If a well typed expression takes several evaluation steps
   then the result has the same type as before. *)
Lemma preservation_steps
 :  forall te x1 t1 x2
 ,  TypeX  te x1 t1
 -> Steps     x1 x2
 -> TypeX  te x2 t1.
Proof.
 intros te x1 t1 x2 HT HS.
 induction HS.
 - assumption.
 - eapply preservation; eauto.
 - eapply IHHS. eapply preservation; eauto.
Qed.


(* If a closed, well typed expression takes several evaluation steps
   then the result has the same type as before. 
   Usses the left linearised version of steps judement. *)
Lemma preservation_stepsl
 :  forall te x1 t1 x2
 ,  TypeX  te x1 t1
 -> StepsL    x1 x2
 -> TypeX  te x2 t1.
Proof.
 intros te x1 t1 x2 HT HS.
 induction HS; eauto using preservation.
Qed.

