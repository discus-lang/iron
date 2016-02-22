
Require Export Iron.Language.DelayedSimpleUS.Step.


(* If a well typed expression takes an evaluation step 
   then the result has the same type as before. *)
Theorem preservation
 :  forall te x x' t
 ,  TypeX  te x  t
 -> Step   x  x'
 -> TypeX  te x' t.
Proof.
 intros te x x' t HT HS. gen t x'.
 induction x.

 - Case "XVar". 
   intros. inverts HS.

 - Case "XAbs".
   intros. inverts HS.

 - Case "XApp".
   intros.
   inverts HS.
   + SCase "functional expression steps".
     inverts_type.
     eapply TxApp; eauto.

   + SCase "argument steps".
     inverts_type.
     eapply TxApp; eauto.

   + SCase "perform a substitution".
     inverts_type.
     eapply subst_exp_exp.
     * simpl. assumption.
     * unfold ForallSubstXT. simpl.
       eapply Forall2_cons; auto.
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

