
Require Export Iron.Language.DelayedSystemF.Step.


(* A well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall ke te x t
 ,  TypeX  ke te x t
 -> Done x \/ (exists x', Step x x').
Proof.
 intros. gen t.
 induction x using exp_iind; intros.

 - Case "XVar is done".
   left. auto.

 - Case "XLam is done".
   left. auto.

 - Case "XApp".
   inverts_type.

   assert (Done x1 \/ (exists x1', Step x1 x1')) as HX1; eauto.
   destruct HX1.

   + SCase "x1 is done.".
     destruct x1; firstorder.

     * SSCase "x1 is an abstraction".
       right.
       assert (Done x2 \/ (exists x2', Step x2 x2')) as HX2; eauto.
       destruct HX2.

       SSSCase "beta reduction".
        exists (substXX (BBind v t0 x2 :: sx) x1).
        eapply EsAbsApp.
        assumption.

       SSSCase "x2 steps".
        destruct H0 as [x2'].
        exists (XApp (XAbs sx v t0 x1) x2').
        eapply EsAppRight.
         inverts H. assumption.
         assumption.

     * SSCase "x1 is a type abstraction".
       nope.

   + SCase "x1 steps".
     destruct H as [x1'].
     right.
     exists (XApp x1' x2).
     eapply EsAppLeft.
     assumption.

 - Case "XABS is done".
   left. auto.

 - Case "XAPP".
   inverts_type.

   assert (Done x \/ (exists x', Step x x')) as HX; eauto.
   destruct HX.

   + SCase "x1 is done".
     destruct x; firstorder.

     * SSCase "x1 is an abstraction".
       nope.

     * SSCase "x1 is a type abstraction".
       right.
       exists (substTX (st0 :> BBind a k t2) sx x).
       eapply EsABSAPP.

  + SCase "x1 steps".
    destruct H as [x'].
    right.
    exists (XAPP x' t2).
    eapply EsAPPLeft.
    assumption.
Qed.

