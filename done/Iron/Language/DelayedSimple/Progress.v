
Require Export Iron.Language.DelayedSimple.Step.


(* A well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall te x t
 ,  TypeX  te x t
 -> Done x \/ (exists x', Step x x').
Proof.
 intros. gen t.
 induction x using exp_iind; intros.

 - Case "XVar".
   left. auto.

 - Case "XLam".
   left. auto.

 - Case "XApp".
   inverts_type.

   assert (Done x1 \/ (exists x1', Step x1 x1')) as HX1; eauto.
   destruct HX1.

   + SCase "x1 is done.".
     destruct x1.

     * SSCase "x1 is a variable".
       left.  eapply DoneApp. 
       split. 
        eapply DoneVar.
        intuition. nope.

     * SSCase "x1 is a lambda".
       right.
       assert (Done x2 \/ (exists x2', Step x2 x2')) as HX2; eauto.
       destruct HX2.

       SSSCase "beta reduction".
        exists (substXX (BBind v t0 x2 :: ss) x1).
        eapply EsAbsApp.
        assumption.

       SSSCase "x2 steps".
        destruct H0 as [x2'].
        exists (XApp (XAbs ss v t0 x1) x2').
        eapply EsAppRight.
         inverts H. assumption.
         assumption.

     * SSCase "x1 is an application".
       left.
       eapply DoneApp.
       split.
        assumption.
        intuition. nope.

   + SCase "x1 steps".
     destruct H as [x1'].
     right.
     exists (XApp x1' x2).
     eapply EsAppLeft.
     assumption.
Qed.

