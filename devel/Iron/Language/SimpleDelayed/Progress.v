
Require Import Iron.Language.SimpleDelayed.Step.
Require Import Iron.Language.SimpleDelayed.TypeX.
Require Import Iron.Language.SimpleDelayed.Exp.


(* A closed, well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall te x t
 ,  TypeX te x t
 -> Done x \/ (exists x', Step x x').
Proof.
 intros. gen t.
 induction x using exp_mutind with
  (PB := fun b => b = b).

 - Case "XVar".
   intros. 
   left.
   eapply DoneVar.

 - Case "XLam".
   left. 
   apply DoneLam.

 - Case "XApp".
   intros.
   inverts H.

   assert (Done x1 \/ (exists x1', Step x1 x1')) as HX1; eauto.
   destruct HX1.
   + SCase "x1 is done.".
     destruct H.
     * SSCase "x1 is a variable".
       left. eapply DoneApp. 
       split. eapply DoneVar.
       auto.

     * SSCase "x1 is a lambda".
       right.
       assert (Done x2 \/ (exists x2', Step x2 x2')) as HX2; eauto.

       destruct HX2.
       SSSCase "beta reduction".
        exists (substXX (BBind n t0 x2 :: bs) x).
        eapply EsLamApp.
        assumption.

       SSSCase "x2 steps".
        dest x2'.
        exists (XApp (XLam bs n t0 x) x2').
        eapply EsAppRight.
        assumption.

     * SSCase "x1 is an application".
       left. auto.

   + SCase "x1 steps".
     dest x1'.
     right.
     exists (XApp x1' x2).
     eapply EsAppLeft.
     assumption.

 - Case "BBind".
   trivial.
Qed.
