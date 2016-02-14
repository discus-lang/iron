
Require Import Iron.Language.SimpleDelayed.Step.
Require Import Iron.Language.SimpleDelayed.TypeX.
Require Import Iron.Language.SimpleDelayed.Exp.


Lemma done_lam 
 :  forall x t1 t2
 ,  TypeX nil x (TFun t1 t2)
 -> Done x
 -> isXLam x.
Proof.
 intros. gen t1 t2.
 induction x.

 - Case "XVar".
   nope.

 - Case "XLam". 
   intros.
   auto.

 - Case "XApp".
   inverts H0. inverts H1.
   destruct x1.
   + nope.
   + have (isXLam (XLam l n t x1)). nope.
   + intros.
     exfalso.
     clear H0.
     lets D: IHx1 H.
     inverts H1.
     eapply D in H4. nope.
Qed.
Hint Resolve done_lam.


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

   have (Done x1 \/ (exists x1', Step x1 x1')) as HX1.
   destruct HX1.
   + SCase "x1 is done.".
     destruct H.
     * SSCase "x1 is a variable".
       left. eapply DoneApp. 
       split. eapply DoneVar.
       auto.

     * SSCase "x1 is a lambda".
       right.
       have (Done x2 \/ (exists x2', Step x2 x2')) as HX2.

       destruct HX2.
       SSSCase "beta reduction".
        exists (substXX (BBind n t0 x2 :: bs) x).
        eapply EsLamApp.
        trivial.

       SSSCase "x2 steps".
        dest x2'.
        exists (XApp (XLam bs n t0 x) x2').
        eapply EsAppRight.
        assumption.

     * SSCase "x1 is an application".
       left.
       eapply DoneApp.
       split.
        eapply DoneApp. assumption.
        auto.

   + SCase "x1 steps".
     dest x1'.
     right.
     exists (XApp x1' x2).
     eapply EsAppLeft.
     assumption.

 - Case "BBind".
   trivial.
Qed.
