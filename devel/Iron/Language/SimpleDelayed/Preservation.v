
Require Import Iron.Language.SimpleDelayed.Step.
Require Import Iron.Language.SimpleDelayed.SubstXX.
Require Import Iron.Language.SimpleDelayed.TypeX.


(* If a closed, well typed expression takes an evaluation step 
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
   intros.
   inverts HS. destruct H0. nope. nope.

 - Case "XLam".
   intros.
   inverts HS. destruct H0. nope. nope.

 - Case "XApp".
   intros.
   inverts HS.
   + SCase "one component steps in context".
     inverts H0.

     * SSCase "functional expression steps".
       inverts H.
       inverts HT.
       lets D: IHx1 H3 H1. eauto.

     * SSCase "argument steps".
       inverts H.
       inverts HT.
       lets D: IHx2 H6 H1. eauto.

   + SCase "perform a substitution".
     inverts HT.
     inverts H3.
     eapply subst_exp_exp.
     * simpl. simpl in H10. trivial.
     * simpl in H10.
       eapply Forall_cons. eauto. trivial.
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
 induction HS; burn using preservation.
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
 induction HS; burn using preservation.
Qed.


