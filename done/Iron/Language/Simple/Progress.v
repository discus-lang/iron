
Require Import Iron.Language.Simple.Step.
Require Import Iron.Language.Simple.Ty.
Require Import Iron.Language.Simple.Exp.


(* A closed, well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall x t
 ,  TYPE nil x t
 -> value x \/ (exists x', STEP x x').
Proof.
 intros.
 remember (@nil ty) as tyenv.
 induction H; subst.

 Case "XVar".
  burn.

 Case "XLam".
  left. burn.

 Case "XApp".
  right.
  assert (@nil ty = nil). burn. rip.

  destruct IHTYPE1.
  SCase "value x1".
   destruct IHTYPE2.
   SSCase "value x2".
    have (exists t x, x1 = XLam t x).
     destruct H4 as [t11]. 
     destruct H4 as [x11]. 
     subst.
    exists (substX 0 x2 x11). burn.

   SSCase "x2 steps".
    destruct H3 as [x2'].
    exists (XApp x1 x2'). 
    lets D: EsContext XcApp2; burn.

   SSCase "x1 steps".
    destruct H2 as [x1'].
    exists (XApp x1' x2).
    lets D: EsContext XcApp1; burn.
Qed.

