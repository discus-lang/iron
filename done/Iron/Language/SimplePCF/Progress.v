
Require Import Iron.Language.SimplePCF.Step.
Require Import Iron.Language.SimplePCF.Ty.
Require Import Iron.Language.SimplePCF.Exp.


(* A closed well typed expression is either a value 
   or can transition to the next state. *)
Theorem progress
 :  forall x t
 ,  TYPE nil x t
 -> value x \/ (exists x', STEP x x').
Proof.
 intros.
 remember (@nil ty) as te.
 induction H; subst; try (solve [left; burn]); right.

 Case "XApp".
  have HN: (@nil ty = nil). rip. clear HN.

  destruct IHTYPE1.
  SCase "value x1".
   destruct IHTYPE2.
   SSCase "value x2".
    have HL: (exists t x, x1 = XLam t x).
    destruct HL as [t].
    destruct H3 as [x].
    subst.
    exists (substX 0 x2 x). burn.

   SSCase "x2 steps".
    destruct H2 as [x2'].
    exists (XApp x1 x2'). burn.

   SSCase "x1 steps".
    destruct H1 as [x1'].
    exists (XApp x1' x2).
    eapply (EsContext (fun xx => XApp xx x2)); burn.

 Case "XFix".
  exists (substX 0 (XFix t1 x1) x1).
  burn.  

 Case "XSucc".
  have HN: (@nil ty = nil). rip. clear HN.
  destruct IHTYPE.
   have HN: (exists n, x1 = XNat n).
    destruct HN. subst. burn.
    destruct H0 as [x'].
   exists (XSucc x').
    burn.

 Case "XPred".
  have HN: (@nil ty = nil). rip. clear HN.
  destruct IHTYPE.
   have HN: (exists n, x1 = XNat n).
    destruct HN as [n]. subst.
    destruct n; burn.
   destruct H0 as [x'].
    exists (XPred x').
    burn.

 Case "XIsZero".
  have HN: (@nil ty = nil). rip. clear HN.
  destruct IHTYPE.
   have HN: (exists n, x1 = XNat n).
    destruct HN as [n]. subst.
    destruct n; burn.
   destruct H0 as [x'].
    exists (XIsZero x').
    burn. 

 Case "XIf".
  have HN: (@nil ty = nil). rip. clear HN.
  destruct IHTYPE1.
   have HN: (x1 = XFalse \/ x1 = XTrue).
    destruct HN; subst; burn.
   destruct H2 as [x1'].
    exists (XIf x1' x2 x3).
    eapply (EsContext (fun xx => XIf xx x2 x3)); burn.
Qed.


