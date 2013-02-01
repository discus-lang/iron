
Require Import Iron.Language.SimplePCFa.Step.Frame.
Require Import Iron.Language.SimplePCFa.Step.TfJudge.
Require Import Iron.Language.SimplePCFa.Value.


Definition done (fs : stack) (x : exp)
 := fs = nil /\ (exists v, x = XVal v).
Hint Unfold done.

Lemma progress
 :  forall fs x t
 ,  TYPEC nil fs x t
 -> done fs x \/ (exists fs' x', STEPF fs x fs' x').
Proof.
 intros fs x t HC.
 gen fs t.
 induction x; intros.

 Case "XVal".
  induction fs.
   left.
    unfold done. rip.
    exists v. auto.
   right.
    destruct a as [t3 x3].
    exists fs.
    exists (substVX 0 v x3).
    eauto.

 Case "XLet".
  right.
  exists (fs :> FLet t x2).
  exists x1. 
  auto.

 Case "XApp".
  right.
  exists fs.
  inverts HC.
  destruct v; nope.
   SCase "v1 = VLam".
    exists (substVX 0 v0 e).
    eauto.
   SCase "v1 = VFix".
    exists (XApp (substVV 0 (VFix t0 v) v) v0).
    eauto.

 Case "XOp1".
  right.
  exists fs.
   destruct o.

   SCase "OSucc".
    destruct v; nope.
    SSCase "VConst". 
     destruct c; nope.
     exists (XVal (VConst (CNat (S n)))).
      auto.

   SCase "OPred".
    destruct v; nope.
    SSCase "VConst".
     destruct c; nope.
     destruct n; eauto.
     
  SCase "OIsZero".
   destruct v; nope.
   SSCase "VConst".
    destruct c; nope.
    destruct n; eauto.
    
 Case "XIf".
  right.
  exists fs.
  destruct v; nope.
  SSCase "VConst".
   destruct c; nope.
   destruct b; eauto.
Qed.


