
Require Import Iron.Language.SystemF2Effect.Step.
Require Import Iron.Language.SystemF2Effect.Store.
Require Import Iron.Language.SystemF2Effect.TyEnv.
Require Import Iron.Language.SystemF2Effect.TyJudge.
Require Import Iron.Language.SystemF2Effect.KiJudge.


(* A closed, well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall se x t e s
 ,  WfS    se s
 -> TYPEX  nil nil se x t e
 -> (exists v, x = XVal v) 
 \/ (exists s' x', STEP s x s' x').
Proof.
 intros se x t e s HS HT.
 gen t e.
 induction x; intros.

 Case "XVal".
  left. 
  exists v. trivial.

 Case "XLet".
  right.
  inverts_type.
  edestruct IHx1; eauto.
  SCase "x1 value". 
   destruct H as [v]. subst. eauto.  
  SCase "x1 steps".
   dests H. eauto.

 Case "XApp".   
  right.
  inverts_type.
  destruct v; nope.
   SCase "v1 = VLam".
    exists s.
    exists (substVX 0 v0 e0). eauto.

 Case "XAPP".
  right.
  inverts_type.
  exists s.
  destruct v; nope.
   SCase "v1 = VLAM".
    exists (substTX 0 t e). eauto.

 Case "XAlloc".
  right.
  exists (v <: s).
  exists (XVal (VLoc (length s))).
  eauto.

 Case "XRead".
  right.
  inverts_type.
  destruct v; nope.
  inverts_type.
  inverts HS.
  eapply Forall2_get_get_right in H5; eauto.
  exists s.
  destruct H5 as [v].
  exists (XVal v).
  auto.

 Case "XWrite".
  right.
  destruct v; nope.
  exists (update n v0 s).
  exists (XVal (VConst CUnit)).
  auto.

 Case "XOp1".
  destruct o.
  SCase "OSucc".
   inverts_type.
   right.
   exists s.
   destruct v; nope.
   destruct c; nope.
   eauto.

  SCase "OIsZero".
   inverts_type.
   right.
   exists s.
   destruct v; nope.
   destruct c; nope.
   eauto.
Qed.   

