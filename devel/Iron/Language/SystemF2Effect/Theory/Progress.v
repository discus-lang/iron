
Require Import Iron.Language.SystemF2Effect.Kind.
Require Import Iron.Language.SystemF2Effect.Type.
Require Import Iron.Language.SystemF2Effect.Value.
Require Import Iron.Language.SystemF2Effect.Store.
Require Import Iron.Language.SystemF2Effect.Step.


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
  exists (substTX 0 t e). eauto.

 Case "XNew".
  right.
  inverts_type.
  exists (SDesc <: s).
  exists (substTX 0 (TCon (TyConRegion (length s))) x).
  eauto.

 Case "XUse".
  right.
  inverts_type.
  edestruct IHx; eauto.
  SCase "x value".
   dest v. subst.
   exists s. exists (XVal v).
   eauto.
  SCase "x steps".
   shift s'. dest x'.
   exists (XUse n x').
   eauto.

 Case "XAlloc".
  right.
  inverts_type.
  have HR: (exists n, t = TCon (TyConRegion n)).
  destruct HR as [n].
  exists (SValue n v <: s).
  exists (XVal (VLoc (length s))).
  subst.
  eauto.

 Case "XRead".
  right.
  inverts_type.
  have HR: (exists n, t = TCon (TyConRegion n)).
  destruct HR as [n]. subst.
  have HL: (exists l, v = VLoc l) by (destruct v; burn).
  destruct HL as [l]. subst.
  inverts_type. 
  destruc
 
  exists s.
  inverts H7.
  
  burn.
  
  burn.

 Case "XWrite".
  right.
  inverts_type.
  have HR: (exists n, t = TCon (TyConRegion n)).
  have HL: (exists l, v = VLoc l).
  destruct HL as [l]. subst.
  burn.

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

