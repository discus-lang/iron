
Require Import Iron.Language.SystemF2Effect.Kind.
Require Import Iron.Language.SystemF2Effect.Type.
Require Import Iron.Language.SystemF2Effect.Value.
Require Import Iron.Language.SystemF2Effect.Store.
Require Import Iron.Language.SystemF2Effect.Step.


(* A closed, well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall se sp ss x t e
 ,  WfS    se sp ss
 -> TYPEX  nil nil se sp x t e
 -> (exists v, x = XVal v) 
 \/ (exists ss' sp' x', STEP ss sp x ss' sp' x').
Proof.
 intros se sp ss x t e HS HT.
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
    exists ss. 
    exists sp.
    exists (substVX 0 v0 e0). 
    eauto.

 Case "XAPP".
  right.
  inverts_type.
  destruct v; nope.
  exists ss. 
  exists sp.
  exists (substTX 0 t e).
  eauto.

 Case "XNew".
  right.
  inverts_type.
  exists ss.
  exists sp.
  exists (XUse (length sp) (substTX 0 (TCon (TyConRegion (length sp))) x)).
  eauto.

 Case "XUse".
  right.
  inverts_type.
  edestruct IHx; eauto.
  SCase "x value".
   dest v. subst.
   exists ss. 
   exists sp.
   exists (XVal v).
   eauto.
  SCase "x steps".
   shift ss'. 
   shift sp'.
   dest x'.
   exists (XUse n x').
   eauto.

 Case "XAlloc".
  right.
  inverts_type.
  have HR: (exists n, t = TCon (TyConRegion n)).
  destruct HR as [n].
  exists (StValue n v <: ss).
  exists sp.
  exists (XVal (VLoc (length ss))).
  subst.
  eauto.

 Case "XRead".
  right.
  inverts_type.

  have HR: (exists n, t = TCon (TyConRegion n)).
   dest n. subst.
  have HL: (exists l, v = VLoc l) by (destruct v; burn).
   dest l. subst.

  inverts_type. 
  exists ss.
  exists sp.
  inverts HS. rip.
  have (exists v, get l ss = Some v).
   dest v.

  unfold STORET in *.
  destruct v.
  have HB: (TYPEB nil nil se sp (StValue n0 v) (tRef (TCon (TyConRegion n)) t0))
   by (eapply Forall2_get_get_same; eauto).
  inverts HB.
  exists (XVal v).
  eauto.

 Case "XWrite".
  right.
  inverts_type.
  have HR: (exists n, t = TCon (TyConRegion n)).
   dest n. subst.
  destruct v; burn.

 Case "XOp1".
  destruct o.
  SCase "OSucc".
   inverts_type.
   right.
   exists ss.
   exists sp.
   destruct v; nope.
   destruct c; nope.
   eauto.

  SCase "OIsZero".
   inverts_type.
   right.
   exists ss.
   exists sp.
   destruct v; nope.
   destruct c; nope.
   eauto.
Qed.

