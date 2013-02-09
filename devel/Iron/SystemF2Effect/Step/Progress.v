
Require Export Iron.SystemF2Effect.Step.TfJudge.


Definition done (fs : stack) (x : exp)
 := fs = nil /\ (exists v, x = XVal v).


(* Add condition, e1 does not mention handles of any deleted regions.
   Also add this condition to preservation to get region deallocation. *)
Lemma progress
 :  forall se ss sp fs x1 t1 e1
 ,  WfFS   se sp ss fs
 -> TYPEC  nil nil se sp fs x1 t1 e1
 ->  done fs x1
  \/ (exists ss' fs' x1', STEPF ss fs x1 ss' fs' x1').
Proof.
 intros se ss sp fs x1 t1 e1 HW HC.
 gen t1 e1.
 induction x1; intros; eauto.
 
 Case "XVal".
  induction fs.
  SCase "fs = nil".
   left.
   unfold done. rip. exists v. auto.

  SCase "fs = cons ...".
   right.
   destruct a as [t x | n].
   SSCase "FLet".
    exists ss. exists fs. exists (substVX 0 v x).
    eauto.
   SSCase "FUse".
    exists ss. exists fs. exists (XVal v).
    eauto.

 Case "XApp".
  right.
  exists ss. exists fs.
  inverts_typec.
  destruct v; nope.
  SCase "v1 = XLam".
   exists (substVX 0 v0 e). eauto.
  SCase "v1 = XConst".
   destruct c; nope.

 Case "XAPP".
  right.  
   exists ss. exists fs.
   inverts_typec.
   destruct v; nope.
   SCase "v1 = XLAM".
    exists (substTX 0 t e). eauto.
   SCase "v1 = XConst".
    destruct c; nope.

 Case "XOp1".
  right.
  exists ss. exists fs.
  destruct o.
  SCase "OSucc".
   inverts_typec.
   snorm. inverts H8.
   destruct v; nope.
   destruct c; nope.
   eauto.
 SCase "OIsZero".
   inverts_typec.
   snorm. inverts H8.
   destruct v; nope.
   destruct c; nope.
   eauto.

 Case "XNew".
  right.
  exists ss. exists (fs :> FUse (allocRegionFs fs)).
  eauto.

 Case "XAlloc".
  right. 
  inverts_typec. unfold tRef in *.
  have HR: (exists n, t = TCap (TyCapRegion n)).
  destruct HR as [n].
  exists  (StValue n v <: ss).
  exists  fs.
  exists  (XVal (VLoc (length ss))).
  subst. auto.

 Case "XRead".
  right.
  inverts HC. inverts_type. unfold tRef in *.
  have HR: (exists n, t = TCap (TyCapRegion n)).
  destruct HR as [n]. subst.

  assert (exists l, v = VLoc l) as HL.
   destruct v; burn.
   destruct c; nope.
  dest l. subst.

  inverts_type. 
  exists ss.
  exists fs.
  inverts HW. rip.
  have (exists v, get l ss = Some v).
   dest v.

  unfold STORET in *.
  destruct v.
  have HB: (TYPEB nil nil se sp (StValue n0 v) (tRef (TCap (TyCapRegion n)) t0))
   by (eapply Forall2_get_get_same; eauto).
  inverts HB.
  exists (XVal v).
  eauto.

 Case "XWrite".
  right.
  inverts_typec.
  have HR: (exists n, t = TCap (TyCapRegion n)).
   destruct HR as [n]. subst.
  destruct v; burn.
  destruct c; nope.
Qed.


