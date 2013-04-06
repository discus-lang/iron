
Require Export Iron.SystemF2Effect.Step.TypeC.
Require Export Iron.SystemF2Effect.Store.LiveE.
Require Export Iron.SystemF2Effect.Store.LiveS.


Definition done (fs : stack) (x : exp)
 := fs = nil /\ (exists v, x = XVal v).


(* Add condition, e1 does not mention handles of any deleted regions.
   Also add this condition to preservation to get region deallocation. *)
Lemma progress
 :  forall se ss sp fs x1 t1 e1
 ,   WfFS   se sp ss fs
 ->  LiveS  ss fs -> LiveE fs e1
 ->  TYPEC  nil nil se sp fs x1 t1 e1
 ->  done fs x1
  \/ (exists ss' sp' fs' x1', STEPF ss sp fs x1 ss' sp' fs' x1').
Proof.
 intros se ss sp fs x1 t1 e1 HW HLS HLE HC.
 gen t1 e1.
 induction x1; intros; eauto.


 (*********************************************************)
 Case "XVal".
 { induction fs.
   SCase "fs = nil".
    left.
    unfold done. rip. exists v. auto.

   SCase "fs = cons ...".
    right.
    destruct a as [t x | n].
    SSCase "FLet".
     exists ss. exists sp. exists fs. exists (substVX 0 v x).
     eauto.
    SSCase "FUse".
     exists ss. exists sp. exists fs. exists (XVal v).
     eauto.
 }


 (*********************************************************)
 Case "XLet".
 { right.
   exists ss. exists sp. exists (fs :> FLet t x1_2). exists x1_1.
   eauto.
 }


 (*********************************************************)
 Case "XApp".
 { right.
   exists ss. exists sp. exists fs.
   inverts_typec.
   destruct v; nope.
   SCase "v1 = XLam".
    exists (substVX 0 v0 e). eauto.
   SCase "v1 = XConst".
    destruct c; nope.
 }

 (*********************************************************)
 Case "XAPP".
 { right.  
   exists ss. exists sp. exists fs.
   inverts_typec.
   destruct v; nope.
   SCase "v1 = XLAM".
    exists (substTX 0 t e). eauto.
   SCase "v1 = XConst".
    destruct c; nope.
 }


 (*********************************************************)
 Case "XOp1".
 { right.
   exists ss. exists sp. exists fs.
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
 }


 (*********************************************************)
 Case "XNew".
 { right.
   exists ss. 
   exists (sp :> SRegion (allocRegion sp)). 
   exists (fs :> FUse    (allocRegion sp)).
   eauto.
 }


 (*********************************************************)
 Case "XAlloc".
 { right. 
   inverts_typec. 
   have HR: (exists n, t = TCap (TyCapRegion n)).
   destruct HR as [n].
   exists (StValue n v <: ss).
   exists sp.
   exists fs.
   exists (XVal (VLoc (length ss))).
   subst. auto.
 }


 (*********************************************************)
 Case "XRead".
 { right.
   inverts HC. inverts_type.
   have HR: (exists n, t = TCap (TyCapRegion n)).
   destruct HR as [n]. subst.

   assert (exists l, v = VLoc l) as HL.
    destruct v; burn.
    destruct c; nope.
   dest l. subst.

   inverts_type. inverts HW. 
   exists ss. exists sp. exists fs.
   rip.

   (* There is a binding in the store corresponding
      to the entry in the store environment. *)
   have (exists b, get l ss = Some b).
    dest b.

   unfold STORET in *.

   destruct b.
   (* Store binding contains a value. *)
   - have HB: (TYPEB nil nil se sp 
                    (StValue n0 v) 
                    (TRef (TCap (TyCapRegion n)) t0))
      by (eapply Forall2_get_get_same; eauto).
     inverts HB.
     exists (XVal v).
     eauto.
    
   (* Store binding is dead, 
      can't happen due to binding liveness constraints LiveE/LiveE *)
   - have HB: (TYPEB nil nil se sp
                     (StDead n0)
                     (TRef (TCap (TyCapRegion n)) t0))
      by (eapply Forall2_get_get_same; eauto).
     inverts HB.

     remember (TCap (TyCapRegion n)) as p. 

     have (SubsT nil sp e1 (TRead p) KEffect)
      by  (eapply EqSym in H; eauto).

     have (LiveE fs (TRead p)).

     lets D: liveS_liveE_value ss fs (TRead p) l (StDead n).
     spec D n. rip. subst p. snorm. rip.
     have (Some n = Some n). rip.
     have (n = n). rip. nope.
 }


 (*********************************************************)
 Case "XWrite".
 { right.
   inverts_typec.
   have HR: (exists n, t = TCap (TyCapRegion n)).
    destruct HR as [n]. subst.
   destruct v; burn.
   destruct c; nope.
 }
Qed.

