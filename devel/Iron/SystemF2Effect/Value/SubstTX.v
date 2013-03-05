
Require Export Iron.SystemF2Effect.Type.
Require Export Iron.SystemF2Effect.Value.Exp.
Require Export Iron.SystemF2Effect.Value.Lift.
Require Export Iron.SystemF2Effect.Value.TyJudge.


(* Substitution of Types in Exps *)
Fixpoint substTV (d: nat) (u: ty) (vv: val) : val :=
  match vv with
  | VVar _         => vv
  | VLoc _         => vv
  | VLam t x       => VLam (substTT d u t) (substTX d u x)
  | VLAM k x       => VLAM k (substTX (S d) (liftTT 1 0 u) x)
  | VConst c       => vv
  end
 with    substTX (d: nat) (u: ty) (xx: exp) : exp :=
  match xx with
  | XVal v         => XVal   (substTV d u v)
  | XLet t x1 x2   => XLet   (substTT d u t)  (substTX d u x1) (substTX d u x2)
  | XApp v1 v2     => XApp   (substTV d u v1) (substTV d u v2)
  | XAPP v1 t2     => XAPP   (substTV d u v1) (substTT d u t2)

  | XOp1 op1 v     => XOp1   op1 (substTV d u v)

  | XNew x         => XNew   (substTX (S d) (liftTT 1 0 u) x)
  | XAlloc r v     => XAlloc (substTT d u r) (substTV d u v)
  | XRead  r v     => XRead  (substTT d u r) (substTV d u v)
  | XWrite r v1 v2 => XWrite (substTT d u r) (substTV d u v1) (substTV d u v2)
  end.  


(******************************************************************************)
(* Substitution of types in exps. *)
Theorem subst_type_exp_ix
 :  forall ix ke te se sp x1 t1 e1 t2 k2
 ,  get ix ke = Some k2
 -> TYPEX ke te se sp x1 t1 e1
 -> KindT (delete ix ke) sp t2 k2
 -> TYPEX (delete ix ke)     (substTE ix t2 te)  (substTE ix t2 se) sp
          (substTX ix t2 x1) (substTT ix t2 t1)  (substTT ix t2 e1).
Proof.
 intros. gen ix ke te se sp t1 t2 e1. gen k2.
 induction x1 using exp_mutind with 
  (PV := fun v => forall ix ke te se sp t1 t2 k3
      ,  get ix ke = Some k3
      -> TYPEV ke te se sp v t1
      -> KindT (delete ix ke) sp t2 k3
      -> TYPEV (delete ix ke)   (substTE ix t2 te) (substTE ix t2 se) sp
               (substTV ix t2 v)(substTT ix t2 t1));
  intros; simpl; inverts_type; eauto.

 Case "VVar".
  apply TvVar; auto.
  unfold substTE. auto.
  eauto using subst_type_type_ix.

 Case "VLoc".
  eapply TvLoc; fold substTT;
  rrwrite ( TRef (substTT ix t2 r) (substTT ix t2 t)
          = substTT ix t2 (TRef r t)).
  unfold substTE; eauto.
  eauto using subst_type_type_ix.

 Case "VLam".
  simpl. apply TvLam.
  eapply subst_type_type_ix; eauto.
  unfold substTE at 1. rewrite map_rewind.
  rrwrite ( map (substTT ix t2) (te :> t)
          = substTE ix t2 (te :> t)).
  eauto.

 Case "VLAM".
  simpl. apply TvLAM.
  rewrite delete_rewind.
  rewrite (liftTE_substTE 0 ix).
  rewrite (liftTE_substTE 0 ix).
  rrwrite ( TBot KEffect 
          = substTT (S ix) (liftTT 1 0 t2) (TBot KEffect)).
  eauto using kind_kienv_weaken.

 Case "VConst".
  destruct c; burn.
 
 Case "XLet".
  simpl. apply TxLet.
   eapply subst_type_type_ix; eauto.
   eauto.
   unfold substTE at 1. rewrite map_rewind.
    rrwrite ( map (substTT ix t2) (te :> t)
            = substTE ix t2 (te :> t)).
   eauto.

 Case "XApp".
  eapply TxApp.
   eapply IHx1 in H8; eauto.
    simpl in H8. burn.
   eapply IHx0 in H11; eauto.

 Case "XAPP".
  rrwrite ( TBot KEffect
          = substTT 0 t (TBot KEffect)).
  rewrite (substTT_substTT 0 ix).
  rewrite (substTT_substTT 0 ix).
  eapply TvAPP.
   simpl. eapply (IHx1 ix) in H8; eauto.
   simpl. eauto using subst_type_type_ix.

 Case "XOp1".
  eapply TxOpPrim.
  destruct o; simpl in *.
   inverts H8. rrwrite (TNat  = substTT ix t2 TNat); eauto.
   inverts H8. rrwrite (TNat  = substTT ix t2 TNat); eauto.

  destruct o; simpl in *.
   inverts H8.
   spec IHx1 H11; eauto.
   spec IHx1 H11; eauto.
   inverts H8. 
   spec IHx1 H1; eauto.

 Case "XNew".
  simpl. 
  apply TxNew 
   with (t := substTT (S ix) (liftTT 1 0 t2) t)
        (e := substTT (S ix) (liftTT 1 0 t2) e).

   rrwrite (ix = 0 + ix).
   eapply lowerTT_substTT_liftTT. auto.
    admit. (* fixme: t2 does not contain TVar 0 as we've lifted it, 
              use mask_substTT, mask_liftTT_id, lowerTT_substTT_liftTT *)

  rewrite delete_rewind.
  rewrite (liftTE_substTE 0 ix).
  rewrite (liftTE_substTE 0 ix).
  eauto using kind_kienv_weaken.

 Case "XAlloc".
  eapply TxOpAlloc; fold substTT.
   eauto using subst_type_type_ix.
   eauto.

 Case "XRead".
  eapply TxOpRead; fold substTT.
   eauto using subst_type_type_ix.
   rrwrite ( TRef (substTT ix t2 r) (substTT ix t2 t1)
           = substTT ix t2 (TRef r t1)).
   eauto.

 Case "XWrite".
  eapply TxOpWrite; fold substTT.
   eauto using subst_type_type_ix.
   eapply IHx1 in H12; eauto. snorm. eauto.
Qed.


Theorem subst_type_exp
 :  forall ke te se sp x1 t1 e1 t2 k2
 ,  TYPEX (ke :> k2) te se sp x1 t1 e1
 -> KindT  ke sp t2 k2
 -> TYPEX  ke (substTE 0 t2 te) (substTE 0 t2 se) sp
              (substTX 0 t2 x1) (substTT 0 t2 t1) (substTT 0 t2 e1).
Proof.
 intros. 
 rrwrite (ke = delete 0 (ke :> k2)).
 eapply subst_type_exp_ix; burn.
Qed.


