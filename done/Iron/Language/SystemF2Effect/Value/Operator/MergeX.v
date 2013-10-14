
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.
Require Import Iron.Language.SystemF2Effect.Value.Relation.FreshX.
Require Import Iron.Language.SystemF2Effect.Value.Operator.SubstTX.


(********************************************************************)
Fixpoint mergeV (p1 p2 : nat) (vv : val) : val :=
 match vv with
 | VVar  _        => vv
 | VLoc  _        => vv
 | VLam  t x      => VLam     (mergeT p1 p2 t) (mergeX p1 p2 x)
 | VLAM  k x      => VLAM k   (mergeX p1 p2 x)
 | VConst c       => vv
 end
 with   mergeX (p1 p2 : nat) (xx : exp) : exp :=
 match xx with
 |  XVal v         
 => XVal     (mergeV p1 p2 v)

 |  XLet t x1 x2   
 => XLet     (mergeT p1 p2 t)  (mergeX p1 p2 x1) (mergeX p1 p2 x2)

 |  XApp v1 v2     
 => XApp     (mergeV p1 p2 v1) (mergeV p1 p2 v2)

 |  XAPP v1 t2     
 => XAPP     (mergeV p1 p2 v1) (mergeT p1 p2 t2)

 |  XOp1 op v      
 => XOp1 op  (mergeV p1 p2 v)

 |  XPrivate x     
 => XPrivate (mergeX p1 p2 x)

 |  XExtend  t x   
 => XExtend  (mergeT p1 p2 t)  (mergeX p1 p2 x)

 |  XAlloc t v     
 => XAlloc   (mergeT p1 p2 t)  (mergeV p1 p2 v)

 |  XRead  t v     
 => XRead    (mergeT p1 p2 t)  (mergeV p1 p2 v)

 |  XWrite t v1 v2 
 => XWrite   (mergeT p1 p2 t)  (mergeV p1 p2 v1) (mergeV p1 p2 v2)
 end.


(********************************************************************)
Lemma mergeX_typeX
 :  forall ke te se sp x t e p1 p2
 ,  In (SRegion p1) sp
 -> TYPEX ke te se sp x t e
 -> TYPEX ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp 
          (mergeX p1 p2 x) (mergeT p1 p2 t) (mergeT p1 p2 e).
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t
      ,  In (SRegion p1) sp
      -> TYPEV ke te se sp v t
      -> TYPEV ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp
                  (mergeV  p1 p2 v)  (mergeT  p1 p2 t)); 
  intros; inverts_type
   ; try (solve [snorm]).
   
 - Case "VVar".
   simpl.
   eapply TvVar.
   + unfold mergeTE. erewrite get_map; eauto.
   + eauto.

 - Case "VLoc".
   simpl.
   eapply TvLoc.
   + unfold mergeTE. erewrite get_map.
     rrwrite ( TRef (mergeT p1 p2 r) (mergeT p1 p2 t0)
             = mergeT p1 p2 (TRef r t0)).
     eauto. auto.
   + rrwrite ( TRef (mergeT p1 p2 r) (mergeT p1 p2 t0)
             = mergeT p1 p2 (TRef r t0)).
     eauto.

 - Case "VLam".
   snorm. eapply TvLam; eauto.
   rgwrite ( mergeTE p1 p2 te :> mergeT p1 p2 t
           = mergeTE p1 p2 (te :> t)).
   eauto.

 - Case "VLAM".
   simpl.
   eapply TvLAM.
   repeat (rewrite mergeTE_liftTE_comm).
   rrwrite ( TBot KEffect = mergeT p1 p2 (TBot KEffect)).
   eapply IHx; auto.

 - Case "VConst".
   destruct c; snorm.

 - Case "XLet". 
   snorm.
   eapply TxLet; eauto.
   rgwrite ( mergeTE p1 p2 te :> mergeT p1 p2 t
           = mergeTE p1 p2 (te :> t)).
   eauto.   
 
 - Case "XApp". 
   snorm.
   eapply TxApp; eauto.
   rgwrite ( TFun (mergeT p1 p2 t11) (mergeT p1 p2 e) (mergeT p1 p2 t)
           = mergeT p1 p2 (TFun t11 e t)).
   eauto.

 - Case "XAPP".
   snorm.
   rgwrite ( TBot KEffect = mergeT p1 p2 (TBot KEffect)).
   rewrite <- mergeT_substTT_comm.
   eapply TvAPP with (k11 := k11).
   rgwrite ( TForall k11 (mergeT p1 p2 t12)
           = mergeT p1 p2 (TForall k11 t12)).
   eauto. eauto.

 - Case "XOp1".
   snorm.
   destruct o; snorm.
   + inverts H7. 
     eapply TxOpPrim. snorm.
     rgwrite (TNat = mergeT p1 p2 TNat). eauto.
   + inverts H7.
     eapply TxOpPrim. snorm.
     rgwrite (TNat = mergeT p1 p2 TNat). eauto.

 - Case "XPrivate".
   snorm.
   eapply TxPrivate
    with (t := mergeT p1 p2 t0)
         (e := mergeT p1 p2 e0).
    + symmetry.
      eapply mergeT_lowerTT. eauto.
    + rewrite mergeT_maskOnVarT.
      symmetry.
      eapply mergeT_lowerTT. eauto.
    + repeat (rewrite mergeTE_liftTE_comm).
      eapply IHx; eauto.

 - Case "XExtend".
   snorm.
   rewrite <- mergeT_substTT_comm.
   eapply TxExtend
    with (e := mergeT p1 p2 e0).            
    + rewrite mergeT_maskOnVarT.
      symmetry.
      eapply mergeT_lowerTT. eauto.
    + eauto.
    + repeat (rewrite mergeTE_liftTE_comm).
      eapply IHx; eauto.

 - Case "XRead".
   simpl.
   eapply TxOpRead; eauto.
   rgwrite ( TRef (mergeT p1 p2 r) (mergeT p1 p2 t)
           = mergeT p1 p2 (TRef r t)).
   eauto.

 - Case "XWrite".
   simpl.
   eapply TxOpWrite; eauto.
   rgwrite ( TRef (mergeT p1 p2 r) (mergeT p1 p2 t2)
           = mergeT p1 p2 (TRef r t2)).
   eauto.
Qed.



Lemma mergeX_typeX_freshX
 :  forall ke te se sp x t e p1 p2
 ,  freshX     p2 x
 -> freshFreeX p2 te x
 -> TYPEX ke te se sp x t e
 -> TYPEX ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp x t e.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t 
      ,  freshV     p2 v
      -> freshFreeV p2 te v
      -> TYPEV ke te se sp v t
      -> TYPEV ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp v t);
  intros; inverts_type; auto.

 - Case "XVar".
   eapply TvVar; auto.
   unfold freshFreeV in *.
   spec H1 n. spec H1 t.

   have HF: (freeXV n (VVar n)) 
    by (unfold freeXV; symmetry; eapply beq_nat_refl).

   assert (freshT p2 t).
    eauto. clear H1.

   unfold mergeTE.
   eapply get_map with (f := mergeT p1 p2) in H4.
   rewrite H4.
   rewrite mergeT_freshT_id; auto.

 - Case "XLoc".
   eapply TvLoc; auto.
   admit.                                    (* ok, need freshSuppV crap *)

 - Case "XLam".
   eapply TvLam; auto.
   snorm. 
   rewrite mergeTE_rewind; auto.

 - Case "XLAM".
   eapply TvLAM.
   snorm. repeat (rewrite mergeTE_liftTE_comm).
   eapply IHx; snorm; eauto. 
   
 - Case "XLet".
   snorm.
   eapply TxLet; auto.
   + eapply IHx1; auto. firstorder.
   + rewrite mergeTE_rewind; auto.
     eapply IHx2; eauto. 
  
 - Case "XApp".
   snorm.
   eapply TxApp. 
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
   + eapply IHx0; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.

 - Case "XAPP".
   rgwrite (TBot KEffect = substTT 0 t (TBot KEffect)).
   eapply TvAPP; eauto.
   eapply IHx; snorm; eauto.
 
 - Case "XOp1".
   eapply TxOpPrim; eauto.

 - Case "XPrivate".
   eapply TxPrivate; eauto.
   repeat (rewrite mergeTE_liftTE_comm).
   eapply IHx; snorm.
   eapply freshFreeX_XPrivate; eauto.

 - Case "XExtend".
   eapply TxExtend; eauto.
   repeat (rewrite mergeTE_liftTE_comm).
   eapply IHx; snorm.
   eapply freshFreeX_XExtend; eauto.

 - Case "XAlloc".
   eapply TxOpAlloc; eauto.
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H; snorm; eauto.

 - Case "XRead".
   eapply TxOpRead; eauto.
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H; snorm; eauto.

 - Case "XWrite".
   eapply TxOpWrite; eauto.
   + eapply IHx; snorm; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
   + eapply IHx0; snorm; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
Qed.

