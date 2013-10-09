
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.

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


Definition mergeTE p1 p2 te := map (mergeT p1 p2) te.
Hint Unfold mergeTE.


Definition mergeSE p1 p2 se := map (mergeT p1 p2) se.
Hint Unfold mergeSE.


(********************************************************************)
Lemma typex_merge_substTT 
 : forall ix ke te se sp x t e p1 p2 k
 ,  get ix ke = Some KRegion
 -> In (SRegion p1) sp
 -> freshT p2 t
 -> KindT ke sp t k
 -> KindT ke sp e KEffect
 -> TYPEX (delete ix ke) te se sp 
          x                 (substTT ix (TRgn p2) t) (substTT ix (TRgn p2) e)
 -> TYPEX (delete ix ke)    (mergeTE p1 p2 te)       (mergeSE p1 p2 se)  sp
          (mergeX  p1 p2 x) (substTT ix (TRgn p1) t) (substTT ix (TRgn p1) e).
Proof.
 intros. gen ke te se sp t e k.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t k
      ,  get ix ke = Some KRegion
      -> In (SRegion p1) sp
      -> freshT p2 t
      -> KindT ke sp t k
      -> TYPEV (delete ix ke) te se sp v (substTT ix (TRgn p2) t)  
      -> TYPEV (delete ix ke)            (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp
               (mergeV  p1 p2 v) (substTT ix (TRgn p1) t));
  intros.

 - Case "VVar".
   inverts_type. simpl.
   eapply TvVar.
   + eapply get_map with (f := mergeT p1 p2) in H5.
     unfold mergeTE.
     rewrite H5. f_equal.
     admit.                            (* ok, mergeT_substTT *)
   + admit.                            (* ok, need kindT_substTT_swap lemma *)
   
 - Case "VLoc".
   admit.

 - Case "VLam".
   inverts H3.
   destruct t0;       try (snorm; congruence).
   inverts H10.
   destruct t0_1;     try (snorm; congruence).
   simpl in H4. inverts H4.
   destruct t0_1_1;   try (snorm; congruence).
   simpl in H5. inverts H5.
   destruct t0_1_1_1; try (snorm; congruence).
   simpl in H4. inverts H4.

   simpl.
   erewrite mergeT_substTT.
   eapply TvLam; auto.
   + eapply subst_type_type_ix; auto.
     * eauto.
     * inverts_kind. snorm. inverts H8. auto.
   + eapply IHx in H12; auto.
     * inverts_kind. snorm. inverts H8.
       erewrite mergeT_substTT in H12; eauto.
     * inverts_kind. snorm. 
     * inverts_kind. snorm. inverts H8. auto.
     * inverts_kind. snorm. inverts H8. eauto.
   + snorm.
   + inverts_kind. snorm. inverts H8. eauto.

 - Case "VLAM".
   snorm.
   admit.

 - Case "VConst".
   snorm. 
   eapply TvConst.
   destruct c; inverts_type; snorm.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.

 - Case "VVal".
   admit.

 - Case "XLet".
   admit.

 - Case "XApp".
   admit.

 - Case "XAPP".
   admit.

 - Case "XOp1".
   admit.

 - Case "XPrivate".
   admit.

 - Case "XExtend".
   admit.

 - Case "XAlloc".
   admit.

 - Case "XRead".
   admit.

 - Case "XWrite".
   admit.
Qed.

