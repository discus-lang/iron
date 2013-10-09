
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.
Require Import Iron.Language.SystemF2Effect.Value.Operator.SubstTX.

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
 :  forall ke te se sp x t e p1 p2
 ,  In (SRegion p1) sp
 -> TYPEX ke 
          (substTE 0 (TRgn p2) te) (substTE 0 (TRgn p2) se) sp
          (substTX 0 (TRgn p2) x) 
          (substTT 0 (TRgn p2) t)  (substTT 0 (TRgn p2) e)
 -> TYPEX ke 
          (substTE 0 (TRgn p1) te) (substTE 0 (TRgn p1) se) sp
          (substTX 0 (TRgn p1) x)
          (substTT 0 (TRgn p1) t)  (substTT 0 (TRgn p1) e).
Proof.
 admit.
Qed.

(*
Lemma typex_merge_substTT 
 : forall ke te se sp x t e p1 p2 k
 ,  In (SRegion p1) sp
 -> freshT p2 t
 -> freshT p2 e
 -> KindT (ke :> KRegion) sp t k
 -> KindT (ke :> KRegion) sp e KEffect
 -> TYPEX ke te                    se                 sp 
          x
          (substTT 0 (TRgn p2) t) (substTT 0 (TRgn p2) e)
 -> TYPEX ke (mergeTE p1 p2 te)   (mergeSE p1 p2 se)  sp
          (mergeX p1 p2 x)
          (substTT 0 (TRgn p1) t) (substTT 0 (TRgn p1) e).
Proof.
 intros. gen ke te se sp t e k.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t k
      ,  In (SRegion p1) sp
      -> freshT p2 t
      -> KindT (ke :> KRegion) sp t k
      -> TYPEV ke  te                 se                sp 
               v
               (substTT 0 (TRgn p2) t)  
      -> TYPEV ke  (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp
               (mergeV  p1 p2 v)
               (substTT 0 (TRgn p1) t));
  intros.

 - Case "VVar".
   snorm.
   inverts_type. 
   eapply TvVar.
   + eapply get_map with (f := mergeT p1 p2) in H4.
     unfold mergeTE.
     rewrite H4. f_equal.
     admit.                            (* ok, mergeT_substTT *)
   + admit.                            (* ok, need kindT_substTT_swap lemma *)

 - Case "VLoc".
   snorm.
   inverts_type.
   destruct t; snorm; try nope.
   inverts H4.
   destruct t1.
   eapply TvLoc.
   + eapply get_map with (f := mergeT p1 p2) in H9.
     unfold mergeSE.
     rewrite H9. f_equal.
     simpl. f_equal.
     admit. admit.                    (* ok, mergeT_substTT *)
   + admit.                           (* ok, need kindT_substTT_swap lemma *)  

 - Case "VLam".
   (*
   inverts H2.
   destruct t0;       try (snorm; congruence).
   inverts H9.
   destruct t0_1;     try (snorm; congruence).
   simpl in H3. inverts H4.
   destruct t0_1_1;   try (snorm; congruence).
   simpl in H5. inverts H5.
   destruct t0_1_1_1; try (snorm; congruence).
   simpl in H4. inverts H4.

   snorm.
   erewrite mergeT_substTT.
   eapply TvLam; auto.
   + inverts_kind.
     admit. 
     (* eapply subst_type_type_ix; auto.
        * eauto.
        * inverts_kind. snorm. inverts H13. auto. *)
   + eapply IHx in H12; auto.
     * inverts_kind. snorm. inverts H13.
       erewrite mergeT_substTT in H12; eauto.
     * inverts_kind. snorm. inverts H13. auto. 
     * inverts_kind. snorm. inverts H13. eauto.
   + snorm. 
   + inverts_kind. snorm. inverts H13. 
     eauto.
 *)
   admit.

 - Case "VLAM".
   inverts_type.
   destruct t;       try (snorm; congruence). snorm.
   inverts H10.

   eapply TvLAM.
   admit.                            (* prob ok, need mergeT_liftTT lemma *)   

 - Case "VConst".
   snorm. 
   eapply TvConst.
   destruct c; inverts_type; snorm.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.

 - Case "VVal".
   inverts_type.
   destruct e; try (snorm; congruence). snorm.
   inverts H10.
   eapply TxVal.
   eapply IHx; eauto.

 - Case "XLet". simpl.
   destruct e; try (inverts_type; snorm; congruence). snorm.
   inverts_type.  
 eapply TxLet.
   + admit.
   + inverts_type.
     

eapply IHx1; eauto 2.
     * admit.                                 (* ok, freshT_mergeT lemma *)
     * inverts_kind; eauto. 
     * inverts_type; eauto.
       
       
        
     
   

   + inverts_kind. 
     rgwrite ( mergeTE p1 p2 te :> mergeT p1 p2 t
             = mergeTE p1 p2 (te :> t)).
     eapply IHx2; eauto.

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
*)
