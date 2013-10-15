
Require Export Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


(* A well typed expression is well formed *)
Lemma typex_wfX
 :  forall ke te se sp x t e
 ,  TypeX  ke te se sp x t e
 -> wfX (length ke) (length te) (length se) x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t1
      ,  TypeV ke te se sp v t1
      -> wfV (length ke) (length te) (length se) v);
   rip; inverts_type; try burn.

 Case "VLam".
  spec IHx H8. burn.

 Case "VLAM".
  eapply WfV_VLAM.
  spec IHx H7. simpl in IHx.
  rewrite <- length_liftTE in IHx.
  rewrite <- length_liftTE in IHx.
  auto.

 Case "XLet".
  spec IHx1 H10.
  spec IHx2 H11.
  burn.

 Case "XNew".
  eapply WfX_XNew.
  spec IHx H7.
  rrwrite (length (ke :> KRegion) = S (length ke)) in IHx.
  rewrite <- length_liftTE in IHx.
  rewrite <- length_liftTE in IHx.
  burn.
Qed.
Hint Resolve typex_wfX.
