
Require Export Iron.Language.SystemF2Cap.Type.
Require Export Iron.Language.SystemF2Cap.Value.Exp.
Require Export Iron.Language.SystemF2Cap.Value.Operator.LiftX.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.WeakTyEnv.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.WeakKiEnv.


(********************************************************************)
(* Substitution of Values in Exps *)
Fixpoint substVV (d: nat) (u: val) (vv: val) : val :=
  match vv with
  | VVar ix 
  => match nat_compare ix d with
     (* Index matches the one we are substituting for. *)
     | Eq  => u
     
     (* Index was free in the original expression.
        As we've removed the outermost binder, also decrease this
        index by one. *)
     | Gt  => VVar (ix - 1)

     (* Index was bound in the original expression. *)
     | Lt  => VVar ix
     end

  | VLoc l           => vv

  | VBox x           => VBox       (substVX d u x)

  (* Increase the depth as we move across a lambda.
     Also lift free references in the exp being substituted
     across the lambda as we enter it. *)
  | VLam t1 x2       => VLam t1 (substVX (S d) (liftXV 1 0 u) x2)

  | VLAM k1 x2       => VLAM k1 (substVX d (liftTV 0 u) x2)

  | VConst c         => VConst c
  end

 with   substVX (d: nat) (u: val) (xx: exp) : exp :=
  match xx with
  |  XVal v          => XVal (substVV d u v)

  |  XLet t1 x2 x3 
  => XLet t1 (substVX d u x2) (substVX (S d) (liftXV 1 0 u) x3)

  |  XApp v1 v2        => XApp   (substVV d u v1) (substVV d u v2)
  |  XAPP v1 t2        => XAPP   (substVV d u v1) t2

  |  XOp1 op v1        => XOp1 op (substVV d u v1)

  |  XPrivate ts x     => XPrivate ts (substVX (d + length ts) 
                                               (liftXV (length ts) 0 (liftTV 0 u)) x)
  |  XExtend  tR x     => XExtend  tR (substVX d (liftTV 0 u) x)

  |  XRun     v        => XRun        (substVV d u v)

  |  XAlloc   tR v2    => XAlloc  tR (substVV d u v2)
  |  XRead    tR v1    => XRead   tR (substVV d u v1)
  |  XWrite   tR v1 v2 => XWrite  tR (substVV d u v1) (substVV d u v2)
  end.


(********************************************************************)
(* Substitution of values in exps preserves typing *)
Lemma subst_val_exp_ix
 :  forall ix ke te se sp x1 t1 e1 v2 t2
 ,  get  ix te = Some t2
 -> TypeX ke te             se sp x1 t1 e1
 -> TypeV ke (delete ix te) se sp v2 t2
 -> TypeX ke (delete ix te) se sp (substVX ix v2 x1) t1 e1.
Proof.
 intros. gen ke te se sp t1 e1 v2 t2. gen ix.
 induction x1 using exp_mutind with 
  (PV := fun v1 => forall ix ke te se sp t1 t2 v2
      ,  get ix te = Some t2
      -> TypeV ke te             se sp v1 t1
      -> TypeV ke (delete ix te) se sp v2 t2
      -> TypeV ke (delete ix te) se sp (substVV ix v2 v1) t1)
  ; intros; simpl; inverts_type; eauto.

 - Case "VVar".
   snorm.
   + subst. rewrite H in H3. norm.
   + apply TvVar; auto.
     destruct n.
      burn.
      down. snorm.

 - Case "VLam".
   apply TvLam; auto.
    rewrite delete_rewind.
    eauto using typev_tyenv_weaken1.

 - Case "VLAM".
   simpl.
   eapply (IHx1 ix) in H9.
   apply TvLAM.
    unfold liftTE. rewrite map_delete. eauto.
    eapply get_map. eauto.
    unfold liftTE. rewrite <- map_delete.
     rrwrite ( map (liftTT 1 0) (delete ix te) 
             = liftTE 0 (delete ix te)).
     eauto using typev_kienv_weaken1.

 - Case "XLet".
   apply TxLet; eauto.
    rewrite delete_rewind.
    eauto using typev_tyenv_weaken1.

 - Case "XPrivate".
   eapply (IHx1 (ix + length ts)) in H13.
   + eapply TxPrivate; eauto.
     unfold liftTE in *. rewrite map_delete.
     rewrite delete_app. eauto.
   + eapply get_app_left_some.
     eapply get_map. eauto.
   + unfold liftTE.
     rewrite <- delete_app.
     rewrite <- map_delete.
     rrwrite ( map (liftTT 1 0) (delete ix te)
             = liftTE 0 (delete ix te)).
     lets D1: typev_kienv_weaken1 H1.
     lets D2: typev_tyenv_weaken_append D1.
     eapply D2.

 - Case "XExtend".
   eapply (IHx1 ix) in H12.
   + eapply TxExtend; eauto.
     unfold liftTE. rewrite map_delete. eauto.
   + eapply get_map. eauto.
   + unfold liftTE.
     rewrite <- map_delete.
     rrwrite ( map (liftTT 1 0) (delete ix te)
             = liftTE 0 (delete ix te)).
     lets D: typev_kienv_weaken1 H1.
     eapply D.
Qed.


Lemma subst_val_exp
 :  forall ke te se sp x1 t1 e1 v2 t2
 ,  TypeX  ke (te :> t2) se sp x1                t1 e1
 -> TypeV  ke te se         sp v2                t2
 -> TypeX  ke te se         sp (substVX 0 v2 x1) t1 e1.
Proof.
 intros.
 rrwrite (te = delete 0 (te :> t2)). 
 eapply subst_val_exp_ix; burn.
Qed.

