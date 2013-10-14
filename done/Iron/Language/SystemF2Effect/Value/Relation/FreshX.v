
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.FreeXX.
Require Export Iron.Language.SystemF2Effect.Value.Relation.TyJudge.
Require Export Iron.Language.SystemF2Effect.Value.Relation.TyJudge.TypeKind.


(********************************************************************)
Fixpoint freshV (p : nat) (vv : val) : Prop :=
 match vv with 
 | VVar     _       => True
 | VLoc     _       => True
 | VLam     t x     => freshT p t  /\ freshX p x
 | VLAM     k x     => freshX p x
 | VConst   _       => True
 end
 with    freshX (p : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v       => freshV p v
 | XLet     t x1 x2 => freshT p t  /\ freshX p x1 /\ freshX p x2
 | XApp     v1 v2   => freshV p v1 /\ freshV p v2
 | XAPP     v1 t2   => freshV p v1 /\ freshT p t2
 | XOp1     op v    => freshV p v
 | XPrivate x       => freshX p x
 | XExtend  t x     => freshT p t  /\ freshX p x
 | XAlloc   t v     => freshT p t  /\ freshV p v
 | XRead    t v     => freshT p t  /\ freshV p v
 | XWrite   t v1 v2 => freshT p t  /\ freshV p v1 /\ freshV p v2
 end.


Definition freshFreeV p2 te v
 := forall n t, (freeXV n v /\ get n te = Some t) -> freshT p2 t.
Hint Unfold freshFreeV.


Definition freshFreeX p2 te x
 := forall n t, (freeXX n x /\ get n te = Some t) -> freshT p2 t.
Hint Unfold freshFreeX.


(********************************************************************)
Lemma freshX_type
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TYPEX ke te se sp x t e
 -> freshT p t.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TYPEV ke te se sp v t
      -> freshT p t); 
  intros; rip; eauto 3.
Qed.
Hint Resolve freshX_type.


Lemma freshX_effect
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TYPEX ke te se sp x t e
 -> freshT p e.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TYPEV ke te se sp v t
      -> freshT p t); 
  intros; rip; eauto 3.
Qed.
Hint Resolve freshX_effect.


Lemma freshFreeX_nil
 : forall p2 x
 , freshFreeX p2 nil x.
Proof.
 unfold freshFreeX.
 intros. snorm.
Qed.
Hint Resolve freshFreeX_nil.


Lemma freshFreeV_nil
 : forall p2 x
 , freshFreeV p2 nil x.
Proof.
 unfold freshFreeV.
 intros. snorm.
Qed.
Hint Resolve freshFreeV_nil.


Lemma freshFreeX_XLam
 :  forall p te t  x
 ,  freshT p t
 -> freshFreeV p te (VLam t x)
 -> freshFreeX p (te :> t) x.
Proof.
 intros.
 unfold freshFreeX in *.
 unfold freshFreeV in *.
 rip.
 destruct n.
 - snorm.
 - snorm. eauto.
Qed.
Hint Resolve freshFreeX_XLam.


Lemma freshFreeX_XLAM
 :  forall p te k x
 ,  freshFreeV p te (VLAM k x)
 -> freshFreeX p (liftTE 0 te) x.
Proof.
 intros.
 unfold freshFreeX in *.
 unfold freshFreeV in *. 
 rip.
 snorm.
 unfold liftTE in *.
 eapply get_map_exists in H2.
 destruct H2 as [t']. rip.
 eapply freshT_liftTT. eauto.
Qed.
Hint Resolve freshFreeX_XLAM.


Lemma freshFreeX_XLet 
 :  forall p t te x1 x2
 ,  freshT p t
 -> freshFreeX p te (XLet t x1 x2) 
 -> freshFreeX p (te :> t) x2. 
Proof.
 intros.
 unfold freshFreeX in *.
 rip. 
 snorm.
 eapply H0; eauto.
Qed.
Hint Resolve freshFreeX_XLet.


Lemma freshFreeX_XPrivate
 :  forall p te x 
 ,  freshFreeX p te (XPrivate x)
 -> freshFreeX p (liftTE 0 te) x.
Proof.
 intros.
 unfold freshFreeX in *.
 rip.
 snorm.
 unfold liftTE in *.
 eapply get_map_exists in H2.
 destruct H2 as [t']. rip.
 eapply freshT_liftTT. eauto.
Qed.


Lemma freshFreeX_XExtend
 :  forall p te t x 
 ,  freshT p t
 -> freshFreeX p te (XExtend t x)
 -> freshFreeX p (liftTE 0 te) x.
Proof.
 intros.
 unfold freshFreeX in *.
 rip.
 snorm.
 unfold liftTE in *.
 eapply get_map_exists in H3.
 destruct H3 as [t']. rip.
 eapply freshT_liftTT. eauto.
Qed.

