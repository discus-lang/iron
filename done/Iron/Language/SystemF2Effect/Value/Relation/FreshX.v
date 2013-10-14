
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.FreeXX.
Require Export Iron.Language.SystemF2Effect.Value.Relation.SuppX.
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


Definition freshSuppV p2 se v
 := forall l t, get l se = Some t -> suppV l v -> freshT p2 t.
Hint Unfold freshSuppV.

Definition freshSuppX p2 se x
 := forall l t, get l se = Some t -> suppX l x -> freshT p2 t.
Hint Unfold freshSuppX.


(********************************************************************)
Lemma freshX_typeX
 :  forall ke te se sp x t e  p
 ,  not (In (SRegion p) sp)
 -> TYPEX ke te se sp x t e
 -> freshX p x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TYPEV ke te se sp v t
      -> freshV p v);
  intros; inverts_type; 
  try (solve [simpl; rip; eauto]).
Qed.
Hint Resolve freshX_typeX. 


Lemma freshT_typeX_type
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
Hint Resolve freshT_typeX_type.


Lemma freshT_typeX_effect
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
Hint Resolve freshT_typeX_effect.


(********************************************************************)
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
 rewrite <- freshT_liftTT. eauto.
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
 rewrite <- freshT_liftTT. eauto.
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
 rewrite <- freshT_liftTT. eauto.
Qed.


(********************************************************************)
Lemma freshSuppX_liftTE
 :  forall p se x
 ,  freshSuppX p se x
 -> freshSuppX p (liftTE 0 se) x.
Proof.
 intros.
 unfold freshSuppX in *; intros.
 unfold liftTE in H0.
 eapply get_map_exists in H0.
 destruct H0. rip.
 rewrite <- freshT_liftTT.
 eauto.
Qed.
Hint Resolve freshSuppX_liftTE.


Lemma freshSuppX_XLet_split
 :  forall p te t x1 x2
 ,  freshSuppX p te (XLet t x1 x2)
 -> freshSuppX p te x1
 /\ freshSuppX p te x2.
Proof.
 intros.
 split; unfold freshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XLet_join
 :  forall p te t x1 x2
 ,  freshSuppX p te x1
 -> freshSuppX p te x2
 -> freshSuppX p te (XLet t x1 x2).
Proof.
 intros.
 unfold freshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XApp_split
 :  forall p te v1 v2
 ,  freshSuppX p te (XApp v1 v2)
 -> freshSuppV p te v1
 /\ freshSuppV p te v2.
Proof.
 intros.
 split; unfold freshSuppX in *; unfold freshSuppV in *; firstorder.
Qed.


Lemma freshSuppX_XApp_join
 :  forall p te v1 v2
 ,  freshSuppV p te v1
 -> freshSuppV p te v2
 -> freshSuppX p te (XApp v1 v2).
Proof.
 intros.
 unfold freshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XWrite_split
 :  forall p te v1 v2 t
 ,  freshSuppX p te (XWrite t v1 v2)
 -> freshSuppV p te v1
 /\ freshSuppV p te v2.
Proof.
 intros.
 split; unfold freshSuppX in *; unfold freshSuppV in *; firstorder.
Qed.


Lemma freshSuppX_XWrite_join
 :  forall p te v1 v2 t
 ,  freshSuppV p te v1
 -> freshSuppV p te v2
 -> freshSuppX p te (XWrite t v1 v2).
Proof.
 intros.
 unfold freshSuppX in *; firstorder.
Qed.


(* NOTE: the firstorder tactic runs away when given an term with
   multiple sub terms, so we need to do some split/join manually. *)
Lemma freshSuppX_mergeTE
 :  forall p1 p2 p3 te x
 ,  freshSuppX p1 te x
 -> freshSuppX p2 te x
 -> freshSuppX p2 (mergeTE p3 p1 te) x.
Proof.
 intros. gen te.
 induction x using exp_mutind with 
  (PV := fun v => forall te
      ,  freshSuppV p1 te v
      -> freshSuppV p2 te v
      -> freshSuppV p2 (mergeTE p3 p1 te) v); 
  intros; snorm.

  - firstorder.

  - unfold freshSuppV in *.
    rip.
    simpl in H2. subst.
    spec H l. spec H0 l. snorm.
    unfold mergeTE in H1.
    eapply get_map_exists in H1. 
    destruct H1 as [t'].
    spec H t'. spec H0 t'.
    have (l = l). firstorder.
    subst.
    rewrite mergeT_freshT_id; auto.

  - firstorder. 
  - firstorder.
  - firstorder.
  - firstorder.

  - apply freshSuppX_XLet_split in H.
    apply freshSuppX_XLet_split in H0.
    apply freshSuppX_XLet_join; firstorder.

  - apply freshSuppX_XApp_split in H.
    apply freshSuppX_XApp_split in H0.
    apply freshSuppX_XApp_join; firstorder.

  - firstorder.
  - firstorder.
  - firstorder.
  - firstorder.
  - firstorder.
  - firstorder.

  - apply freshSuppX_XWrite_split in H.
    apply freshSuppX_XWrite_split in H0.
    apply freshSuppX_XWrite_join; firstorder.
Qed.


Lemma freshSuppX_typeX
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TYPEX ke te se sp x t e
 -> freshSuppX p se x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TYPEV ke te se sp v t
      -> freshSuppV p se v); 
  intros; inverts_type;
  unfold freshSuppX in *;
  unfold freshSuppV in *; 
  snorm;
  try (solve [ nope]);
  try (solve [ eapply IHx; eauto 2]).

 - subst. rewrite H2 in H0. inverts H0.
   inverts_kind; snorm; eauto.

 - eapply get_map with (f := liftTT 1 0) in H0.
   erewrite freshT_liftTT. 
   eapply IHx; eauto.

 - inverts H1. 
   eapply IHx1; eauto.
   eapply IHx2; eauto.

 - inverts H1.
   eapply IHx; eauto.
   eapply IHx0; eauto.
 
 - eapply get_map with (f := liftTT 1 0) in H0.
   erewrite freshT_liftTT. 
   eapply IHx; eauto.
   
 - eapply get_map with (f := liftTT 1 0) in H0.
   erewrite freshT_liftTT. 
   eapply IHx; eauto.

 - inverts H1.  
   eapply IHx; eauto.
   eapply IHx0; eauto.
Qed.   
