
Require Export Iron.Language.SystemF2Cap.Type.
Require Export Iron.Language.SystemF2Cap.Value.Exp.
Require Export Iron.Language.SystemF2Cap.Value.Relation.FreeXX.
Require Export Iron.Language.SystemF2Cap.Value.Relation.SuppX.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.TypeKind.


(********************************************************************)
Fixpoint FreshV (p : nat) (vv : val) : Prop :=
 match vv with 
 | VVar     _       => True
 | VLoc     _       => True
 | VBox     x       => FreshX p x
 | VLam     t x     => FreshT p t  /\ FreshX p x
 | VLAM     k x     => FreshX p x
 | VConst   _       => True
 end
 with    FreshX (p : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v       => FreshV p v
 | XLet     t x1 x2 => FreshT p t  /\ FreshX p x1 /\ FreshX p x2
 | XApp     v1 v2   => FreshV p v1 /\ FreshV p v2
 | XAPP     v1 t2   => FreshV p v1 /\ FreshT p t2
 | XOp1     op v    => FreshV p v
 | XPrivate ts x    => Forall (FreshT p) ts /\ FreshX p x
 | XExtend  t x     => FreshT p t  /\ FreshX p x
 | XRun     v       => FreshV p v
 | XAlloc   t v     => FreshT p t  /\ FreshV p v
 | XRead    t v     => FreshT p t  /\ FreshV p v
 | XWrite   t v1 v2 => FreshT p t  /\ FreshV p v1 /\ FreshV p v2
 end.


Definition FreshFreeV p2 te v
 := forall n t, (FreeXV n v /\ get n te = Some t) -> FreshT p2 t.
Hint Unfold FreshFreeV.

Definition FreshFreeX p2 te x
 := forall n t, (FreeXX n x /\ get n te = Some t) -> FreshT p2 t.
Hint Unfold FreshFreeX.


Definition FreshSuppV p2 se v
 := forall l t, get l se = Some t -> SuppV l v -> FreshT p2 t.
Hint Unfold FreshSuppV.

Definition FreshSuppX p2 se x
 := forall l t, get l se = Some t -> SuppX l x -> FreshT p2 t.
Hint Unfold FreshSuppX.


(********************************************************************)
Lemma freshX_typeX
 :  forall ke te se sp x t e  p
 ,  not (In (SRegion p) sp)
 -> TypeX ke te se sp x t e
 -> FreshX p x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TypeV ke te se sp v t
      -> FreshV p v);
  intros; inverts_type; 
  try (solve [simpl; rip; eauto]).

  - Case "XPrivate".
    simpl. rip; eauto. snorm. eauto.
Qed.
Hint Resolve freshX_typeX. 


Lemma freshT_typeX_type
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TypeX ke te se sp x t e
 -> FreshT p t.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TypeV ke te se sp v t
      -> FreshT p t); 
  intros; rip; eauto 3.
Qed.
Hint Resolve freshT_typeX_type.


Lemma freshT_typeX_effect
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TypeX ke te se sp x t e
 -> FreshT p e.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TypeV ke te se sp v t
      -> FreshT p t); 
  intros; rip; eauto 3.
Qed.
Hint Resolve freshT_typeX_effect.


(********************************************************************)
Lemma freshFreeX_nil
 : forall p2 x
 , FreshFreeX p2 nil x.
Proof.
 unfold FreshFreeX.
 intros. snorm.
Qed.
Hint Resolve freshFreeX_nil.


Lemma freshFreeV_nil
 : forall p2 x
 , FreshFreeV p2 nil x.
Proof.
 unfold FreshFreeV.
 intros. snorm.
Qed.
Hint Resolve freshFreeV_nil.


Lemma freshFreeX_XLam
 :  forall p te t  x
 ,  FreshT p t
 -> FreshFreeV p te (VLam t x)
 -> FreshFreeX p (te :> t) x.
Proof.
 intros.
 unfold FreshFreeX in *.
 unfold FreshFreeV in *.
 rip.
 destruct n.
 - snorm.
 - snorm. eauto.
Qed.
Hint Resolve freshFreeX_XLam.


Lemma freshFreeX_XLAM
 :  forall p te k x
 ,  FreshFreeV p te (VLAM k x)
 -> FreshFreeX p (liftTE 0 te) x.
Proof.
 intros.
 unfold FreshFreeX in *.
 unfold FreshFreeV in *. 
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
 ,  FreshT p t
 -> FreshFreeX p te (XLet t x1 x2) 
 -> FreshFreeX p (te :> t) x2. 
Proof.
 intros.
 unfold FreshFreeX in *.
 rip. 
 snorm.
 eapply H0; eauto.
Qed.
Hint Resolve freshFreeX_XLet.


Lemma freshFreeX_XPrivate_ts
 :  forall p te ts x 
 ,  Forall (FreshT p) ts
 -> FreshFreeX p te (XPrivate ts x)
 -> FreshFreeX p ts x.
Proof.
 intros.
 unfold FreshFreeX in *.
 rip.
 snorm. eapply H. eauto.
Qed.


Lemma get_app_first_length
 :  forall {A} n (xs1 xs2 : list A) x
 ,  n < length xs2
 -> get n (xs1 >< xs2) = Some x
 -> get n xs2          = Some x.
Proof.
 intros. gen n.
 induction xs2; intros.
 - simpl. snorm. nope.
 - destruct n.
   + simpl. auto.
   + simpl. eapply IHxs2. 
     snorm.
     snorm.
Qed.


Lemma get_app_second_length
 :  forall {A} n (xs1 xs2 : list A) x
 ,  n >= length xs2
 -> get n (xs1 >< xs2) = Some x
 -> (exists n1, get n1 xs1 = Some x /\ n = n1 + length xs2).
Proof.
  admit. (* fine. list lemma *)
Qed.


Lemma get_app_or
 :  forall {A} n (xs1 xs2 : list A) (x : A)
 ,  get    n (xs1 >< xs2) = Some x
 -> (exists n1, get n1 xs1 = Some x /\ n = n1 + length xs2)
 \/ (           get n  xs2 = Some x).
Proof.
 intros.
 have S: (n < length xs2 \/ n >= length xs2) by omega.
 inverts S.
 
 - right. eapply get_app_first_length; eauto.
 - left.  eapply get_app_second_length; eauto.
Qed.    


Lemma freshFreeX_XPrivate
 :  forall p te ts x
 ,  Forall (FreshT p) ts
 -> FreshFreeX p te (XPrivate ts x) 
 -> FreshFreeX p (liftTE 0 te >< ts) x.
Proof.
 intros.
 unfold FreshFreeX. rip.

 assert  (   (exists n1, get n1 (liftTE 0 te) = Some t /\ n = n1 + length ts)
         \/  (           get n ts             = Some t)) as HE.
 eapply get_app_or; auto.

 inverts HE.

 - destruct H1. rip.
   rip. clear H3.
   unfold liftTE in *.
   eapply get_map_exists in H4.
   destruct H4 as [x']. rip.
   rewrite <- freshT_liftTT.

   unfold FreshFreeX in H0.
   eapply H0. rip.
   simpl. eauto. auto.

 - snorm. eauto.
Qed.


Lemma freshFreeX_XExtend
 :  forall p te t x 
 ,  FreshT p t
 -> FreshFreeX p te (XExtend t x)
 -> FreshFreeX p (liftTE 0 te) x.
Proof.
 intros.
 unfold FreshFreeX in *.
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
 ,  FreshSuppX p se x
 -> FreshSuppX p (liftTE 0 se) x.
Proof.
 intros.
 unfold FreshSuppX in *; intros.
 unfold liftTE in H0.
 eapply get_map_exists in H0.
 destruct H0. rip.
 rewrite <- freshT_liftTT.
 eauto.
Qed.
Hint Resolve freshSuppX_liftTE.


Lemma freshSuppX_XLet_split
 :  forall p te t x1 x2
 ,  FreshSuppX p te (XLet t x1 x2)
 -> FreshSuppX p te x1
 /\ FreshSuppX p te x2.
Proof.
 intros.
 split; unfold FreshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XLet_join
 :  forall p te t x1 x2
 ,  FreshSuppX p te x1
 -> FreshSuppX p te x2
 -> FreshSuppX p te (XLet t x1 x2).
Proof.
 intros.
 unfold FreshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XApp_split
 :  forall p te v1 v2
 ,  FreshSuppX p te (XApp v1 v2)
 -> FreshSuppV p te v1
 /\ FreshSuppV p te v2.
Proof.
 intros.
 split; unfold FreshSuppX in *; unfold FreshSuppV in *; firstorder.
Qed.


Lemma freshSuppX_XApp_join
 :  forall p te v1 v2
 ,  FreshSuppV p te v1
 -> FreshSuppV p te v2
 -> FreshSuppX p te (XApp v1 v2).
Proof.
 intros.
 unfold FreshSuppX in *; firstorder.
Qed.


Lemma freshSuppX_XWrite_split
 :  forall p te v1 v2 t
 ,  FreshSuppX p te (XWrite t v1 v2)
 -> FreshSuppV p te v1
 /\ FreshSuppV p te v2.
Proof.
 intros.
 split; unfold FreshSuppX in *; unfold FreshSuppV in *; firstorder.
Qed.


Lemma freshSuppX_XWrite_join
 :  forall p te v1 v2 t
 ,  FreshSuppV p te v1
 -> FreshSuppV p te v2
 -> FreshSuppX p te (XWrite t v1 v2).
Proof.
 intros.
 unfold FreshSuppX in *; firstorder.
Qed.


(* NOTE: the firstorder tactic runs away when given an term with
   multiple sub terms, so we need to do some split/join manually. *)
Lemma freshSuppX_mergeTE
 :  forall p1 p2 p3 te x
 ,  FreshSuppX p1 te x
 -> FreshSuppX p2 te x
 -> FreshSuppX p2 (mergeTE p3 p1 te) x.
Proof.
 intros. gen te.
 induction x using exp_mutind with 
  (PV := fun v => forall te
      ,  FreshSuppV p1 te v
      -> FreshSuppV p2 te v
      -> FreshSuppV p2 (mergeTE p3 p1 te) v); 
  intros; snorm.

  - firstorder.

  - unfold FreshSuppV in *.
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
  - firstorder.

  - apply freshSuppX_XWrite_split in H.
    apply freshSuppX_XWrite_split in H0.
    apply freshSuppX_XWrite_join; firstorder.
Qed.


Lemma freshSuppX_typeX
 :  forall ke te se sp x t e p
 ,  not (In (SRegion p) sp)
 -> TypeX ke te se sp x t e
 -> FreshSuppX p se x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  not (In (SRegion p) sp)
      -> TypeV ke te se sp v t
      -> FreshSuppV p se v); 
  intros; inverts_type;
  unfold FreshSuppX in *;
  unfold FreshSuppV in *; 
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


