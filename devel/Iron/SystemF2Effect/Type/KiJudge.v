
Require Export Iron.SystemF2Effect.Type.LiftTT.
Require Export Iron.SystemF2Effect.Type.Wf.
Require Export Iron.SystemF2Effect.Type.Ty.
Require Export Iron.SystemF2Effect.Store.Prop.


(* Only types of effect and closure kinds can be used in sums. *)
Definition sumkind (k : ki) : Prop
 := k = KEffect.
Hint Unfold sumkind.


(* Region kinds cannot be the result of type applications. *)
Definition appkind (k : ki) : Prop
 := ~ (k = KRegion).
Hint Unfold appkind.


(* Kinds judgement assigns a kind to a type *)
Inductive KIND : kienv -> stprops -> ty -> ki -> Prop :=
  | KiVar
    :  forall ke sp i k
    ,  get i ke = Some k
    -> KIND ke sp (TVar i) k

  | KiForall
    :  forall ke sp k t
    ,  KIND (ke :> k) sp t KData
    -> KIND ke        sp (TForall k t) KData

  | KiApp 
    :  forall ke sp t1 t2 k11 k12
    ,  appkind k12
    -> KIND ke sp t1 (KFun k11 k12)
    -> KIND ke sp t2 k11
    -> KIND ke sp (TApp t1 t2) k12

  | KiSum
    :  forall ke sp k t1 t2
    ,  sumkind k
    -> KIND ke sp t1 k -> KIND ke sp t2 k
    -> KIND ke sp (TSum t1 t2) k

  | KiBot
    :  forall ke sp k
    ,  sumkind k
    -> KIND ke sp (TBot k) k

  | KiCon0
    :  forall ke sp tc k
    ,  k = kindOfTyCon0 tc
    -> KIND ke sp (TCon0 tc) k

  | KiCon1 
    :  forall ke sp tc t1 k1 k
    ,  KFun k1 k = kindOfTyCon1 tc
    -> KIND ke sp t1 k1
    -> KIND ke sp (TCon1 tc t1) k

  | KiCon2 
    :  forall ke sp tc t1 t2 k1 k2 k
    ,  KFun k1 (KFun k2 k) = kindOfTyCon2 tc
    -> KIND ke sp t1 k1
    -> KIND ke sp t2 k2
    -> KIND ke sp (TCon2 tc t1 t2) k

  | KiCap
    :  forall ke sp n
    ,  In (SRegion n) sp
    -> KIND ke sp (TCap (TyCapRegion n)) KRegion.

Hint Constructors KIND.


(* Invert all hypothesis that are compound kinding statements. *)
Ltac inverts_kind :=
 repeat 
  (match goal with 
   | [ H: KIND _ _ (TVar _)      _  |- _ ] => inverts H
   | [ H: KIND _ _ (TForall _ _) _  |- _ ] => inverts H
   | [ H: KIND _ _ (TApp _ _)    _  |- _ ] => inverts H
   | [ H: KIND _ _ (TSum _ _)    _  |- _ ] => inverts H
   | [ H: KIND _ _ (TBot _ )     _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon0 _)     _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon1 _ _)   _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon2 _ _ _) _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCap _)      _  |- _ ] => inverts H
   end).


(********************************************************************)
(* A well kinded type is well formed *)
Lemma kind_wfT
 :  forall ke sp t k
 ,  KIND   ke sp t k
 -> wfT (length ke) t.
Proof.
 intros ke sp t k HK. gen ke sp k.
 induction t; intros; inverts_kind; burn.
 lets D: IHt H4. burn.
Qed.
Hint Resolve kind_wfT.


Lemma kind_wfT_Forall
 :  forall ks sp k ts
 ,  Forall (fun t => KIND ks sp t k) ts
 -> Forall (wfT (length ks)) ts.
Proof.
 intros. norm. eauto.
Qed.
Hint Resolve kind_wfT_Forall.


Lemma kind_wfT_Forall2
 :  forall  (ke: kienv) (sp: stprops) ts ks
 ,  Forall2 (KIND ke sp) ts ks
 -> Forall  (wfT (length ke)) ts.
Proof.
 intros.
 eapply (Forall2_Forall_left (KIND ke sp)); burn.
Qed.
Hint Resolve kind_wfT_Forall2.


(********************************************************************)
(* Forms of types *)
Lemma kind_region
 :  forall t sp
 ,  KIND nil sp t KRegion
 -> (exists n, t = TCap (TyCapRegion n)).
Proof.
 intros.
 destruct t; burn.

  Case "TApp".
   inverts_kind.
   false. auto.

  Case "TCon0".
   destruct t; nope.

  Case "TCon1".
   destruct t; nope.

  Case "TCon2".
   destruct t1; nope.
   inverts_kind.
    destruct tc. simpl in *. nope.

  Case "TCap".
   destruct t.
   exists n. auto.
Qed.
Hint Resolve kind_region.


(********************************************************************)
(* If a type is well kinded in an empty environment,
   then that type is closed. *)
Lemma kind_empty_is_closed
 :  forall sp t k
 ,  KIND   nil sp t k 
 -> closedT t.
Proof.
 intros. unfold closedT.
 have (@length ki nil = 0).
  rewrite <- H0.
  eapply kind_wfT. eauto.
Qed.
Hint Resolve kind_empty_is_closed.


(********************************************************************)
(* Weaken kind environment in kind judgement. *)
Lemma kind_kienv_insert
 :  forall ke sp ix t k1 k2
 ,  KIND   ke sp t k1
 -> KIND   (insert ix k2 ke) sp (liftTT 1 ix t) k1.
Proof.
 intros. gen ix ke sp k1.
 induction t; intros; simpl; inverts_kind; eauto.

 Case "TVar".
  lift_cases; intros; norm; auto.

 Case "TForall".
  apply KiForall.
  rewrite insert_rewind. auto.

 Case "TCon2".
  eapply KiCon2.
  destruct t1.
   destruct tc. eauto.
  destruct tc. eauto.
  destruct tc. eauto.
Qed.


Lemma kind_kienv_weaken
 :  forall ke sp t k1 k2
 ,  KIND   ke sp        t              k1
 -> KIND  (ke :> k2) sp (liftTT 1 0 t) k1.
Proof.
 intros.
 rrwrite (ke :> k2 = insert 0 k2 ke).
 apply kind_kienv_insert. auto.
Qed.


(********************************************************************)
(* Weaken store properties in kind judgement. *)
Lemma kind_stprops_snoc
 : forall ke sp p t k
 ,  KIND ke sp        t k
 -> KIND ke (p <: sp) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.

 Case "TCon2".
  destruct tc. norm. inverts H2. 
  eapply KiCon2.
  destruct t1. simpl in *. eauto.
  eauto. eauto.
Qed.


Lemma kind_stprops_cons
 :  forall ke sp p t k
 ,  KIND ke sp t k
 -> KIND ke (sp :> p) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.
  
 Case "TCon2".
  destruct tc. snorm. inverts H2.
  eapply KiCon2; eauto.
  destruct t1. snorm.
Qed.


