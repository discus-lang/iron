
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Store.Prop.


(********************************************************************)
(* Type equivalence.
   The interesting cases all concern sums. *)
Inductive EquivT : kienv -> stprops -> ty -> ty -> ki -> Prop :=
 | EqRefl
   :  forall  ke sp t k
   ,  KindT   ke sp t k
   -> EquivT  ke sp t t k

 | EqSym
   :  forall  ke sp t1 t2 k
   ,  KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> EquivT  ke sp t1 t2 k
   -> EquivT  ke sp t2 t1 k

 | EqTrans
   :  forall  ke sp t1 t2 t3 k
   ,  EquivT  ke sp t1 t2 k
   -> EquivT  ke sp t2 t3 k
   -> EquivT  ke sp t1 t3 k

 | EqSumCong
   :  forall  ke sp t1 t1' t2 t2' k
   ,  SumKind k
   -> EquivT  ke sp t1 t1' k
   -> EquivT  ke sp t2 t2' k
   -> EquivT  ke sp (TSum t1 t2) (TSum t1' t2') k

 | EqSumBot
   :  forall ke sp t k
   ,  SumKind k
   -> KindT   ke sp t k
   -> EquivT  ke sp t (TSum t (TBot k)) k

 | EqSumIdemp
   :  forall  ke sp t k
   ,  SumKind k
   -> KindT   ke sp t k
   -> EquivT  ke sp t (TSum t t) k

 | EqSumComm
   :  forall ke sp t1 t2 k
   ,  SumKind k
   -> KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> EquivT  ke sp (TSum t1 t2)  (TSum t2 t1) k

 | EqSumAssoc
   :  forall ke sp t1 t2 t3 k
   ,  SumKind k
   -> KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> KindT   ke sp t3 k
   -> EquivT  ke sp (TSum t1 (TSum t2 t3))
                    (TSum (TSum t1 t2) t3) k.

Hint Constructors EquivT.


(********************************************************************)
Lemma equivT_sum_left
 :  forall ke sp t k
 ,  SumKind k
 -> KindT   ke sp t k
 -> EquivT ke sp t (TSum (TBot k) t) k.
Proof.
 intros.
 eapply EqTrans.
  eapply EqSumBot; eauto.
  eauto.
Qed.
Hint Resolve equivT_sum_left.


Lemma equivT_kind_left
 :  forall ke sp t1 t2 k
 ,  EquivT ke sp t1 t2 k
 -> KindT  ke sp t1 k.
Proof.
 intros. 
 induction H; eauto.
Qed.
Hint Resolve equivT_kind_left.


Lemma equivT_kind_right
 :  forall ke sp t1 t2 k
 ,  EquivT ke sp t1 t2 k
 -> KindT   ke sp t2 k.
Proof.
 intros. 
 induction H; eauto.
Qed.  
Hint Resolve equivT_kind_right.


Lemma equivT_kind_trans
 :  forall ke sp t1 t2 k
 ,  EquivT ke sp t1 t2 k
 -> KindT   ke sp t1 k
 -> KindT   ke sp t2 k.
Proof.
 intros.
 induction H; eauto.
Qed.


Lemma equivT_stprops_snoc
 :  forall ke sp p e1 e2 k
 ,  EquivT ke sp        e1 e2 k
 -> EquivT ke (p <: sp) e1 e2 k.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve equivT_stprops_snoc.


Lemma equivT_stprops_app
 :  forall ke sp sp' e1 e2 k
 ,  EquivT ke sp e1 e2 k
 -> EquivT ke (sp' >< sp) e1 e2 k.
Proof.
 intros. gen ke sp k.
 induction sp'; intros; burn.
 - rrwrite ((sp' :> a) >< sp = sp' >< (a <: sp)).
   burn.
Qed.
Hint Resolve equivT_stprops_app.


Lemma equivT_stprops_extends 
 :  forall ke sp sp' e1 e2 k
 ,  extends sp' sp
 -> EquivT ke sp  e1 e2 k
 -> EquivT ke sp' e1 e2 k.
Proof.
 intros.
 unfold extends in *.
 destruct H. subst.
 snorm.
Qed.


Lemma equivT_closed_kenv_cons
 :  forall sp t1 t2 k1 k2
 ,  EquivT nil sp t1 t2 k1
 -> EquivT (nil :> k2) sp t1 t2 k1.
Proof.
 intros.
 remember nil as ke.
 induction H; subst; eauto 4.

 - Case "EqRefl".
   have (ClosedT t).
   eapply kind_kienv_weaken in H.
   rrwrite (liftTT 1 0 t = t).
   eauto.

 - Case "EqSym".
   have (nil = @nil (list ki)).
   eapply EqSym.
    + have (ClosedT t1).
      eapply kind_kienv_weaken in H.
      rrwrite (liftTT 1 0 t1 = t1). eauto.
    + have (ClosedT t2).
      eapply kind_kienv_weaken in H0.
      rrwrite (liftTT 1 0 t2 = t2). eauto.
    + auto.

 - Case "EqSumBot".
   eapply EqSumBot; auto.
   have (ClosedT t).
   eapply kind_kienv_weaken in H0.
   rrwrite (liftTT 1 0 t = t). eauto.

 - Case "EqSumIdemp".
   eapply EqSumIdemp; auto.
   have (ClosedT t).
   eapply kind_kienv_weaken in H0.
   rrwrite (liftTT 1 0 t = t). eauto.

 - Case "EqSumComm".
   eapply EqSumComm; auto.
   have (ClosedT t1).
    eapply kind_kienv_weaken in H0.
    rrwrite (liftTT 1 0 t1 = t1). eauto.
   have (ClosedT t2).
    eapply kind_kienv_weaken in H1.
    rrwrite (liftTT 1 0 t2 = t2). eauto.

 - Case "EqSumAssoc".
   eapply EqSumAssoc; auto.
   have (ClosedT t1).
    eapply kind_kienv_weaken in H0.
    rrwrite (liftTT 1 0 t1 = t1). eauto.
   have (ClosedT t2).
    eapply kind_kienv_weaken in H1.
    rrwrite (liftTT 1 0 t2 = t2). eauto.
   have (ClosedT t3).
    eapply kind_kienv_weaken in H2.
    rrwrite (liftTT 1 0 t3 = t3). eauto.
Qed.
Hint Resolve equivT_closed_kenv_cons.


