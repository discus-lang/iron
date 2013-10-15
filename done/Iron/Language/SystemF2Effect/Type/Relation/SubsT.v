
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivT.


(********************************************************************)
(* Type subsumptinon.
   The interesting cases all concern sums. *)
Inductive SubsT : kienv -> stprops -> ty -> ty -> ki -> Prop :=
 | SbEquiv
   :  forall  ke sp t1 t2 k
   ,  EquivT  ke sp t1 t2 k
   -> SubsT   ke sp t1 t2 k

 | SbTrans
   :  forall  ke sp t1 t2 t3 k
   ,  SubsT   ke sp t1 t2 k -> SubsT  ke sp t2 t3 k
   -> SubsT   ke sp t1 t3 k

 | SbBot
   :  forall  ke sp t k
   ,  SumKind k
   -> KindT   ke sp t k
   -> SubsT   ke sp t (TBot k) k

 | SbSumAbove
   :  forall  ke sp t1 t2 t3 k
   ,  SumKind k
   -> SubsT   ke sp t1 t2 k -> SubsT  ke sp t1 t3 k
   -> SubsT   ke sp t1 (TSum t2 t3) k

 | SbSumBelow
   :  forall  ke sp t1 t2 t3 k
   ,  SumKind k
   -> KindT   ke sp t3 k
   -> SubsT   ke sp t1 t2 k
   -> SubsT   ke sp (TSum t1 t3) t2 k

 | SbSumAboveLeft
   :  forall  ke sp t1 t2 t3 k
   ,  SumKind k
   -> SubsT   ke sp t1 (TSum t2 t3) k
   -> SubsT   ke sp t1 t2 k

 | SbSumAboveRight
   :  forall  ke sp t1 t2 t3 k
   ,  SumKind k
   -> SubsT   ke sp t1 (TSum t2 t3) k
   -> SubsT   ke sp t1 t3 k.

Hint Constructors SubsT.


(********************************************************************)
(* Kind projection *)
Lemma subsT_kind_left
 :  forall ke sp t1 t2 k
 ,  SubsT  ke sp t1 t2 k
 -> KindT  ke sp t1 k.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve subsT_kind_left.


Lemma subsT_kind_right
 :  forall ke sp t1 t2 k
 ,  SubsT  ke sp t1 t2 k
 -> KindT  ke sp t2 k.
Proof.
 intros.
 induction H; eauto.
  inverts IHSubsT. eauto.
  inverts IHSubsT. eauto.
Qed.
Hint Resolve subsT_kind_right.


(* Sumkind projection *)
Lemma subsT_sumkind_left
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp (TSum t1 t2) t3 k
 -> SumKind k.
Proof.
 intros.
 inverts H; eauto.
Qed.
Hint Resolve subsT_sumkind_left.


Lemma subsT_sumkind_right
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp t1 (TSum t2 t3) k
 -> SumKind k.
Proof.
 intros.
 inverts H; eauto.
Qed.
Hint Resolve subsT_sumkind_right.


(* Subs/Equiv *)
Lemma subsT_equiv_above
 :  forall ke sp t1 t1' t2 k
 ,  EquivT ke sp t1  t1' k
 -> SubsT  ke sp t1  t2  k 
 -> SubsT  ke sp t1' t2  k.
Proof.
 intros. 
 eapply SbTrans with (t2 := t1); eauto.
Qed.
Hint Resolve subsT_equiv_above.


Lemma subsT_equiv_below
 :  forall ke sp t1 t2 t2' k
 ,  EquivT ke sp t2 t2' k
 -> SubsT  ke sp t1 t2  k
 -> SubsT  ke sp t1 t2' k.
Proof.
 intros.
 eapply SbTrans with (t1 := t1); eauto.
Qed.
Hint Resolve subsT_equiv_below.


(* Subs sum lemmas *)
Lemma subsT_sum_comm_below
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp t1 (TSum t2 t3) k
 -> SubsT  ke sp t1 (TSum t3 t2) k.
Proof.
 intros.
 eapply subsT_equiv_below with (t2 := TSum t2 t3).
  have HK: (KindT ke sp (TSum t2 t3) k). inverts HK.
  eapply EqSumComm; eauto.
  auto.
Qed.
Hint Resolve subsT_sum_comm_below.


Lemma subsT_sum_comm_above
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp (TSum t1 t2) t3 k
 -> SubsT  ke sp (TSum t2 t1) t3 k.
Proof.
 intros.
 eapply subsT_equiv_above with (t1 := TSum t1 t2).
  have HK: (KindT ke sp (TSum t1 t2) k). inverts HK.
  eapply EqSumComm; eauto.
  auto.
Qed.
Hint Resolve subsT_sum_comm_above.


Lemma subsT_sum_left
 : forall ke sp t1 t1' t2 k
 ,  SumKind k
 -> KindT  ke sp t2 k
 -> SubsT  ke sp t1 t1' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1' t2) k.
Proof.
 intros.
 eapply SbSumAbove; eauto.
Qed.
Hint Resolve subsT_sum_left.


Lemma subsT_sum_right
 :  forall ke sp t1 t2 t2' k
 ,  SumKind k
 -> KindT   ke sp t1 k
 -> SubsT  ke sp t2 t2' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1 t2') k.
Proof.
 intros.
 eapply SbSumAbove; eauto.
Qed.
Hint Resolve subsT_sum_right.


Lemma subsT_sum_merge
 :  forall ke sp t1 t1' t2 t2' k
 ,  SumKind k
 -> SubsT  ke sp t1 t1' k
 -> SubsT  ke sp t2 t2' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1' t2') k.
Proof.
 intros.
 eapply SbTrans with (t2 := TSum t1' t2); eauto.
Qed.
Hint Resolve subsT_sum_merge.


Lemma subsT_stprops_snoc
 :  forall ke sp p t1 t2 k
 ,  SubsT  ke sp        t1 t2 k
 -> SubsT  ke (p <: sp) t1 t2 k.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve subsT_stprops_snoc.


Lemma subsT_stprops_app
 :  forall ke sp sp' t1 t2 k
 ,  SubsT ke sp          t1 t2 k
 -> SubsT ke (sp' >< sp) t1 t2 k.
Proof.
 intros. gen ke sp k.
 induction sp'; intros; snorm; auto.
 - rrwrite ((sp' :> a) >< sp = sp' >< (a <: sp)).
   snorm.
Qed.
Hint Resolve subsT_stprops_app.


Lemma subsT_stprops_extends
 :  forall ke sp sp' e1 e2 k
 ,  extends sp' sp
 -> SubsT ke sp  e1 e2 k
 -> SubsT ke sp' e1 e2 k.
Proof.
 intros.
 unfold extends in *.
 destruct H. subst.
 snorm.
Qed.


Lemma subsT_closed_kenv_cons
 :  forall sp t1 t2 k1 k2
 ,  SubsT nil sp t1 t2 k1
 -> SubsT (nil :> k2) sp t1 t2 k1.
Proof.
 intros. 
 remember nil as KE.
 induction H; subst; eauto 4.

 - Case "SbBot".
   eapply SbBot; auto.
   have (ClosedT t).
   eapply kind_kienv_weaken in H0.
   rrwrite (liftTT 1 0 t = t).
   eauto.

 - Case "SbSumAbove".
   eapply SbSumBelow; auto.
   have (ClosedT t3).
   eapply kind_kienv_weaken in H0.
   rrwrite (liftTT 1 0 t3 = t3).
   eauto.
Qed.
Hint Resolve subsT_closed_kenv_cons.

