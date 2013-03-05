
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.EquivT.


(* Type subsumptinon.
   The interesting cases all concern sums. *)
Inductive SubsT : kienv -> stprops -> ty -> ty -> ki -> Prop :=
 | SbEquiv
   :  forall ke sp t1 t2 k
   ,  EquivT ke sp t1 t2 k
   -> SubsT  ke sp t1 t2 k

 | SbTrans
   :  forall ke sp t1 t2 t3 k
   ,  KIND   ke sp t1 k
   -> KIND   ke sp t2 k
   -> KIND   ke sp t3 k
   -> SubsT  ke sp t1 t2 k -> SubsT  ke sp t2 t3 k
   -> SubsT  ke sp t1 t3 k

 | SbBot
   :  forall ke sp t k
   ,  sumkind k
   -> KIND   ke sp t k
   -> SubsT  ke sp t (TBot k) k

 | SbSumAbove
   :  forall ke sp t1 t2 t3 k
   ,  sumkind k
   -> SubsT  ke sp t1 t2 k -> SubsT  ke sp t1 t3 k
   -> SubsT  ke sp t1 (TSum t2 t3) k

 | SbSumBelow
   :  forall ke sp t1 t2 t3 k
   ,  sumkind k
   -> KIND   ke sp t1 k
   -> KIND   ke sp t2 k
   -> KIND   ke sp t3 k
   -> SubsT  ke sp t1 t2 k
   -> SubsT  ke sp (TSum t1 t3) t2 k.

Hint Constructors SubsT.


(********************************************************************)
(* Kind projection *)
Lemma subsT_kind_left
 :  forall ke sp t1 t2 k
 ,  SubsT  ke sp t1 t2 k
 -> KIND   ke sp t1 k.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve subsT_kind_left.


Lemma subsT_kind_right
 :  forall ke sp t1 t2 k
 ,  SubsT  ke sp t1 t2 k
 -> KIND   ke sp t2 k.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve subsT_kind_right.


(********************************************************************)
(* Sumkind projection *)
Lemma subsT_sumkind_left
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp (TSum t1 t2) t3 k
 -> sumkind k.
Proof.
 intros.
 inverts H; eauto.
Qed.


Lemma subsT_sumkind_right
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp t1 (TSum t2 t3) k
 -> sumkind k.
Proof.
 intros.
 inverts H; eauto.
Qed.


(********************************************************************)
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


Lemma subsT_equiv_below
 :  forall ke sp t1 t2 t2' k
 ,  EquivT ke sp t2 t2' k
 -> SubsT  ke sp t1 t2  k
 -> SubsT  ke sp t1 t2' k.
Proof.
 intros.
 eapply SbTrans with (t1 := t1); eauto.
Qed.


(********************************************************************)
(* Subs sum lemmas *)
Lemma subsT_sum_comm_below
 :  forall ke sp t1 t2 t3 k
 ,  SubsT  ke sp t1 (TSum t2 t3) k
 -> SubsT  ke sp t1 (TSum t3 t2) k.
Proof.
 intros.
 eapply subsT_equiv_below with (t2 := TSum t2 t3).
  have HK: (KIND ke sp (TSum t2 t3) k). inverts HK.
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
  have HK: (KIND ke sp (TSum t1 t2) k). inverts HK.
  eapply EqSumComm; eauto.
  auto.
Qed.
Hint Resolve subsT_sum_comm_above.


Lemma subsT_sum_left
 : forall ke sp t1 t1' t2 k
 ,  sumkind k
 -> KIND   ke sp t2 k
 -> SubsT  ke sp t1 t1' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1' t2) k.
Proof.
 intros.
 eapply SbSumAbove; eauto.
  eapply SbTrans with (t2 := TSum t2 t1); eauto.
Qed.
Hint Resolve subsT_sum_left.


Lemma subsT_sum_right
 :  forall ke sp t1 t2 t2' k
 ,  sumkind k
 -> KIND   ke sp t1 k
 -> SubsT  ke sp t2 t2' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1 t2') k.
Proof.
 intros.
 eapply SbSumAbove; eauto.
Qed.
Hint Resolve subsT_sum_right.


Lemma subsT_sum_merge
 :  forall ke sp t1 t1' t2 t2' k
 ,  sumkind k
 -> SubsT  ke sp t1 t1' k
 -> SubsT  ke sp t2 t2' k
 -> SubsT  ke sp (TSum t1 t2) (TSum t1' t2') k.
Proof.
 intros.
 eapply SbTrans with (t2 := TSum t1' t2); eauto.
Qed.
Hint Resolve subsT_sum_merge.

