
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Operator.FlattenT.
Require Export Iron.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.SystemF2Effect.Type.Relation.EquivTs.


Fixpoint bunchT (k : ki) (tt : list ty) : ty
 := match tt with
    | nil           => TBot k
    | t :: ts       => TSum t (bunchT k ts)
    end.


Lemma bunchT_kind
 :  forall ke sp ts k
 ,  sumkind k
 -> Forall (fun t => KIND ke sp t k) ts
 -> KIND ke sp (bunchT k ts) k.
Proof.
 intros.
 induction ts.
  simpl. eauto.
  eapply KiSum; eauto.
   norm.
   eapply IHts.
    inverts H0. auto.
Qed.
Hint Resolve bunchT_kind.


Definition KINDS (ke : kienv) (sp : stprops) (ts : list ty) k
 := Forall (fun t => KIND ke sp t k) ts.


Lemma bunchT_singleton
 :  forall ke sp t k
 ,  sumkind k
 -> KIND ke sp t k
 -> EquivT ke sp (bunchT k (t :: nil)) t k.
Proof.
 intros.
 simpl.
 eapply EqSym. 
  auto.
  auto.
  eapply EqSumBot; auto.
Qed.


Lemma bunchT_sum
 :  forall ke sp ts1 ts2 k
 ,  sumkind k
 -> KINDS ke sp ts1 k
 -> KINDS ke sp ts2 k
 -> EquivT ke sp (bunchT k (ts2 >< ts1)) 
                 (TSum (bunchT k ts1) (bunchT k ts2)) k.
Proof.
 intros. 
 induction ts1. simpl.
  eapply EqSym; auto.
  have (KINDS ke sp ts1 k) by admit. rip.
  simpl.
  eapply EqTrans 
   with (t2 := TSum a (TSum (bunchT k ts1) (bunchT k ts2))).
  eapply EqSumCong.
   auto. 
   admit.   (* ok kind *)
   auto.
  eapply EqSumAssoc.
   auto.
   admit.   (* ok kind *)
   admit.   (* ok kind *)
   admit.   (* ok kind *)
Qed.


Lemma bunchT_flattenT_sum
 :  forall ke sp k t1 t2
 ,  sumkind k
 -> EquivT ke sp (bunchT k (flattenT t1)) t1 k
 -> EquivT ke sp (bunchT k (flattenT t2)) t2 k
 -> EquivT ke sp (bunchT k (flattenT t2 >< flattenT t1)) (TSum t1 t2) k.
Proof.
 intros.
 eapply EqTrans.
  eapply bunchT_sum.
  auto.
  admit.  (* ok kind *)
  admit.  (* ok kind *)
 eapply EqSumCong; eauto.
Qed.


Lemma bunchT_flattenT
 :  forall ke sp t k
 ,  sumkind k
 -> KIND   ke sp t k
 -> EquivT ke sp (bunchT k (flattenT t)) t k.
Proof.
 induction t; intros; simpl; eauto.

 - Case "TSum".
   inverts H0.
   spec IHt1 k.
   spec IHt2 k.
   rip. 
   eapply bunchT_flattenT_sum; auto.

 - Case "TBot".
   inverts H0. eauto.
Qed.
Hint Resolve bunchT_flattenT.

