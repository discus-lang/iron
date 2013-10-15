
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Operator.FlattenT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindTs.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivTs.


(********************************************************************)
Fixpoint bunchT (k : ki) (tt : list ty) : ty
 := match tt with
    | nil           => TBot k
    | t :: ts       => TSum t (bunchT k ts)
    end.


(********************************************************************)
Lemma bunchT_kindT
 :  forall ke sp ts k
 ,  SumKind k
 -> KindTs ke sp ts k
 -> KindT  ke sp (bunchT k ts) k.
Proof.
 intros.
 induction ts.
 - simpl. eauto.
 - inverts H0.
   eapply KiSum; eauto.
Qed.
Hint Resolve bunchT_kindT.


Lemma bunchT_kindTs
 :  forall ke sp ts k
 ,  KindT  ke sp (bunchT k ts) k
 -> KindTs ke sp ts k.
Proof.
 intros.
 induction ts.
 - auto.
 - unfold KindTs.
   snorm.
   inverts H0.
   + inverts H. auto.
   + inverts H. rip.
     unfold KindTs in *. snorm.
Qed.     
Hint Resolve bunchT_kindTs.


Lemma bunchT_singleton
 :  forall ke sp t k
 ,  SumKind k
 -> KindT ke sp t k
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
 ,  SumKind k
 -> KindTs ke sp ts1 k
 -> KindTs ke sp ts2 k
 -> EquivT ke sp (bunchT k (ts2 >< ts1)) 
                 (TSum (bunchT k ts1) (bunchT k ts2)) k.
Proof.
 intros. 
 induction ts1. 
 - simpl.
   eapply EqSym; auto.
 - have (KindTs ke sp ts1 k). rip.
   have (KindT  ke sp a   k).
   simpl.
   eapply EqTrans 
    with (t2 := TSum a (TSum (bunchT k ts1) (bunchT k ts2))).
   + eapply EqSumCong; auto.
   + eapply EqSumAssoc; auto.
Qed.
Hint Resolve bunchT_sum.


Lemma bunchT_flattenT_sum
 :  forall ke sp k t1 t2
 ,  SumKind k
 -> EquivT ke sp (bunchT k (flattenT t1)) t1 k
 -> EquivT ke sp (bunchT k (flattenT t2)) t2 k
 -> EquivT ke sp (bunchT k (flattenT t2 >< flattenT t1)) (TSum t1 t2) k.
Proof.
 intros.
 eapply EqTrans.
 - eapply bunchT_sum; eauto.
 - eapply EqSumCong; eauto.
Qed.


Lemma bunchT_flattenT
 :  forall ke sp t k
 ,  SumKind k
 -> KindT   ke sp t k
 -> EquivT  ke sp (bunchT k (flattenT t)) t k.
Proof.
 induction t; intros; simpl; snorm.

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


(* The converse is not true.
   If 'ts' contains  '(TSum t1 t2)'  this will be eliminated 
   by 'flattenT . bunchT', then the EqsSum check fails.  
Lemma flattenT_bunchT
 :  forall  ke sp ts k
 ,  SumKind k
 -> KindTs  ke sp ts k
 -> EquivTs ke sp (flattenT (bunchT k ts)) ts k.
*)

