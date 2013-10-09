
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.FreshT.


Fixpoint mergeT (p1 p2 : nat) (tt : ty)  : ty :=
 match tt with
 | TVar    _            => tt
 | TForall k t          => TForall k (mergeT p1 p2 t)
 | TApp    t1 t2        => TApp (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TSum    t1 t2        => TSum (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TBot    k            => TBot k
 | TCon0   tc0          => TCon0 tc0
 | TCon1   tc1 t1       => TCon1 tc1 (mergeT p1 p2 t1)
 | TCon2   tc2 t1 t2    => TCon2 tc2 (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TCap (TyCapRegion p) => if beq_nat p p2 then TRgn p1 else tt
 end.


Lemma mergeT_freshT_id
 :  forall p1 p2 t
 ,  freshT p2 t
 -> mergeT p1 p2 t = t.
Proof.
 intros. 
 induction t; snorm; rewritess; auto.
 - destruct t. snorm. nope.
Qed.


Lemma mergeT_substTT
 :  forall ke sp t k p1 p2 ix
 ,  freshT p2 t
 -> KindT ke sp t k
 -> mergeT p1 p2 (substTT ix (TRgn p2) t)
 =  substTT ix (TRgn p1) t.
Proof.
 intros. gen ix ke k.
 induction t; snorm;
  try (inverts H0; espread; eauto).
 - nope.
Qed.


