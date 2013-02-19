
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.KiJudge.


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
