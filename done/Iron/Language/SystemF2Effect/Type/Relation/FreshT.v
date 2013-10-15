
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.


(********************************************************************)
(* Region identifier is not mentioned in the given type. *)
Fixpoint FreshT (p : nat) (tt : ty) : Prop :=
 match tt with
 | TVar _               => True
 | TForall k t          => FreshT p t
 | TApp t1 t2           => FreshT p t1 /\ FreshT p t2
 | TSum t1 t2           => FreshT p t1 /\ FreshT p t2
 | TBot _               => True
 | TCon0 _              => True
 | TCon1 tc t1          => FreshT p t1
 | TCon2 tc t1 t2       => FreshT p t1 /\ FreshT p t2
 | TCap (TyCapRegion n) => ~(n = p)
 end.


(********************************************************************)
Lemma freshT_kind
 :  forall ke sp t k p
 ,  ~(In (SRegion p) sp)
 -> KindT  ke sp t k
 -> FreshT p t.
Proof.
 intros; gen ke k.
 induction t; snorm; inverts_kind; eauto 2.
 - unfold not in H.
   have HP: (p = p0 \/ not (p = p0)).
   destruct HP; subst; auto.
Qed.
Hint Resolve freshT_kind.


Lemma freshT_liftTT
 :  forall p n d t
 ,  FreshT p t
 =  FreshT p (liftTT n d t).
Proof.
 intros. gen n d.
 induction t; intros; espread; snorm; espread; eauto.
Qed.
Hint Resolve freshT_liftTT.

