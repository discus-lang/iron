
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.


(* Region identifier is fresh with respect to a type. *)
Fixpoint freshT (p : nat) (tt : ty) : Prop :=
 match tt with
 | TVar _               => True
 | TForall k t          => freshT p t
 | TApp t1 t2           => freshT p t1 /\ freshT p t2
 | TSum t1 t2           => freshT p t1 /\ freshT p t2
 | TBot _               => True
 | TCon0 _              => True
 | TCon1 tc t1          => freshT p t1
 | TCon2 tc t1 t2       => freshT p t1 /\ freshT p t2
 | TCap (TyCapRegion n) => beq_nat n p = false
 end.


Lemma freshT_kind
 : forall ke sp t k p
 ,  not (In (SRegion p) sp)
 -> KindT ke sp t k
 -> freshT p t.
Proof.
 intros; gen ke k.
 induction t; snorm; inverts_kind; eauto 2.
 - unfold not in H.
   have HP: (p = p0 \/ not (p = p0)). 
   destruct HP.
   + subst. tauto.
   + rewrite beq_nat_false_iff. firstorder.
Qed.
Hint Resolve freshT_kind.


Lemma freshT_liftTT
 :  forall p n d t
 ,  freshT p t
 =  freshT p (liftTT n d t).
Proof.
 intros. gen n d.
 induction t; intros; espread; snorm; espread; eauto.
Qed.
Hint Resolve freshT_liftTT.

