
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.SystemF2Effect.Store.Prop.


(* Type equivalence.
   The interesting cases all concern sums. *)
Inductive EquivT : kienv -> stprops -> ty -> ty -> ki -> Prop :=
 | EqRefl
   :  forall ke sp t k
   ,  KindT   ke sp t k
   -> EquivT ke sp t t k

 | EqSym
   :  forall ke sp t1 t2 k
   ,  KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> EquivT ke sp t1 t2 k
   -> EquivT ke sp t2 t1 k

 | EqTrans
   :  forall ke sp t1 t2 t3 k
   ,  EquivT ke sp t1 t2 k
   -> EquivT ke sp t2 t3 k
   -> EquivT ke sp t1 t3 k

 | EqSumCong
   :  forall ke sp t1 t1' t2 t2' k
   ,  sumkind k
   -> EquivT ke sp t1 t1' k
   -> EquivT ke sp t2 t2' k
   -> EquivT ke sp (TSum t1 t2) (TSum t1' t2') k

 | EqSumBot
   :  forall ke sp t k
   ,  sumkind k
   -> KindT   ke sp t k
   -> EquivT ke sp t (TSum t (TBot k)) k

 | EqSumIdemp
   :  forall ke sp t k
   ,  sumkind k
   -> KindT   ke sp t k
   -> EquivT ke sp t (TSum t t) k

 | EqSumComm
   :  forall ke sp t1 t2 t3 k
   ,  sumkind k
   -> KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> KindT   ke sp t3 k
   -> EquivT ke sp (TSum t1 t2)  (TSum t2 t1) k

 | EqSumAssoc
   :  forall ke sp t1 t2 t3 k
   ,  sumkind k
   -> KindT   ke sp t1 k
   -> KindT   ke sp t2 k
   -> KindT   ke sp t3 k
   -> EquivT ke sp (TSum t1 (TSum t2 t3))
                   (TSum (TSum t1 t2) t3) k.

Hint Constructors EquivT.


Lemma equivT_sum_left
 :  forall ke sp t k
 ,  sumkind k
 -> KindT   ke sp t k
 -> EquivT ke sp t (TSum (TBot k) t) k.
Proof.
 intros.
 eapply EqTrans.
  eapply EqSumBot; eauto.
  eauto.
Qed.
Hint Resolve equivT_sum_left.


Lemma equivT_kind_trans
 :  forall ke sp t1 t2 k
 ,  EquivT ke sp t1 t2 k
 -> KindT   ke sp t1 k
 -> KindT   ke sp t2 k.
Proof.
 intros.
 induction H; eauto.
 inverts H0. eauto.
Qed.


Lemma equivT_kind_left
 :  forall ke sp t1 t2 k
 ,  EquivT ke sp t1 t2 k
 -> KindT   ke sp t1 k.
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

