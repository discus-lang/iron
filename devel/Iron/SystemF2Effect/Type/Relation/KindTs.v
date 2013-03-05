
Require Export Iron.SystemF2Effect.Type.Relation.KindT.

Definition KindTs (ke : kienv) (sp : stprops) (ts : list ty) k
 := Forall (fun t => KindT ke sp t k) ts.
Hint Unfold KindTs.


Lemma KindTs_head
 :  forall ke sp ts t k
 ,  KindTs ke sp (ts :> t) k
 -> KindT  ke sp t k.
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve KindTs_head.


Lemma KindTs_tail
 :  forall ke sp ts t k
 ,  KindTs ke sp (ts :> t) k
 -> KindTs ke sp ts k.
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve KindTs_tail.

