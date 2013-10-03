
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.


(********************************************************************)
Definition KindTs (ke : kienv) (sp : stprops) (ts : list ty) k
 := Forall (fun t => KindT ke sp t k) ts.
Hint Unfold KindTs.


(********************************************************************)
Lemma kindTs_head
 :  forall ke sp ts t k
 ,  KindTs ke sp (ts :> t) k
 -> KindT  ke sp t k.
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve kindTs_head.


Lemma kindTs_tail
 :  forall ke sp ts t k
 ,  KindTs ke sp (ts :> t) k
 -> KindTs ke sp ts k.
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve kindTs_tail.


Lemma kindTs_snoc 
 :  forall ke sp ts t k
 ,  KindTs ke sp (ts :> t) k
 -> KindTs ke sp ts k 
 /\ KindT  ke sp t k.
Proof. eauto. Qed.
Hint Resolve kindTs_snoc.


Lemma kindTs_app
 :  forall ke sp ts1 ts2 k
 ,  KindTs ke sp ts1 k
 -> KindTs ke sp ts2 k
 -> KindTs ke sp (ts1 ++ ts2) k.
Proof.
 intros.
 unfold KindTs in *. snorm.
Qed.
Hint Resolve kindTs_app.
