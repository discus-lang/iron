
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.Base.


(* A well kinded type is well formed *)
Lemma kind_wfT
 :  forall ke sp t k
 ,  KindT   ke sp t k
 -> WfT (length ke) t.
Proof.
 intros ke sp t k HK. gen ke sp k.
 induction t; intros; inverts_kind; burn.
 lets D: IHt H4. burn.
Qed.
Hint Resolve kind_wfT.


Lemma kind_wfT_Forall
 :  forall ks sp k ts
 ,  Forall (fun t => KindT ks sp t k) ts
 -> Forall (WfT (length ks)) ts.
Proof.
 intros. norm. eauto.
Qed.
Hint Resolve kind_wfT_Forall.


Lemma kind_wfT_Forall2
 :  forall  (ke: kienv) (sp: stprops) ts ks
 ,  Forall2 (KindT ke sp) ts ks
 -> Forall  (WfT (length ke)) ts.
Proof.
 intros.
 eapply (Forall2_Forall_left (KindT ke sp)); burn.
Qed.
Hint Resolve kind_wfT_Forall2.


(* If a type is well kinded in an empty environment,
   then that type is closed. *)
Lemma kind_empty_is_closed
 :  forall sp t k
 ,  KindT   nil sp t k 
 -> ClosedT t.
Proof.
 intros.
 have (@length ki nil = 0).
  rewrite <- H0.
  eapply kind_wfT. eauto.
Qed.
Hint Resolve kind_empty_is_closed.
