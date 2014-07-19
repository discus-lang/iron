
Require Export Iron.Language.SystemF2Cap.Type.Relation.KindT.Base.


(* Weaken kind environment in kind judgement. *)
Lemma kind_kienv_insert
 :  forall ke sp ix t k1 k2 o2
 ,  KindT  ke sp t k1
 -> KindT  (insert ix (o2, k2) ke) sp (liftTT 1 ix t) k1.
Proof.
 intros. gen ix ke sp k1.
 induction t; intros; simpl; inverts_kind; eauto.

 - Case "TVar".
   destruct H3 as [o1].
   lift_cases.
   + eapply KiVar. exists o1. snorm.
   + eapply KiVar. exists o1. snorm.
   + eapply KiVar. exists o1. snorm.

 - Case "TForall".
   apply KiForall.
   rewrite insert_rewind. auto.
Qed.


Lemma kind_kienv_weaken
 :  forall ke sp t k1 o2 k2
 ,  KindT   ke sp           t                 k1
 -> KindT  (ke :> (o2, k2)) sp (liftTT 1 0 t) k1.
Proof.
 intros.
 rrwrite (ke :> (o2, k2) = insert 0 (o2, k2) ke).
 apply kind_kienv_insert. auto.
Qed.

