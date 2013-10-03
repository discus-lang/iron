
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.Base.


(* Weaken kind environment in kind judgement. *)
Lemma kind_kienv_insert
 :  forall ke sp ix t k1 k2
 ,  KindT   ke sp t k1
 -> KindT   (insert ix k2 ke) sp (liftTT 1 ix t) k1.
Proof.
 intros. gen ix ke sp k1.
 induction t; intros; simpl; inverts_kind; eauto.

 - Case "TVar".
   lift_cases; snorm.

 - Case "TForall".
   apply KiForall.
   rewrite insert_rewind. auto.

 - Case "TCon2".
   eapply KiCon2.
   destruct t1.
    destruct tc. eauto.
   destruct tc. eauto.
   destruct tc. eauto.
Qed.


Lemma kind_kienv_weaken
 :  forall ke sp t k1 k2
 ,  KindT   ke sp        t              k1
 -> KindT  (ke :> k2) sp (liftTT 1 0 t) k1.
Proof.
 intros.
 rrwrite (ke :> k2 = insert 0 k2 ke).
 apply kind_kienv_insert. auto.
Qed.
