
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.Base.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.LowerTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.EquivT.


(********************************************************************)
(* Commuting substitutions. *)
Lemma substTT_substTT
 :  forall n m t1 t2 t3
 ,  substTT (n + m) t3 (substTT n t2 t1)
 =  substTT n (substTT (n + m) t3 t2)
              (substTT (1 + n + m) (liftTT 1 n t3) t1).
Proof.
 intros. gen n m t2 t3.
 induction t1; intros;
  try (solve [simpl; f_equal; rewritess; norm]).

 Case "TVar".
  repeat (simpl; split_match; repeat norm_nat_compare);
   first [omega | burn].

 Case "TForall".
  simpl.
  rewrite (IHt1 (S n) m). 
  rewrite (liftTT_substTT_1 0 (n + m)).
  rewrite (liftTT_liftTT_11 0 n).
  burn.
Qed.


(********************************************************************)
(* Substitution of types in types preserves kinding.
   Must also subst new new type into types in env higher than ix
   otherwise indices that reference subst type are broken, and 
   the resulting type env would not be well formed *)
Theorem subst_type_type_ix
 :  forall ix ke sp t1 k1 t2 k2
 ,  get ix ke = Some k2
 -> KindT ke sp t1 k1
 -> KindT (delete ix ke) sp t2 k2
 -> KindT (delete ix ke) sp (substTT ix t2 t1) k1.
Proof.
 intros. gen ix ke sp t2 k1 k2.
 induction t1; intros; simpl; inverts_kind; eauto.

 Case "TVar".
  fbreak_nat_compare.
  SCase "n = ix".
   rewrite H in H5.
   inverts H5. auto.

  SCase "n < ix".
   apply KiVar. rewrite <- H5.
   apply get_delete_above; auto.

  SCase "n > ix".
   apply KiVar. rewrite <- H5.
   destruct n.
    burn.
    simpl. nnat. apply get_delete_below. omega.

 Case "TForall".
  apply KiForall.
  rewrite delete_rewind.
  eapply IHt1; eauto.
   apply kind_kienv_weaken; auto.

 Case "TCon2".
  eapply KiCon2.
  destruct tc. simpl in *. inverts H4.
  destruct t.  simpl in *. eauto.
  eauto.
  destruct tc. simpl in *. inverts H4.
  eauto.
Qed.


Theorem subst_type_type
 :  forall ke sp t1 k1 t2 k2
 ,  KindT (ke :> k2) sp t1 k1
 -> KindT ke         sp t2 k2
 -> KindT ke sp (substTT 0 t2 t1) k1.
Proof.
 intros.
 unfold substTT.
 rrwrite (ke = delete 0 (ke :> k2)).
 eapply subst_type_type_ix; burn.
Qed.


(* If two types are equivalent, and we substitute some third type
   into both, then the result is also equivalent. *)
Lemma substTT_EquivT
 :  forall  ke sp t1 t2 t3 k3 k
 ,  KindT    ke sp t3 k3
 -> EquivT (ke :> k3) sp t1 t2 k
 -> EquivT  ke sp (substTT 0 t3 t1) (substTT 0 t3 t2) k.
Proof.
 intros ke sp t1 t2 t3 k3 k HK HE.
 have HK1: (KindT (ke :> k3) sp t1 k).
 have HK2: (KindT (ke :> k3) sp t2 k).
 remember (ke :> k3) as X.
 induction HE; subst.

 - Case "EqRefl".
   eapply EqRefl; 
    eauto using subst_type_type.
  
 - Case "EqSym".
   eapply EqSym;
    eauto using subst_type_type.

 - Case "EqTrans".
   eapply EqTrans with (t2 := substTT 0 t3 t2); eauto.

 - Case "EqSumCong".
   eapply EqSumCong; fold substTT. auto.
   eauto using subst_type_type.
   eauto using subst_type_type.

 - Case "EqSumBot".
   apply EqSumBot; fold substTT. auto.
   eauto using subst_type_type.

 - Case "EqSumIdemp".
   eapply EqSumIdemp. auto.
   eauto using subst_type_type.

 - Case "EqSumComm".
   eapply EqSumComm; fold substTT. auto.
   eauto using subst_type_type.
   eauto using subst_type_type. 

 - Case "EqSumAssoc".
   eapply EqSumAssoc; fold substTT. auto.
   eauto using subst_type_type.
   eauto using subst_type_type. 
   eauto using subst_type_type. 
Qed.   


