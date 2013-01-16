
Require Export Iron.Language.SystemF2Effect.Kind.
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.


(* Substitution of types in types preserves kinding.
   Must also subst new new type into types in env higher than ix
   otherwise indices that reference subst type are broken, and 
   the resulting type env would not be well formed *)
Theorem subst_type_type_ix
 :  forall ix ke t1 k1 t2 k2
 ,  get ix ke = Some k2
 -> KIND ke t1 k1
 -> KIND (delete ix ke) t2 k2
 -> KIND (delete ix ke) (substTT ix t2 t1) k1.
Proof.
 intros. gen ix ke t2 k1 k2.
 induction t1; intros; simpl; inverts_kind; eauto.

 Case "TVar".
  fbreak_nat_compare.
  SCase "n = ix".
   rewrite H in H4.
   inverts H4. auto.

  SCase "n < ix".
   apply KiVar. rewrite <- H4.
   apply get_delete_above; auto.

  SCase "n > ix".
   apply KiVar. rewrite <- H4.
   destruct n.
    burn.
    simpl. nnat. apply get_delete_below. omega.

 Case "TForall".
  apply KiForall.
  rewrite delete_rewind.
  eapply IHt1; eauto.
   apply kind_kienv_weaken; auto.
Qed.


Theorem subst_type_type
 :  forall ke t1 k1 t2 k2
 ,  KIND (ke :> k2) t1 k1
 -> KIND ke         t2 k2
 -> KIND ke (substTT 0 t2 t1) k1.
Proof.
 intros.
 unfold substTT.
 rrwrite (ke = delete 0 (ke :> k2)).
 eapply subst_type_type_ix; burn.
Qed.


(* If we can lower a particular index then the term does not use it, 
   so we can delete the corresponding slot from the enviornment. *)
Theorem lower_type_type_ix
 :  forall ix ke t1 k1 t2
 ,  lowerTT ix t1 = Some t2
 -> KIND ke t1 k1
 -> KIND (delete ix ke) t2 k1.
Proof.
 intros. gen ix ke k1 t2.
 induction t1; intros; simpl.

 Case "TCon".
  inverts_kind. 
  norm.
  destruct t2; burn.
  inverts H. eauto.

 Case "TCap".
  inverts_kind.
  norm.
  destruct t2; burn.
  inverts H. eauto.

 Case "TVar".
  inverts_kind.
  simpl in H.
  remember (nat_compare n ix) as X.
  destruct X.
   SCase "n = ix".
    nope.

   SCase "n < ix".
    inverts H.
    eapply KiVar.
    norm.
    symmetry in HeqX.
    apply nat_compare_lt in HeqX.
    burn.

   SCase "n > ix".
    inverts H.
    eapply KiVar.
    rewrite <- H3.
    symmetry in HeqX.
    apply nat_compare_gt in HeqX.
    destruct n.
     simpl. burn.
     simpl. norm. eapply get_delete_below. omega.

 Case "TForall".
  inverts_kind. norm.
  remember (lowerTT (S ix) t1) as X.
  destruct X.
   inverts H.
   eapply KiForall.
   rewrite delete_rewind. eauto.
   false.

 Case "TApp".
  inverts_kind. norm.
  remember (lowerTT ix t1_1) as X1.
  remember (lowerTT ix t1_2) as X2.
  destruct X1. destruct X2.
  inverts H.
   spec IHt1_1 H5. eauto.
   nope. nope.

 Case "TSum".
  inverts_kind. norm.
  remember (lowerTT ix t1_1) as X1.
  remember (lowerTT ix t1_2) as X2.
  destruct X1. destruct X2.
  inverts H.
   spec IHt1_1 H5. eauto.
   nope. nope.

 Case "TBot".
  inverts_kind. norm.
  inverts H.
  auto.
Qed.


Theorem lower_type_type_snoc
 :  forall t1 t2 ke k1 k2
 ,  lowerTT 0 t1 = Some t2
 -> KIND (ke :> k1) t1 k2 
 -> KIND ke         t2 k2.
Proof.
 intros.
 lets D: lower_type_type_ix H H0.
 simpl in D. auto.
Qed.

