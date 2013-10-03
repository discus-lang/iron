
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LowerTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.Base.


Lemma lowerTT_substTT
 :  forall ix t1 t1' t2
 ,  lowerTT ix    t1 = Some t1'
 -> substTT ix t2 t1 = t1'.
Proof.
 intros. gen ix t2 t1'.
 induction t1; intros; 
  try (solve [snorm; espread; nope]).
Qed.
Hint Resolve lowerTT_substTT.
Hint Rewrite lowerTT_substTT : global.


(* What a horrow show *)
Lemma lowerTT_substTT_liftTT
 :  forall t1 t1' d d' t2
 ,  lowerTT d t1 = Some t1'
 -> lowerTT d (substTT (1 + d + d') (liftTT 1 d t2) t1) 
       = Some (substTT (d + d')      t2              t1').
Proof.
 intros. gen d d' t2 t1'.
 induction t1; intros;
  try (solve [snorm]).

 Case "TVar".
  repeat (simpl in *; norm1); try nope; try omega.

 Case "TForall".
  snorm. repeat f_equal. 

   (* Goal 10 *)
   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t0.
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   rrwrite (S (S d + d') = S (S (d + d'))) in D.
   norm. rewrite D in HeqH0. snorm.

   (* Goal 8 *)
   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. 
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   rrwrite (S (S d + d') = S (S (d + d'))) in D.
   norm. rewrite D in HeqH0. nope.
 
 Case "TApp".
  snorm; nope.
   repeat (espread; burn); burn.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.

 Case "TSum".
  snorm; nope.
   repeat (espread; burn); burn.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.

 Case "TCon1".
  snorm; nope.
   repeat (espread; burn).
   erewrite IHt1 in *; eauto. nope.

 Case "TCon2".
  snorm; nope.
   repeat (espread; burn); burn.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.
Qed.


(* If we can lower a particular index then the term does not use it, 
   so we can delete the corresponding slot from the enviornment. *)
Lemma lower_type_type_ix
 :  forall ix ke sp t1 k1 t2
 ,  lowerTT ix t1 = Some t2
 -> KindT ke sp t1 k1
 -> KindT (delete ix ke) sp t2 k1.
Proof.
 intros. gen ix ke sp k1 t2.
 induction t1; intros; simpl;
  try (solve [inverts_kind; snorm; eauto; nope]).

 - Case "TVar".
   inverts_kind. snorm.
    SCase "n > ix".
     eapply KiVar.
     rewrite <- H4.
     destruct n.
      simpl. burn.
      simpl. norm. 

 - Case "TForall".
   inverts_kind. snorm. 
    eapply KiForall.
    rewrite delete_rewind.
    eauto.

 - Case "TCon2".
   inverts_kind. snorm.
   eapply KiCon2; eauto.
    destruct tc; destruct t; eauto.
Qed.


Lemma lower_type_type
 :  forall t1 t2 ke sp k1 k2
 ,  lowerTT 0 t1 = Some t2
 -> KindT (ke :> k1) sp t1 k2 
 -> KindT ke         sp t2 k2.
Proof.
 intros.
 lets D: lower_type_type_ix H H0.
 simpl in D. auto.
Qed.

