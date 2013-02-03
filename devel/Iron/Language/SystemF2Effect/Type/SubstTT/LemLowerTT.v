
Require Export Iron.Language.SystemF2Effect.Type.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.LowerTT.
Require Export Iron.Language.SystemF2Effect.Type.SubstTT.Base.


(********************************************************************)
Lemma lowerTT_substTT
 :  forall ix t1 t1' t2
 ,  lowerTT ix    t1 = Some t1'
 -> substTT ix t2 t1 = t1'.
Proof.
 intros. gen ix t2 t1'.
 induction t1; intros; try (solve [snorm]).

 Case "TForall".
  simpl in *.
  split_match; snorm; nope.
   snorm.
   symmetry in HeqH0. spec IHt1 HeqH0.
   repeat rewritess. auto.

 Case "TApp".
   snorm; try (solve [espread; nope]).
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess.  norm.

 Case "TSum".
   snorm; try (solve [espread; nope]).
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess.  norm.

 Case "TCon1".
   snorm; try (solve [espread; nope]).

 Case "TCon2".
   snorm; try (solve [espread; nope]).
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess.  norm.
Qed.
Hint Resolve lowerTT_substTT.
Hint Rewrite lowerTT_substTT : global.


(********************************************************************)
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

   (* Goal 9 *)
   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. 
   symmetry in HeqH1. rip.

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


