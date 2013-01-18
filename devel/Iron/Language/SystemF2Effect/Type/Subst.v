
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Type.Lift.
Require Import Iron.Language.SystemF2Effect.Type.Lower.


(********************************************************************)
(* Substitution of Types in Types. *)
Fixpoint substTT (d: nat) (u: ty) (tt: ty) : ty 
 := match tt with
    | TVar ix
    => match nat_compare ix d with
       | Eq          => u
       | Gt          => TVar (ix - 1)
       | _           => TVar  ix
       end

    |  TForall k t   => TForall k (substTT (S d) (liftTT 1 0 u) t)
    |  TApp t1 t2    => TApp      (substTT d u t1) (substTT d u t2)
    |  TSum t1 t2    => TSum      (substTT d u t1) (substTT d u t2)
    |  TBot k        => TBot k

    | TCon0 tc       => TCon0 tc
    | TCon1 tc t1    => TCon1 tc  (substTT d u t1)
    | TCon2 tc t1 t2 => TCon2 tc  (substTT d u t1) (substTT d u t2)
    | TCap _         => tt
  end.


(* What might happen when we substitute for a variable.
   This can be easier use than the raw substTT definition. *)
Lemma substTT_TVar_cases
 :  forall n1 n2 t1
 ,  (substTT n1 t1 (TVar n2) = t1            /\ n1 = n2)
 \/ (substTT n1 t1 (TVar n2) = TVar (n2 - 1) /\ n1 < n2)
 \/ (substTT n1 t1 (TVar n2) = TVar n2       /\ n1 > n2).
Proof.
 intros.
 unfold substTT.
  lift_cases; burn.
Qed. 


(********************************************************************)
Lemma substTT_wfT
 :  forall d ix t t2
 ,  wfT d t
 -> substTT (d + ix) t2 t = t.
Proof.
 intros. gen d ix t2.
 induction t; rip; inverts H; simpl; f_equal; burn.

 Case "TVar".
  norm; omega.
  lets D: IHt H1. burn.
Qed.
Hint Resolve substTT_wfT.


Lemma substTT_closedT_id
 :  forall d t t2
 ,  closedT t
 -> substTT d t2 t = t.
Proof.
 intros. rrwrite (d = d + 0). eauto.
Qed.
Hint Resolve substTT_closedT_id.


(* Substituting into TBot is still TBot. *)
Lemma substTT_TBot
 : forall d t2 k
 , substTT d t2 (TBot k) = TBot k.
Proof. burn. Qed.
Hint Resolve substTT_TBot.
Hint Rewrite substTT_TBot : global.


(********************************************************************)
(* If we lift at depth d, this creates an empty space and
   substituting into it doens't do anything. *)
Lemma substTT_liftTT
 :  forall d t1 t2
 ,  substTT d t2 (liftTT 1 d t1) = t1.
Proof.
 intros. gen d t2.
 induction t1; intros;
  first [ solve [snorm; try omega]
        | solve [simpl; f_equal; norm]].
Qed.
Hint Rewrite substTT_liftTT : global.


(********************************************************************)
(* Lifting after substitution,
   with the lifting at a lower index. *)
Lemma liftTT_substTT_1
 :  forall n n' t1 t2
 ,  liftTT 1 n (substTT (n + n') t2 t1)
 =  substTT (1 + n + n') (liftTT 1 n t2) (liftTT 1 n t1).
Proof.
 intros. gen n n' t2.
 induction t1; intros;
  try (solve [simpl; f_equal; rewritess; burn]).

 Case "TVar".
  repeat (simpl; split_match; 
          repeat norm_nat_compare; 
          subst; f_equal; try omega; auto).

 Case "TForall".
  simpl.
  rewrite (IHt1 (S n) n').
  rewrite (liftTT_liftTT_11 0 n).
  burn.
Qed.


Lemma liftTT_substTT
 :  forall m n n' t1 t2
 ,  liftTT m n (substTT (n + n') t2 t1)
 =  substTT (m + n + n') (liftTT m n t2) (liftTT m n t1).
Proof.
 intros. gen n n'.
 induction m; intros; simpl.
  burn.

  rrwrite (S m = 1 + m).
  rewrite <- liftTT_plus.
  rewritess.
  rrwrite (m + n + n' = n + (m + n')) by omega.
  rewrite liftTT_substTT_1. 
  burn.
Qed.
Hint Rewrite <- liftTT_substTT : global.


(********************************************************************)
(* Lifting after substiution, 
   with the lifting at a higher index *)
Lemma liftTT_substTT'
 :  forall n n' t1 t2
 ,  liftTT 1 (n + n') (substTT n t2 t1)
 =  substTT n (liftTT 1 (n + n') t2) (liftTT 1 (1 + n + n') t1).
Proof.
 intros. gen n n' t2.
 induction t1; intros;
  try (solve [simpl; f_equal; rewritess; norm]).

 Case "TVar".
  repeat ( unfold liftTT; unfold substTT; fold liftTT; fold substTT
         ; try lift_cases
         ; try fbreak_nat_compare
         ; intros); f_equal; burn; omega.

 Case "TForall".
  simpl. rewrite (IHt1 (S n) n').
  simpl. rewrite (liftTT_liftTT_11 0 (n + n')). 
  burn.
Qed.


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
  try (solve [simpl in *; f_equal; inverts H; burn]).


 Case "TVar".
  repeat (simpl in *; norm1); try nope; try omega. 

 Case "TForall".
  snorm. repeat f_equal. 

   (* Goal 7 *)
   lets L: liftTT_liftTT 1 0 1 d t2.
    rrwrite (d + 0 = d) in L.
    rewrite L in HeqH0.
    clear L.

   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t0. 
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   snorm.   
   rewrite D in HeqH0.
   snorm. 

   (* Goal 5 *)
   lets L: liftTT_liftTT 1 0 1 d t2.
    rrwrite (d + 0 = d) in L.
    rewrite L in HeqH0. 
    clear L.
    snorm.
    
   symmetry in HeqH1. rip.

   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. 
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   snorm.

   lets Z: liftTT_liftTT 1 0 1 d t2.
   rrwrite (d = d + 0) in HeqH0.
   rewrite Z in HeqH0.
   norm. rrwrite (1 + d = S d).
   rewrite D in HeqH0.
    nope.

 Case "TApp".
  snorm; nope.
   repeat (espread; burn); burn.
   espread. nope.
   espread. nope.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.

 Case "TSum".
  snorm; nope.
   repeat (espread; burn); burn.
   espread. nope.
   espread. nope.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.

 Case "TCon1".
  snorm; nope.
   repeat (espread; burn).
   espread. nope.
   erewrite IHt1 in *; eauto. nope.

 Case "TCon2".
  snorm; nope.
   repeat (espread; burn); burn.
   espread. nope.
   espread. nope.
   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto. nope.
   erewrite IHt1_1 in *; eauto. nope.
Qed.


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
   spec IHt1 H2.
   repeat rewritess. nope.

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

