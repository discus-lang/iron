
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


(********************************************************************)
Lemma substTT_wfT
 :  forall d ix t t2
 ,  wfT d t
 -> substTT (d + ix) t2 t = t.
Proof.
 intros. gen d ix t2.
 induction t; rip; inverts H; simpl; f_equal; burn.
 Case "TVar".
  lift_cases; burn; omega.
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
 induction t1; intros; simpl; f_equal; burn.

 Case "TVar".
  lift_cases; unfold substTT;
   fbreak_nat_compare; f_equal; burn; omega.
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
 induction t1; intros; simpl; f_equal; try burn.

 Case "TVar".
  repeat (simpl; fbreak_nat_compare; try lift_cases; rip);
   f_equal; burn; omega.

 Case "TForall".
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
  try (solve [simpl; f_equal; burn]);
  burn.

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
  norm.
  split_match; burn;
   repeat (repeat norm_nat_compare; norm; lift_cases; burn; try omega).


 Case "TForall".
  norm.
  split_match; norm.

   (* Goal 7 *)
   lets L: liftTT_liftTT 1 0 1 d t2.
    rrwrite (d + 0 = d) in L.
    rewrite L in HeqH0.
    clear L.

   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t0. 
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   norm.   
   rewrite D in HeqH0.
   norm. auto.

   (* Goal 6 *)
   rewrite <- HeqH1 in H2. nope.

   (* Goal 5 *)
   lets L: liftTT_liftTT 1 0 1 d t2.
    rrwrite (d + 0 = d) in L.
    rewrite L in HeqH0. 
    clear L.
    norm.

   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. 
   symmetry in HeqH1. rip. clear IHt1. clear HeqH1.
   norm.
   rewrite D in HeqH0.
   nope.

 Case "TApp".
  norm.
  split_match; nope.

   erewrite IHt1_1 in *; eauto.
   erewrite IHt1_2 in *; eauto.
   repeat norm.

   erewrite IHt1_1 in HeqH0. inverts HeqH0.
   erewrite IHt1_2 in HeqH1. nope. 
   eauto. eauto.

   erewrite IHt1_1 in HeqH0.
   nope.
   eauto.

 Case "TSum".
  norm.
  split_match; nope.

    erewrite IHt1_1 in *; eauto.
    erewrite IHt1_2 in *; eauto.
    repeat norm.   
  
    erewrite IHt1_1 in HeqH0. inverts HeqH0.
    erewrite IHt1_2 in HeqH1. nope.
    eauto. eauto.

    erewrite IHt1_1 in HeqH0.
    nope. eauto.

 Case "TCon1".
  norm.
  split_match; nope.

    erewrite IHt1 in *; eauto. 
    repeat norm.

    erewrite IHt1 in HeqH0.
    nope. eauto.

 Case "TCon2".
  norm.
  split_match; nope.

    erewrite IHt1_1 in *; eauto.
    erewrite IHt1_2 in *; eauto.
    repeat norm.   
  
    erewrite IHt1_1 in HeqH0. inverts HeqH0.
    erewrite IHt1_2 in HeqH1. nope.
    eauto. eauto.

    erewrite IHt1_1 in HeqH0.
    nope. eauto.
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
  try (solve [simpl; f_equal; burn]); 
  burn.

 Case "TVar".
  repeat (simpl; fbreak_nat_compare); burn; omega.

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
 induction t1; intros; simpl in *; burn.

 Case "TVar".
  fbreak_nat_compare; try congruence; burn.

 Case "TForall".
  remember (lowerTT (S ix) t1) as X.
  destruct X; nope.
   symmetry in HeqX.
   spec IHt1 HeqX.
   erewrite IHt1. congruence.

 Case "TApp".
  split_match; try nope.
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess. congruence.

 Case "TSum".
  split_match; try nope.
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess. congruence.

 Case "TCon1".
  split_match; try nope.
   symmetry in HeqH0. spec IHt1 HeqH0.
   repeat rewritess. congruence.

 Case "TCon2".
  split_match; try nope.
   symmetry in HeqH0. spec IHt1_1 HeqH0.
   symmetry in HeqH1. spec IHt1_2 HeqH1.
   repeat rewritess. congruence.
Qed.
Hint Resolve lowerTT_substTT.
Hint Rewrite lowerTT_substTT : global.

