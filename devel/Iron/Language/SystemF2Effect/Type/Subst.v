
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Type.Lift.
Require Import Iron.Language.SystemF2Effect.Type.Lower.


(********************************************************************)
(* Substitution of Types in Types. *)
Fixpoint substTT (d: nat) (u: ty) (tt: ty) : ty 
 := match tt with
    | TCon _      => tt
    | TCap _      => tt
 
    | TVar ix
    => match nat_compare ix d with
       | Eq => u
       | Gt => TVar (ix - 1)
       | _  => TVar  ix
       end

    |  TForall k t => TForall k (substTT (S d) (liftTT 1 0 u) t)
    |  TApp t1 t2  => TApp      (substTT d u t1) (substTT d u t2)
    |  TSum t1 t2  => TSum      (substTT d u t1) (substTT d u t2)
    |  TBot k      => TBot k
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
  simpl in *.
  remember (nat_compare n d) as X.
  destruct X; burn.

  symmetry in HeqX. apply nat_compare_lt in HeqX. inverts H.
  lift_cases;
   repeat (norm; lift_cases; burn; try omega).

  symmetry in HeqX. apply nat_compare_gt in HeqX. inverts H.
  lift_cases;
   repeat (norm; lift_cases; burn; try omega).


 Case "TForall".
  simpl.
  simpl in H.
  remember (lowerTT (S d) t1) as X.
  destruct X.
   inverts H.
   symmetry in HeqX.

  remember (lowerTT (S d) (substTT (S (S (d + d'))) (liftTT 1 0 (liftTT 1 d t2)) t1)) as X. 
  destruct X.

   (* Goal 5 *)
   norm. symmetry in HeqX0.
   lets L: liftTT_liftTT 1 0 1 d t2. 
   rrwrite (d + 0 = d) in L.
   rewrite L in HeqX0. clear L.
   norm.
   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. rip. clear IHt1.
   norm.

   (* Goal 4 *)
   norm. symmetry in HeqX0.
   lets L: liftTT_liftTT 1 0 1 d t2.
   rrwrite (d + 0 = d) in L.
   rewrite L in HeqX0. clear L.
   norm.
   lets D: IHt1 (S d) d' (liftTT 1 0 t2) t. rip. clear IHt1.
   norm.

   (* Goal 3 *)
   nope.


 Case "TApp".
  simpl. norm.
  remember (lowerTT d (substTT (S (d + d')) (liftTT 1 d t2) t1_1)) as X1. destruct X1.
   remember (lowerTT d (substTT (S (d + d')) (liftTT 1 d t2) t1_2)) as X2. destruct X2.
    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
     inverts H.
     erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
     erewrite IHt1_2 in HeqX2; eauto. inverts HeqX2.
     simpl. eauto.
     nope.
     nope.

    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
    inverts H. simpl.
    erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
    erewrite IHt1_2 in HeqX2; eauto. inverts HeqX2.
    nope.
    nope.

    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
    inverts H. simpl.
    erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
    nope.
    nope.


 Case "TSum".
  simpl. norm.
  remember (lowerTT d (substTT (S (d + d')) (liftTT 1 d t2) t1_1)) as X1. destruct X1.
   remember (lowerTT d (substTT (S (d + d')) (liftTT 1 d t2) t1_2)) as X2. destruct X2.
    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
     inverts H.
     erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
     erewrite IHt1_2 in HeqX2; eauto. inverts HeqX2.
     simpl. eauto.
     nope.
     nope.

    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
    inverts H. simpl.
    erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
    erewrite IHt1_2 in HeqX2; eauto. inverts HeqX2.
    nope.
    nope.

    remember (lowerTT d t1_1) as B1. destruct B1.
    remember (lowerTT d t1_2) as B2. destruct B2.
    inverts H. simpl.
    erewrite IHt1_1 in HeqX1; eauto. inverts HeqX1.
    nope.
    nope.
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

 Case "TCon".
  congruence.

 Case "TCap".
  congruence.

 Case "TVar".
  fbreak_nat_compare; try congruence; burn.

 Case "TForall".
  remember (lowerTT (S ix) t1) as X.
  destruct X; nope.
   symmetry in HeqX.
   spec IHt1 HeqX.
   erewrite IHt1. congruence.

 Case "TApp".
  remember (lowerTT ix t1_1) as X.
  destruct X; nope. symmetry in HeqX.
   remember (lowerTT ix t1_2) as X.
   destruct X; nope. symmetry in HeqX0.
    spec IHt1_1 HeqX.
    spec IHt1_2 HeqX0.
    repeat rewritess. congruence.

 Case "TSum".
  remember (lowerTT ix t1_1) as X.
  destruct X; nope. symmetry in HeqX.
   remember (lowerTT ix t1_2) as X.
   destruct X; nope. symmetry in HeqX0.
    spec IHt1_1 HeqX.
    spec IHt1_2 HeqX0.
    repeat rewritess. congruence.

 Case "TBot".
  congruence.
Qed.
Hint Resolve lowerTT_substTT.
Hint Rewrite lowerTT_substTT : global.

