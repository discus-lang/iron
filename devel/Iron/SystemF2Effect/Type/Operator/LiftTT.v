
Require Export Iron.SystemF2Effect.Type.Predicate.Wf.
Require Export Iron.SystemF2Effect.Type.Exp.


(*******************************************************************)
(* Lift type indices that are at least a certain depth. *)
Fixpoint liftTT (n: nat) (d: nat) (tt: ty) : ty :=
 match tt with
 |  TVar ix
 => if le_gt_dec d ix
     then TVar (ix + n)
     else tt

 |  TForall k t    => TForall k (liftTT n (S d) t)
 |  TApp t1 t2     => TApp      (liftTT n d t1) (liftTT n d t2)
 |  TSum t1 t2     => TSum      (liftTT n d t1) (liftTT n d t2)
 |  TBot k         => TBot  k

 |  TCon0 tc       => TCon0 tc
 |  TCon1 tc t1    => TCon1 tc  (liftTT n d t1)
 |  TCon2 tc t1 t2 => TCon2 tc  (liftTT n d t1) (liftTT n d t2)
 |  TCap  _        => tt
 end.
Hint Unfold liftTT.


Ltac burn_liftTT t := 
  induction t;
  first [ solve [snorm; f_equal; try omega]
        | solve [repeat (snorm; f_equal; eauto; rewritess; nope) ]].


(********************************************************************)
(* Helper Lemmas *)
Lemma liftTT_TVar_exists
 : forall n d n1
 , exists n2, liftTT n d (TVar n1) = liftTT n d (TVar n2).
Proof.
 intros.
 unfold liftTT. snorm. 
  exists n1. snorm. omega.
  exists n1. snorm. omega.
Qed.


Lemma liftTT_TVar_not_zero
 : forall t
 , liftTT 1 0 t <> TVar 0.
Proof.
 intros.
 destruct t;
  try (solve [unfold not; snorm; inverts H; omega]);
  try (solve [unfold not; snorm; nope]).
Qed.
Hint Resolve liftTT_TVar_not_zero.


Lemma liftTT_TVar_not_succ
 : forall t d
 ,             t <> TVar d
 -> liftTT 1 0 t <> TVar (S d).
Proof.
 intros. gen d.
 destruct t; intros;
   try (solve [simpl; congruence]).

 Case "TVar".
  unfold liftTT. 
  snorm.
  congruence.
Qed.
Hint Resolve liftTT_TVar_not_succ.


Lemma liftTT_TCap
 :  forall n d t tc
 ,  liftTT n d t = TCap tc
 -> t            = TCap tc.
Proof.
 intros.
 destruct t; simpl in *; nope.
  split_if; nope.
Qed.


(********************************************************************)
(* Lifting and well-formedness *)
Lemma liftTT_wfT
 :  forall kn t d
 ,  wfT kn t
 -> wfT (S kn) (liftTT 1 d t).
Proof.
 intros. gen kn d.
 induction t; intros; inverts H; snorm.

 Case "TVar".
  eapply WfT_TVar. omega.
Qed.
Hint Resolve liftTT_wfT.


(********************************************************************)
Lemma liftTT_zero
 :  forall d t
 ,  liftTT 0 d t = t.
Proof.
 intros. gen d. burn_liftTT t.
Qed.
Hint Resolve liftTT_zero.
Hint Rewrite liftTT_zero : global.


Lemma liftTT_comm
 :  forall n m d t
 ,  liftTT n d (liftTT m d t)
 =  liftTT m d (liftTT n d t).
Proof.
 intros. gen d. burn_liftTT t.
Qed.
Hint Resolve liftTT_comm.


Lemma liftTT_succ
 :  forall n m d t
 ,  liftTT (S n) d (liftTT m     d t)
 =  liftTT n     d (liftTT (S m) d t).
Proof.
 intros. gen d m n. burn_liftTT t.
Qed.
Hint Resolve liftTT_succ.
Hint Rewrite liftTT_succ : global. 


Lemma liftTT_plus
 : forall n m d t
 , liftTT (n + m) d t = liftTT n d (liftTT m d t).
Proof.
 intros. gen n d.
 induction m; intros.
 rewrite liftTT_zero; burn.
 rrwrite (n + S m = S n + m).
 rewrite IHm.
 rewrite liftTT_succ.
 auto.
Qed. 
Hint Resolve liftTT_plus.
Hint Rewrite liftTT_plus : global.


(******************************************************************************)
Lemma liftTT_wfT_1
 :  forall t n ix
 ,  wfT n t
 -> liftTT 1 (n + ix) t = t.
Proof.
 intros. gen n ix.
 induction t; intros; inverts H;
  try 
  first 
  [ solve [snorm; omega]
  | solve [repeat (snorm; rewritess; f_equal)]].

  Case "TForall".
   repeat (snorm; try rewritess; f_equal).
   rrwrite (S (n + ix) = S n + ix). 
   eauto.
Qed.
Hint Resolve liftTT_wfT_1.


Lemma liftTT_closedT_id_1
 :  forall t d
 ,  closedT t
 -> liftTT 1 d t = t.
Proof.
 intros.
 rrwrite (d = d + 0). eauto.
Qed.
Hint Resolve liftTT_closedT_id_1.


Lemma liftTT_closedT_10
 :  forall t
 ,  closedT t
 -> closedT (liftTT 1 0 t).
Proof.
 intros. red.
 rrwrite (0 = 0 + 0).
 rewrite liftTT_wfT_1; auto.
Qed.
Hint Resolve liftTT_closedT_10.


(********************************************************************)
(* Changing the order of lifting.
   We build this up in stages. 
   Start out by only allow lifting by a single place for both
   applications. Then allow lifting by multiple places in the first
   application, then multiple places in both. 
*)
Lemma liftTT_liftTT_11
 :  forall d d' t
 ,  liftTT 1 (1 + (d + d')) (liftTT 1 d t)
 =  liftTT 1 d              (liftTT 1 (d + d') t).
Proof.
 intros. gen d d'.
 induction t; intros;
  try (solve [ snorm; omega ]);
  try (solve [ snorm; f_equal; rewritess; auto ]).

 Case "TForall". 
  snorm.
  rrwrite (S (d + d') = (S d) + d').
  f_equal; rewritess; auto.
Qed.


Lemma liftTT_liftTT_1
 :  forall n1 m1 n2 t
 ,  liftTT m1   n1 (liftTT 1 (n2 + n1) t)
 =  liftTT 1 (m1 + n2 + n1) (liftTT m1 n1 t).
Proof.
 intros. gen n1 m1 n2 t.
 induction m1; intros; simpl.
  burn. 

  rrwrite (S m1 = 1 + m1).
  rewrite liftTT_plus.
  rewritess.
  rrwrite (m1 + n2 + n1 = n1 + (m1 + n2)) by omega.
  rewrite <- liftTT_liftTT_11.
  burn.
Qed.


Lemma liftTT_liftTT
 :  forall m1 n1 m2 n2 t
 ,  liftTT m2 (m1 + n2 + n1) (liftTT m1 n1 t)
 =  liftTT m1 n1 (liftTT m2 (n2 + n1) t).
Proof.
 intros. gen n1 m1 n2 t.
 induction m2; intros.
  burn.
  rrwrite (S m2 = 1 + m2).
  rewrite liftTT_plus.
  rewrite IHm2.
  rewrite <- liftTT_liftTT_1.
  burn.
Qed.
Hint Rewrite liftTT_liftTT : global.


(********************************************************************)
Lemma liftTT_liftTT_Sd
 : forall n d t
 , liftTT n (S d) (liftTT 1 0 t)
 = liftTT 1 0     (liftTT n d t).
Proof.
 intros.
 lets D: liftTT_liftTT 1 0 n d t.
 simpl in D.
 rrwrite (d + 0 = d) in D.
 auto.
Qed.
Hint Rewrite liftTT_liftTT_Sd : global.


(********************************************************************)
Lemma liftTT_map_liftTT
 :  forall m1 n1 m2 n2 ts
 ,  map (liftTT m1 n1) (map (liftTT m2 (n2 + n1)) ts)
 =  map (liftTT m2 (m1 + n2 + n1)) (map (liftTT m1 n1) ts).
Proof.
 induction ts; simpl; f_equal; norm; auto.
Qed.  

