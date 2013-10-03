
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.SubstTT.Base.


(* If we lift at depth d, this creates an empty space and
   substituting into it doens't do anything. *)
Lemma substTT_liftTT
 :  forall d t1 t2
 ,  substTT d t2 (liftTT 1 d t1) = t1.
Proof.
 intros. gen d t2.
 induction t1; intros;
  first [ solve [snorm; try omega; nope]
        | solve [simpl; f_equal; norm]].
Qed.
Hint Rewrite substTT_liftTT : global.


(* Lifting after substitution,
   with the lifting at a lower index. *)
Lemma liftTT_substTT_1
 :  forall n n' t1 t2
 ,  liftTT 1 n (substTT (n + n') t2 t1)
 =  substTT (1 + n + n') (liftTT 1 n t2) (liftTT 1 n t1).
Proof.
 intros. gen n n' t2.
 induction t1; intros;
  try (solve [snorm; repeat f_equal; burn]).

 - Case "TVar".
   snorm; try omega.
   f_equal. omega.
   f_equal. omega. 

 - Case "TForall".
   snorm.
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
 - burn.

 - rrwrite (S m = 1 + m).
   rewrite liftTT_plus.
   rewritess.
   rrwrite (m + n + n' = n + (m + n')) by omega.
   rewrite liftTT_substTT_1. 
   burn.
Qed.
Hint Rewrite <- liftTT_substTT : global.


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

 - Case "TVar".
   repeat ( unfold liftTT; unfold substTT; fold liftTT; fold substTT
          ; try lift_cases
          ; try fbreak_nat_compare
          ; intros); try omega; burn.
   f_equal. omega.

 - Case "TForall".
   simpl. rewrite (IHt1 (S n) n').
   simpl. rewrite (liftTT_liftTT_11 0 (n + n')). 
   burn.
Qed.

