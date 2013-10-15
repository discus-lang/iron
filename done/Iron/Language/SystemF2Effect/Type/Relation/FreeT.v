
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Type.Relation.WfT.
Require Import Coq.Bool.Bool.


(********************************************************************)
(* Type variable is free in type *)
Fixpoint freeT (n : nat) (tt: ty)  {struct tt} := 
 match tt with
 | TVar ix        => n = ix
 | TForall k t    => freeT (S n) t
 | TApp t1 t2     => freeT n t1 \/ freeT n t2
 | TSum t1 t2     => freeT n t1 \/ freeT n t2
 | TBot k         => False

 | TCon0 tc       => False
 | TCon1 tc t1    => freeT n t1
 | TCon2 tc t1 t2 => freeT n t1 \/ freeT n t2
 | TCap _         => False
 end.


(********************************************************************)
Lemma freeT_wfT
 :  forall n1 n2 t
 ,  n2 >= n1
 -> WfT n1 t
 -> ~freeT n2 t.
Proof.
 intros. gen n1 n2.
 induction t; intros; inverts H0;
  unfold not; intros; snorm; subst; try omega.

 - cut (~ freeT (S n2) t); firstorder.

 - inverts H0.
   cut (~ freeT n2 t1); firstorder.
   cut (~ freeT n2 t2); firstorder.
 
 - inverts H0.
   cut (~ freeT n2 t1); firstorder.
   cut (~ freeT n2 t2); firstorder.

 - cut (~ freeT n2 t0); firstorder.

 - inverts H0.
   cut (~ freeT n2 t2); firstorder.
   cut (~ freeT n2 t3); firstorder.
Qed.
Hint Resolve freeT_wfT.


Lemma freeT_closedT
 :  forall t n
 ,  ClosedT t
 -> ~freeT n t.
Proof.
 intros. 
 eapply freeT_wfT; eauto.
Qed.


Lemma freeT_wfT_drop
 :  forall n t
 ,  WfT (S n) t
 -> ~freeT n t
 -> WfT  n    t.
Proof.
 intros. gen n.
 induction t; snorm; inverts H; firstorder.
Qed.


Lemma freeT_isEffectOnVar
 :  forall d t
 ,  ~(freeT d t)
 -> isEffectOnVar_b d t = false.
Proof.
 intros. 
 destruct t; snorm.
 destruct t0; snorm;
  try (solve [rewrite andb_false_iff; tauto]).

 - rewrite andb_false_iff. right. 
   rewrite beq_nat_false_iff. auto.
Qed.
Hint Resolve freeT_isEffectOnVar.

