
Require Export Iron.SystemF2Effect.Type.Exp.
Require Export Iron.SystemF2Effect.Type.Relation.WfT.
Require Import Coq.Bool.Bool.


(* Type variable is free in type *)
Fixpoint freeTT (n : nat) (tt: ty) : bool
 := match tt with
    | TVar ix        => beq_nat n ix
    | TForall k t    => freeTT (S n) t
    | TApp t1 t2     => orb (freeTT n t1) (freeTT n t2)
    | TSum t1 t2     => orb (freeTT n t1) (freeTT n t2)
    | TBot k         => false

    | TCon0 tc       => false
    | TCon1 tc t1    => freeTT n t1
    | TCon2 tc t1 t2 => orb (freeTT n t1) (freeTT n t2)
    | TCap _         => false
  end.


Lemma freeT_wfT_1
 :  forall n t
 ,  WfT    n t
 -> freeTT (S n) t = false.
Proof.
 intros. gen n.
 induction t; 
  try (solve [snorm; inverts H; try (erewrite IHt1); snorm; eauto 2]).

 - Case "TVar".
   snorm. inverts H. 
   destruct n; auto.
    eapply beq_nat_false_iff. 
    omega.
Qed.


Lemma freeT_wfT
 :  forall n1 n2 t
 ,  n2 > n1
 -> WfT    n1 t
 -> freeTT n2 t = false.
Proof.
 intros.
 destruct n2.
 - omega.
 - eapply freeT_wfT_1.
   destruct n1; eauto.
   + have (n2 >= n1) by omega.
     inverts H; eauto.
Qed.
Hint Resolve freeT_wfT.


Lemma freeTT_wfT_drop
 :  forall n t
 ,  WfT (S n) t
 -> freeTT n t = false
 -> WfT  n    t.
Proof.
 intros. gen n.
 induction t;
  try (solve [snorm; inverts H; eauto]).
Qed.


(********************************************************************)
Lemma isEffectOnVar_freeTT_false
 :  forall d t
 ,  freeTT d t = false
 -> isEffectOnVar d t = false.
Proof.
 intros. 
 destruct t; snorm.
  destruct t0; snorm; 
   try rewrite andb_false_iff; rip.
  right.
  rewrite beq_nat_false_iff. auto.
Qed.
Hint Resolve isEffectOnVar_freeTT_false.

