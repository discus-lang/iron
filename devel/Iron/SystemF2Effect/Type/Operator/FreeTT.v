
Require Export Iron.SystemF2Effect.Type.Exp.
Require Export Iron.SystemF2Effect.Type.Relation.WfT.
Require Import Coq.Bool.Bool.


(********************************************************************)
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
 induction t; rip.
 - Case "TVar".
   simpl. inverts H. 
    destruct n. auto.
    eapply beq_nat_false_iff. omega.

 - Case "TForall".
   simpl. eapply IHt.
   inverts H. auto.

 - Case "TApp".
   simpl. inverts H.
   erewrite IHt1. snorm. auto.

 - Case "TSum".
   simpl. inverts H.
   erewrite IHt1. snorm. auto.

 - Case "TCon1".
   simpl. inverts H.
   erewrite IHt; auto.

 - Case "TCon2".
   simpl. inverts H.
   erewrite IHt1. snorm. auto.
Qed.


Lemma freeT_wfT
 :  forall n1 n2 t
 ,  n2 > n1
 -> WfT    n1 t
 -> freeTT n2 t = false.
Proof.
 intros.
  destruct n2.
   omega.
   eapply freeT_wfT_1.
   destruct n1.
    eauto.
    inverts H. auto.
    have (n2 >= n1) by omega.
    eauto.
Qed.
Hint Resolve freeT_wfT.


Lemma freeTT_wfT_drop
 :  forall n t
 ,  WfT (S n) t
 -> freeTT n t = false
 -> WfT  n    t.
Proof.
 intros. gen n.
 induction t.
 - Case "TVar".
   snorm. inverts H.
   eapply WfT_TVar. omega.

 - Case "TForall".
   snorm. inverts H.
   eapply WfT_TForall. eauto.

 - Case "TApp".
   snorm.
   apply orb_false_iff in H0. rip.
   inverts H. eauto.

 - Case "TSum".
   snorm.
   apply orb_false_iff in H0. rip.
   inverts H. eauto.

 - Case "TBot".
   eauto.

 - Case "TCon0".
   eauto.

 - Case "TCon1".
   intros.
   inverts H. snorm.

 - Case "TCon2".
   snorm.
   apply orb_false_iff in H0. rip.
   inverts H. eauto.

 - Case "TCap".
   auto.
Qed.

