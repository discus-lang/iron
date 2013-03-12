
Require Export Iron.SystemF2Effect.Type.Exp.
Require Export Iron.SystemF2Effect.Type.Relation.WfT.


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
    | TCon1 tc t1    => false
    | TCon2 tc t1 t2 => false
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

