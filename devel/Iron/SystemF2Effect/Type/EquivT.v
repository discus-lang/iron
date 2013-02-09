
Require Export Iron.SystemF2Effect.Type.Exp.Base.


(* Equivalence for sum types *)
Inductive EquivT : ty -> ty -> Prop :=
 | EqVar
   : forall 


Hint Constructors EquivT.


Lemma Equiv_sum_left
 : forall t1 t1' t2
 ,  EquivT t1 t1'
 -> EquivT (TSum t1 t2) (TSum t1' t2).
Proof.
 intros.
 apply EqSumComm.
 auto.

Lemma Equiv_assoc
 :  forall t1 t2 t3
 ,  EquivT (TSum t1 (TSum t2 t3)) 
           (TSum (TSum t1 t2) t3).
Proof.
 intros.
 eapply EqSumSym.
 eauto.

 induction t1.
  auto.
  inverts H0.
 
 auto.
 auto.


(*
 | EqTrans
   :  forall t1 t2 t3
   ,  EquivT t1 t2
   -> EquivT t2 t3
   -> EquivT t1 t3

 | EqSym 
   :  forall t1 t2
   ,  EquivT t1 t2
   -> EquivT t2 t1

 | EqSumIdemp
   : forall t1
   , EquivT t1 (TSum t1 t1)

 | EqSumComm
   : forall t1 t2
   , EquivT (TSum t1 t2) (TSum t2 t1)

 | EqSumAssoc
   : forall t1 t2 t3
   , EquivT (TSum t1 (TSum t2 t3))
            (TSum (TSum t1 t2) t3)

 | EqSumBot
   : forall t1 k
   , EquivT t1 (TSum t1 (TBot k)).
*)