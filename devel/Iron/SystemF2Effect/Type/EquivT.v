
Require Export Iron.SystemF2Effect.Type.Exp.Base.


(* Type equivalence.
   The interesting cases all concern sums. *)
Inductive EquivT : ty -> ty -> Prop :=
 | EqRefl
   :  forall t
   ,  EquivT t t

 | EqSym
   :  forall t1 t2
   ,  EquivT t1 t2 -> EquivT t2 t1

 | EqTrans
   :  forall t1 t2 t3
   ,  EquivT t1 t2 -> EquivT t2 t3
   -> EquivT t1 t3

 | EqSumBot
   : forall t k
   , EquivT t             (TSum t (TBot k))

 | EqSumIdemp
   : forall t
   , EquivT t             (TSum t t)

 | EqSumComm
   : forall t1 t2
   , EquivT (TSum t1 t2)  (TSum t2 t1)

 | EqSumAssoc
   : forall t1 t2 t3
   , EquivT (TSum t1 (TSum t2 t3))
            (TSum (TSum t1 t2) t3).

Hint Constructors EquivT.


Lemma equivT_TSumBot_left
 :  forall t k
 ,  EquivT t (TSum (TBot k) t).
Proof.
 intros.
 eapply EqTrans.
  eapply EqSumBot.
  eauto.
Qed.
Hint Resolve equivT_TSumBot_left.
