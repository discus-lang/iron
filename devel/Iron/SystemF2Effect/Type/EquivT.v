
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.KiJudge.


(* Type equivalence.
   The interesting cases all concern sums. *)
Inductive EquivT : ki -> ty -> ty -> Prop :=
 | EqRefl
   :  forall k t
   ,  EquivT k t t

 | EqSym
   :  forall k t1 t2
   ,  EquivT k t1 t2 -> EquivT k t2 t1

 | EqTrans
   :  forall k t1 t2 t3
   ,  EquivT k t1 t2 -> EquivT k t2 t3
   -> EquivT k t1 t3

 | EqSumBot
   : forall k t
   , EquivT k t             (TSum t (TBot k))

 | EqSumIdemp
   : forall k t
   , EquivT k t             (TSum t t)

 | EqSumComm
   : forall k t1 t2
   , EquivT k (TSum t1 t2)  (TSum t2 t1)

 | EqSumAssoc
   : forall k t1 t2 t3
   , EquivT k (TSum t1 (TSum t2 t3))
              (TSum (TSum t1 t2) t3).

Hint Constructors EquivT.


Lemma equivT_sum_left
 :  forall t k
 ,  EquivT k t (TSum (TBot k) t).
Proof.
 intros.
 eapply EqTrans.
  eapply EqSumBot.
  eauto.
Qed.
Hint Resolve equivT_sum_left.


Lemma equivT_kind
 :  forall ke sp t1 t2 k
 ,  EquivT k t1 t2
 -> KIND   ke sp t1 k
 -> KIND   ke sp t2 k.
Proof.
 admit.      (* Broken, will need to add KIND judge to EqRefl *)
Qed. 

