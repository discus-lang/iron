
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.


(* Subsumption for sum types *)
Inductive SubsT : ty -> ty -> Prop :=
 | SbEquiv
   :  forall t1 t2
   ,  EquivT t1 t2
   -> SubsT  t1 t2 

 | SbTrans
   :  forall t1 t2 t3
   ,  SubsT t1 t2 -> SubsT t2 t3
   -> SubsT t1 t3

 | SbBot
   :  forall t k
   ,  SubsT t (TBot k)

 | SbSumWeak
   :  forall t1 t2 t3
   ,  SubsT t1 t2
   -> SubsT (TSum t1 t3) t2

 | SbSumAbove
   :  forall t1 t2 t3
   ,  SubsT t1 t2 -> SubsT t1 t3
   -> SubsT t1 (TSum t2 t3)

 | SbSumEquiv 
   :  forall t1 t1' t2 t2'
   ,  EquivT t1 t1' -> EquivT t2 t2'
   -> SubsT  t1 t2  -> SubsT  t1' t2'.

Hint Constructors SubsT.


Lemma SubsT_sum
 : forall e1 e1' e2
 , SubsT e1 e1' -> SubsT (TSum e1 e2) (TSum e1' e2).
Proof.
 intros.
 eapply SbSumAbove. eauto.
 have (SubsT e2 e2).
 eapply SbSumWeak with (t3 := e1) in H0.
 have (EquivT (TSum e2 e1) (TSum e1 e2)).
 eapply SbSumEquiv; eauto.
Qed.
Hint Resolve SubsT_sum.
