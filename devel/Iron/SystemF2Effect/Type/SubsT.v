
Require Export Iron.SystemF2Effect.Type.Exp.Base.


(* Subsumption for sum types *)
Inductive SubsT : ty -> ty -> Prop :=
 | SbRefl
   :  forall t1
   ,  SubsT t1 t1

 | SbTrans
   :  forall t1 t2 t3
   ,  SubsT t1 t2 -> SubsT t2 t3
   -> SubsT t1 t3

 | SbBot
   :  forall t k
   ,  SubsT t (TBot k)

 | SbSumBelow
   :  forall t1 t2 t3
   ,  SubsT t1 t2
   -> SubsT t1 t3
   -> SubsT t1 (TSum t2 t3)

 | SbSumAbove
   :  forall t1 t2 t3
   ,  SubsT t1 t2
   -> SubsT (TSum t1 t3) t2.

Hint Constructors SubsT.


Lemma SubsT_sum_flip
 :  forall t1 t2 t3
 ,  SubsT t1 (TSum t2 t3)
 -> SubsT t1 (TSum t3 t2).
Proof.
 intros. 
 eapply SbSumBelow.
 

Lemma SubsT_sum_left
 : forall t1 t1' t2
 , SubsT  t1 t1'
-> SubsT (TSum t1 t2) (TSum t1' t2).
Proof.
 intros.
 eapply SbSumAbove. 
 eapply SbSumBelow. auto.
eauto.
 have (SubsT e2 e2).
 eapply SbSumWeak with (t3 := e1) in H0.
 have (EquivT (TSum e2 e1) (TSum e1 e2)).
 eapply SbSumEquiv; eauto.
Qed.
Hint Resolve SubsT_sum.

(*
 | SbSumAbove
   :  forall t1 t2 t3 t4
   ,  SubsT t1 t2 -> SubsT t3 t4
   -> SubsT (TSum t1 t3) (TSum t2 t4)
*)