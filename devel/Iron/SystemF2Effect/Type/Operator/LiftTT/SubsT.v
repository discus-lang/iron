
Require Export Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.


Lemma subsT_closed_liftT_liftT
 :  forall sp t1 t2 k d
 ,  SubsT nil sp t1 t2 k
 -> SubsT nil sp (liftTT 1 d t1) (liftTT 1 d t2) k.
Proof.
 intros.
 have (ClosedT t1).
 have (ClosedT t2).
 rrwrite (liftTT 1 d t1 = t1).
 rrwrite (liftTT 1 d t2 = t2).
 auto.
Qed.
Hint Resolve subsT_closed_liftT_liftT. 
