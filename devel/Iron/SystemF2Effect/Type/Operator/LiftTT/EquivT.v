
Require Export Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.SystemF2Effect.Type.Relation.KindT.


Lemma equivT_closed_liftTT_liftTT
 :  forall sp t1 t2 k d
 ,  EquivT nil sp t1 t2 k
 -> EquivT nil sp (liftTT 1 d t1) (liftTT 1 d t2) k.
Proof.
 intros. 
 have (ClosedT t1).
 have (ClosedT t2).
 rrwrite (liftTT 1 d t1 = t1).
 rrwrite (liftTT 1 d t2 = t2).
 auto.
Qed.
Hint Resolve equivT_closed_liftTT_liftTT.
