
Require Export Iron.SystemF2Effect.Type.Operator.SubstTT.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.


Lemma substTT_EquivT
 :  forall t1 t2 t3
 ,  EquivT t1 t2
 -> EquivT (substTT 0 t3 t1) (substTT 0 t3 t2).
Proof.
 intros.
 induction H; snorm.

 Case "EqTrans".
  eapply EqTrans; eauto.
Qed.
