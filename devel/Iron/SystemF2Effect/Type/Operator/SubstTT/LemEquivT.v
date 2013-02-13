
Require Export Iron.SystemF2Effect.Type.Operator.SubstTT.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.


Lemma substTT_EquivT
 :  forall k t1 t2 t3
 ,  EquivT k t1 t2
 -> EquivT k (substTT 0 t3 t1) (substTT 0 t3 t2).
Proof.
 intros.
 induction H; snorm.

 Case "EqTrans".
  eapply EqTrans; eauto.
Qed.
