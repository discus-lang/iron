
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.SystemF2Effect.Type.Operator.


Definition isVisibleE (sp : stprops) (t : ty) : bool
 := match t with 
    | TCon1 tc (TCap (TyCapRegion n)) 
    => andb (isEffectTyCon tc) (hasSRegion n sp)

    | otherwise
    => false
    end.


Definition SubsVisibleT ke sp e e'
 := SubsT ke
          sp 
          e 
          (maskOnT (fun t => negb (isVisibleE sp t)) e') 
          KEffect.


Lemma subsT_visible_refl
 :  forall ke sp e
 ,  KindT ke sp e KEffect
 -> SubsVisibleT ke sp e e.
Proof.
 intros.
 unfold SubsVisibleT.
  admit. (* ok, effect subsumes masked one *)
Qed.


Lemma subsT_visible_equiv
 :  forall       ke sp e1 e2
 ,  SubsT        ke sp e1 e2 KEffect
 -> SubsVisibleT ke sp e1 e2.
Proof.
 intros.
 unfold SubsVisibleT.
  admit. (* ok, effect subsumes masked one *)
Qed.


Lemma subsT_phase_change
 :  forall ke sp n r e1 e2
 ,  hasSRegion n sp = false
 -> r               = TCap (TyCapRegion n)
 -> SubsT         (ke :> KRegion) sp e1               e2               KEffect
 -> SubsVisibleT   ke              sp (substTT 0 r e1) (substTT 0 r e2).
Proof.
 admit.
Qed.
