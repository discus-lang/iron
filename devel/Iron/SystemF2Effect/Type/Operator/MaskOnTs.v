
Require Import Iron.SystemF2Effect.Type.Exp.
Require Import Iron.SystemF2Effect.Type.KiJudge.
Require Import Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.SystemF2Effect.Type.Operator.SubstTT.
Require Import Iron.SystemF2Effect.Type.Operator.MaskOnT.
Require Import Iron.SystemF2Effect.Type.Relation.SubsTs.


Fixpoint maskOnTs (p : ty -> bool) (tt : list ty) : list ty
 := match tt with
    | nil            => nil

    | TCon1 tc t1   :: ts 
    => if p (TCon1 tc t1) then nil
                          else TCon1 tc t1 :: maskOnTs p ts

    | t :: ts
    => t :: maskOnTs p ts
    end.


Lemma subsTs_maskOnTs 
 :  forall ke sp ts1 ts2 k p
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsTs ke sp ts1 (maskOnTs p ts2) k.
Proof.
 admit.
Qed.


Lemma flattenT_maskOnTs
 :  forall p t
 ,  flattenT (maskOnT p t) = maskOnTs p (flattenT t).
Proof.
 admit.
Qed.
Hint Resolve flattenT_maskOnTs.


Lemma subsT_maskOnTs
 :  forall ke sp p e1 e2
 ,  SubsT  ke sp e1 e2 KEffect
 -> SubsT  ke sp e1 (maskOnT p e2) KEffect.
Proof.
 intros.
 have HE1: (EquivT ke sp (bunchT KEffect (flattenT e1)) e1 KEffect).
 eapply subsT_equiv_above. eauto.

 rrwrite (maskOnT p e2 = bunchT KEffect (flattenT (maskOnT p e2))) by admit.
 eapply subsTs_subsT.

 rrwrite (flattenT (maskOnT p e2) = maskOnTs p (flattenT e2)).
 eapply subsTs_maskOnTs.

 eapply subsT_subsTs in H; auto.
Qed.
