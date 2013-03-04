
Require Import Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.SystemF2Effect.Type.Operator.SubstTT.
Require Import Iron.SystemF2Effect.Type.Operator.MaskOnCapT.
Require Import Iron.SystemF2Effect.Type.Relation.SubsTs.
Require Import Iron.SystemF2Effect.Type.KiJudge.
Require Import Iron.SystemF2Effect.Type.Exp.


Fixpoint maskOnCapTs (p : nat -> bool) (tt : list ty) : list ty
 := match tt with
    | nil            => nil

    | TCon1 tc t1   :: ts 
    => match t1 with
       | TCap (TyCapRegion n)
       => if p n
             then ts
             else TCon1 tc (maskOnCapT p t1) :: maskOnCapTs p ts
       | _ =>     TCon1 tc (maskOnCapT p t1) :: maskOnCapTs p ts 
       end

    | t :: ts
    => maskOnCapT p t :: maskOnCapTs p ts
    end.


Lemma subsTs_maskOnCapTs 
 :  forall ke sp ts1 ts2 k p
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsTs ke sp ts1 (maskOnCapTs p ts2) k.
Proof.
 admit.
Qed.


Lemma bunchT_flattenT
 :  forall k t
 ,  bunchT k (flattenT t) = t.
Proof.
 admit.
Qed.
Hint Resolve bunchT_flattenT.


Lemma flattenT_maskOnCapT
 :  forall p t
 ,  flattenT (maskOnCapT p t) = maskOnCapTs p (flattenT t).
Proof.
 admit.
Qed.
Hint Resolve flattenT_maskOnCapT.


Lemma subsT_maskOnCapT
 :  forall ke sp p e1 e2
 ,  SubsT  ke sp e1 e2 KEffect
 -> SubsT  ke sp e1 (maskOnCapT p e2) KEffect.
Proof.
 intros.
 have HE1: (e1 = bunchT KEffect (flattenT e1)). 
 rewrite HE1.

 rrwrite (maskOnCapT p e2 = bunchT KEffect (flattenT (maskOnCapT p e2))).
 eapply subsTs_subsT.

 rrwrite (flattenT (maskOnCapT p e2) = maskOnCapTs p (flattenT e2)).
 eapply subsTs_maskOnCapTs.

 eapply subsT_subsTs in H; auto.
Qed.

