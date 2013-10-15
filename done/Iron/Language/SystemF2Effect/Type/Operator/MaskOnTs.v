
Require Import Iron.Language.SystemF2Effect.Type.Exp.
Require Import Iron.Language.SystemF2Effect.Type.Relation.KindT.
Require Import Iron.Language.SystemF2Effect.Type.Relation.SubsTs.
Require Import Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.Language.SystemF2Effect.Type.Operator.SubstTT.
Require Import Iron.Language.SystemF2Effect.Type.Operator.MaskOnT.
Require Import Iron.Language.SystemF2Effect.Type.Operator.BunchT. 
Require Import Iron.Language.SystemF2Effect.Type.Operator.FlattenT.


(********************************************************************)
(* Like maskOnT, but work with a list of types instead of a 
   bunched type with TSum constructors. *)
Fixpoint maskOnTs (p : ty -> bool) (tt : list ty) : list ty
 := match tt with
    | nil            => nil

    | TCon1 tc t1   :: ts 
    => if p (TCon1 tc t1) then                maskOnTs p ts
                          else TCon1 tc t1 :: maskOnTs p ts

    |  t :: ts
    => t :: maskOnTs p ts
    end.


(********************************************************************)
Lemma maskOnTs_cases 
 :  forall   p t ts ts'
 ,  maskOnTs p (t :: ts) = ts'
 -> (ts' =      maskOnTs p ts)
 \/ (ts' = t :: maskOnTs p ts).
Proof.
 intros.
 simpl in H.
 destruct t; try auto.
  split_if; auto.
Qed.


(* Structural lemmas. *)
Lemma maskOnTs_app
 :  forall p ts1 ts2
 ,  maskOnTs p ts1 ++ maskOnTs p ts2
 =  maskOnTs p (ts1 ++ ts2).
Proof.
 induction ts1; intros.
 - snorm.
 - rrwrite (ts2 >< (ts1 :> a) = (ts2 >< ts1) :> a).
   destruct a;
    try (solve [simpl; rewritess; auto]).
   + simpl. 
     split_if.
     * auto.
     * simpl. rewritess. auto.
Qed.
Hint Resolve maskOnTs_app.


Lemma maskOnTs_flattenT
 :  forall p t
 ,  flattenT (maskOnT p t) = maskOnTs p (flattenT t).
Proof.
 intros.
 induction t; snorm.
 - repeat rewritess.
   apply maskOnTs_app.
 - unfold maskOnT.
   split_if.  
   + snorm.
   + nope.
 - unfold maskOnT.
   split_if.
   + nope.
   + snorm.
Qed.
Hint Resolve maskOnTs_flattenT.


(* Kind preservation. *)
Lemma maskOnTs_kind
 :  forall ke sp ts k p
 ,  KindTs ke sp ts k
 -> KindTs ke sp (maskOnTs p ts) k.
Proof.
 intros.
 induction ts.
 - simpl. auto.
 - apply kindTs_snoc in H. rip.
   remember (maskOnTs p (ts :> a)) as ts2.
    symmetry in Heqts2.
    apply maskOnTs_cases in Heqts2.
    inverts Heqts2; auto.
Qed.
Hint Resolve maskOnTs_kind.   


(* Equivalence *)
Lemma maskOnTs_maskOnT_equivTs
 :  forall ke sp p t k
 ,  SumKind k
 -> KindT   ke sp t k
 -> EquivTs ke sp (flattenT (maskOnT p t)) (maskOnTs p (flattenT t)) k.
Proof.
 intros. gen k.
 induction t; intros;
   try (solve [simpl; eapply equivTs_refl; auto]).

 - Case "TSum".
   inverts H0.
    spec IHt1 H6; auto.
    spec IHt2 H8; auto.
    simpl.
    rewrite <- maskOnTs_app.
    eauto.
 
 - Case "TCon1".
   simpl.
   split_if.
   + unfold maskOnT. 
     rewrite <- HeqH1.
     simpl. auto.
   + unfold maskOnT.
     rewrite <- HeqH1.
     simpl. auto.
Qed.     
Hint Resolve maskOnTs_maskOnT_equivTs.


(* Subsumption *)
Lemma maskOnTs_subsTs_below
 :  forall ke sp ts1 ts2 k p
 ,  SubsTs ke sp ts1 ts2 k
 -> SubsTs ke sp ts1 (maskOnTs p ts2) k.
Proof.
 intros.
 inverts H.
 eapply SbsSum; auto.
 - induction ts2. 
   + snorm.
   + eapply kindTs_snoc in H2. rip.
     apply Forall_split_cons in H3.
     remember (maskOnTs p (ts2 :> a)) as ts'.
      symmetry in Heqts'.
      apply maskOnTs_cases in Heqts'.
      rip. inverts Heqts'.
       auto. auto.
Qed.
Hint Resolve maskOnTs_subsTs_below.


Lemma maskOnT_subsT_below
 :  forall ke sp p e1 e2
 ,  SubsT  ke sp e1 e2             KEffect
 -> SubsT  ke sp e1 (maskOnT p e2) KEffect.
Proof.
 intros.

 have  HE1: (EquivT ke sp (bunchT KEffect (flattenT e1)) 
                          e1                                         KEffect).
 eapply subsT_equiv_above; eauto.
 clear HE1.

 have  HE2: (EquivT ke sp (maskOnT p e2) 
                          (bunchT KEffect (flattenT (maskOnT p e2))) KEffect)
  by (eapply EqSym; [eapply bunchT_kindT; eauto | eauto | eauto]).
 eapply subsT_equiv_below.
  eapply EqSym in HE2; eauto.
 clear HE2.

 eapply subsTs_subsT.

 rrwrite (flattenT (maskOnT p e2) = maskOnTs p (flattenT e2)).
 eapply maskOnTs_subsTs_below.

 eapply subsT_subsTs; eauto.
Qed.
Hint Resolve maskOnT_subsT_below.

